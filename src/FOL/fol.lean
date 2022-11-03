import lib.lib tactic data.set_like.basic logic translation

universe u

namespace fol
open_locale logic_symbol
structure language : Type (u+1) :=
(fn : ℕ → Type u)
(pr : ℕ → Type u)

class has_zero_symbol (L : language) := (zero : L.fn 0)

class has_succ_symbol (L : language) := (succ : L.fn 1)

class has_add_symbol (L : language) := (add : L.fn 2)

class has_mul_symbol (L : language) := (mul : L.fn 2)

class has_le_symbol (L : language) := (le : L.pr 2)

class has_mem_symbol (L : language) := (mem : L.pr 2)

variables (L : language.{u})

inductive subterm (m n : ℕ) : Type u
| metavar {} : fin m → subterm
| var     {} : fin n → subterm
| function   : ∀ {p}, L.fn p → (fin p → subterm) → subterm

@[reducible] def term (m) := subterm L m 0

variables {L}

namespace subterm
variables {m n : ℕ}

prefix `#`:max := subterm.var
prefix `&`:max := subterm.metavar

def term.const (f : L.fn 0) : subterm L m n := function f finitary.nil

instance [inhabited (fin m)] : inhabited (subterm L m n) := ⟨&default⟩

instance [has_zero_symbol L] : has_zero (subterm L m n) := ⟨function has_zero_symbol.zero finitary.nil⟩

instance [has_succ_symbol L] : has_succ (subterm L m n) := ⟨λ t, function has_succ_symbol.succ ‹t›⟩

instance [has_add_symbol L] : has_add (subterm L m n) := ⟨λ t u, function has_add_symbol.add ‹t, u›⟩

instance [has_mul_symbol L] : has_mul (subterm L m n) := ⟨λ t u, function has_mul_symbol.mul ‹t, u›⟩

postfix `˙`:max := numeral

/-
notation `##'` := idvar_inv _

@[simp] lemma idvar_inv_function (n : ℕ) (i : fin n) : (##' : finitary (term L) n) i = #(n - i - 1) := rfl

@[simp] lemma idvar_inv_nil : (##' : finitary (term L) 0) = finitary.nil := by ext

@[simp] lemma idvar_inv_eq_singleton : (##' : finitary (term L) 1) = ‹#0› := by ext; by simp

@[simp] lemma idvar_inv_eq_doubleton : (##' : finitary (term L) 2) = ‹#1, #0› := by ext; by simp

variables (L)


-/

variables (L) (m n)

end subterm

variables (L)
inductive subformula (m) : ℕ → Type u
| verum    {n} : subformula n
| relation {n} : ∀ {p}, L.pr p → (fin p → subterm L m n) → subformula n
| equal    {n} : subterm L m n  → subterm L m n → subformula n
| imply    {n} : subformula n → subformula n → subformula n
| neg      {n} : subformula n → subformula n
| fal      {n} : subformula (n + 1) → subformula n

attribute [pattern]  has_eq.eq has_negation.neg has_arrow.arrow has_univ_quantifier.univ has_exists_quantifier.ex

@[reducible] def formula (m) := subformula L m 0

@[reducible] def sentence := formula L 0

namespace subformula
variables {L} {m n : ℕ}

instance [has_le_symbol L] : has_preceq (subterm L m n) (subformula L m n) := ⟨λ t u, relation has_le_symbol.le ‹t, u›⟩

instance [has_mem_symbol L] : has_elem (subterm L m n) (subformula L m n) := ⟨λ t u, relation has_mem_symbol.mem ‹t, u›⟩

def and (p : subformula L m n) (q : subformula L m n) : subformula L m n := (p.imply q.neg).neg

def or (p : subformula L m n) (q : subformula L m n) : subformula L m n := p.neg.imply q

def ex (p : subformula L m (n + 1)) : subformula L m n := p.neg.fal.neg

instance : has_logic_symbol (subformula L m n) :=
{ bot := verum.neg,
  top := verum,
  sup := or,
  inf := and,
  arrow := imply,
  neg := neg }

instance : inhabited (subformula L m n) := ⟨⊤⟩

instance : has_eq (subterm L m n) (subformula L m n) := ⟨equal⟩

instance : has_univ_quantifier' (subformula L m) := ⟨@fal L m⟩

instance : has_exists_quantifier' (subformula L m) := ⟨@ex L m⟩

lemma top_eq : @subformula.verum L m n = (⊤) := rfl
lemma imply_eq : @subformula.imply L m n = (⟶) := rfl
lemma equal_eq : @subformula.equal L m n = (=') := rfl
lemma neg_eq : @subformula.neg L m n = has_negation.neg := rfl
lemma fal_eq : @subformula.fal L m n = has_univ_quantifier'.univ := rfl

lemma ex_def (p : subformula L m (n + 1)) : ∃'p = ∼∀'∼p := rfl

lemma bot_def : (⊥ : subformula L m n) = ∼⊤ := rfl

@[simp] lemma equal.inj' (t₁ u₁ t₂ u₂ : subterm L m n) : (t₁ =' t₂ : subformula L m n) = (u₁ =' u₂) ↔ t₁ = u₁ ∧ t₂ = u₂ :=
⟨equal.inj, by simp; exact congr_arg2 (=')⟩

@[simp] lemma imply.inj' (p₁ q₁ p₂ q₂ : subformula L m n) : p₁ ⟶ p₂ = q₁ ⟶ q₂ ↔ p₁ = q₁ ∧ p₂ = q₂ :=
⟨imply.inj, by simp; exact congr_arg2 (⟶)⟩

@[simp] lemma neg.inj' (p q : subformula L m n) : ∼p = ∼q ↔ p = q := ⟨neg.inj, congr_arg _⟩

@[simp] lemma and.inj' (p₁ q₁ p₂ q₂ : subformula L m n) : p₁ ⊓ p₂ = q₁ ⊓ q₂ ↔ p₁ = q₁ ∧ p₂ = q₂ :=
by simp[has_inf.inf, and]

@[simp] lemma or.inj' (p₁ q₁ p₂ q₂ : subformula L m n) : p₁ ⊔ p₂ = q₁ ⊔ q₂ ↔ p₁ = q₁ ∧ p₂ = q₂ :=
by simp[has_sup.sup, or]

@[simp] lemma fal.inj' (p q : subformula L m (n + 1)) : (∀'p : subformula L m n) = ∀'q ↔ p = q := ⟨fal.inj, congr_arg _⟩

@[simp] lemma ex.inj' (p q : subformula L m (n + 1)) : (∃'p : subformula L m n) = ∃'q ↔ p = q := 
by simp[has_exists_quantifier'.ex, ex]

end subformula

@[reducible] def preTheory (L : language.{u}) (m : ℕ) := logic.Theory (subformula L m 0)

@[reducible] def Theory (L : language.{u}) := logic.Theory (subformula L 0 0)

namespace subterm

section rew
variables {L} {m m₁ m₂ m₃ n : ℕ}

@[simp] def rew (s : finitary (subterm L m₂ n) m₁) : subterm L m₁ n → subterm L m₂ n
| (&x)           := s x
| (#x)           := #x
| (function f v) := function f (λ i, (v i).rew)

section rew

lemma eq_rew_of_eq {t : subterm L m₁ n} {s₁ s₂ : finitary (subterm L m₂ n) m₁} (h : s₁ = s₂) :
  rew s₁ t = rew s₂ t := by rw[h]

lemma nested_rew {m₁ m₂ m₃} (s₀ : finitary (subterm L m₂ n) m₁) (s₁ : finitary (subterm L m₃ n) m₂) :
  ∀ t, rew s₁ (rew s₀ t) = rew (rew s₁ ∘ s₀) t
| (&x)           := by simp
| (#x)           := by simp
| (function f v) := by simp; funext i; exact nested_rew (v i)

@[simp] lemma rew_metavar (t : subterm L m n) : rew metavar t = t :=
by induction t; simp*

end rew

def subst (t : subterm L m n) : subterm L (m + 1) n → subterm L m n :=
rew (@fin.cases m (λ _, subterm L m n) t metavar) 

section subst

@[simp] lemma subst_var (u : subterm L m n) (x) : subst u #x = #x := rfl

@[simp] lemma subst_metavar_zero (u : subterm L m n) : subst u &0 = u := rfl

@[simp] lemma subst_metavar_succ (u : subterm L m n) (x : fin m) : subst u &x.succ = &x := by simp[subst]

@[simp] lemma subst_function (u : subterm L m n) {p} (f : L.fn p) (v) : subst u (function f v) = function f (subst u ∘ v) := by simp[subst]

end subst

def mlift' : subterm L m n → subterm L (m + 1) n := rew (metavar ∘ fin.succ)

@[simp] def lift : subterm L m n → subterm L m (n + 1)
| (#x)           := #x.succ
| (&x)           := &x
| (function f v) := function f (λ i, (v i).lift)

section lift

lemma lift_rew (s : finitary (subterm L m₂ n) m₁) (t : subterm L m₁ n) : (t.rew s).lift = t.lift.rew (lift ∘ s) :=
by induction t with x x p f v IH; simp; exact funext IH

end lift

@[simp] def mlift : subterm L m n → subterm L (m + 1) n
| (&x)           := &x.succ
| (#x)           := #x
| (function f v) := function f (λ i, (v i).mlift)

section mlift

lemma mlift_eq_rew : @mlift L m n = rew (metavar ∘ fin.succ) :=
funext (λ t, by induction t; simp*)

lemma mlift_rew (s : finitary (subterm L m₂ n) m₁) (t : subterm L m₁ n) : (t.rew s).mlift = t.rew (mlift ∘ s) :=
by induction t with x x p f v IH; simp; exact funext IH

lemma mlift_lift (t : subterm L m n) : t.lift.mlift = t.mlift.lift :=
by induction t; simp*

@[simp] lemma subst_mlift (u : subterm L m n) (t : subterm L m n) :
  subst u t.mlift = t :=
by induction t; simp; exact funext (λ x, by simp*)

lemma mlift_subst (u : subterm L m n) (t : subterm L (m + 1) n) :
  (subst u t).mlift = t.rew (@fin.cases m (λ _, subterm L (m + 1) n) (mlift u) (mlift ∘ metavar)) :=
by simp[subst, mlift_rew];
   refine eq_rew_of_eq (funext $ λ x, by rcases (fin.eq_zero_or_eq_succ x) with (rfl | ⟨x, rfl⟩); simp) 

end mlift

/-
  #0 #1 #2 #3 #4 ... #(n - 1) #n &0 &1 &3 &4 ... &(m - 1)
      ↓push                       ↑pull
  #0 #1 #2 #3 #4 ... #(n - 1) &0 &1 &3 &4 &5 ... &m
-/

def push : subterm L m (n + 1) → subterm L (m + 1) n
| (&x)           := &x.succ
| (#x)           := @fin.last_cases n (λ _, subterm L (m + 1) n) &0 var x
| (function f v) := function f (λ i, (v i).push)

section push

@[simp] lemma push_metavar (x) : (&x : subterm L m (n + 1)).push = &x.succ := rfl

@[simp] lemma push_var_zero_last : (#(fin.last n) : subterm L m (n + 1)).push = &0 := by simp[push]

@[simp] lemma push_var_zero (x) : (#(fin.cast_succ x) : subterm L m (n + 1)).push = #x := by simp[push]

@[simp] lemma push_function {p} (f : L.fn p) (v : fin p → subterm L m (n + 1)) :
  (function f v : subterm L m (n + 1)).push = function f (push ∘ v) := by simp[push]

end push

def pull : subterm L (m + 1) n → subterm L m (n + 1)
| (&x)           := fin.cases #(fin.last n) metavar x
| (#x)           := #x.cast_succ
| (function f v) := function f (λ i, (v i).pull)

section pull

@[simp] lemma pull_metavar_zero : (&0 : subterm L (m + 1) n).pull = #(fin.last n) := rfl

@[simp] lemma pull_metavar_succ (x : fin m) : (&x.succ : subterm L (m + 1) n).pull = &x := by simp[pull]

@[simp] lemma pull_var (x) : (#x : subterm L (m + 1) n).pull = #x.cast_succ := by simp[pull]

@[simp] lemma pull_function {p} (f : L.fn p) (v : fin p → subterm L (m + 1) n) :
  (function f v : subterm L (m + 1) n).pull = function f (pull ∘ v) := by simp[pull]

@[simp] lemma push_pull (t : subterm L m (n + 1)) : t.push.pull = t :=
by{ induction t, 
    case metavar : x { simp },
    case var : x { refine fin.last_cases _ _ x; simp },
    case function : p f v IH { simp, funext x, simp[IH] } }

@[simp] lemma pull_push (t : subterm L (m + 1) n) : t.pull.push = t :=
by{ induction t,
    case metavar : x { refine fin.cases _ _ x; simp },
    case var : x { simp },
    case function : p f v IH { simp, funext x, simp[IH] } }

end pull

def dummy : subterm L m n → subterm L m (n + 1) := pull ∘ mlift

section dummy

@[simp] lemma dummy_metavar (x) : dummy (&x : subterm L m n) = &x := by simp[dummy]

@[simp] lemma dummy_var (x) : dummy (#x : subterm L m n) = #x.cast_succ := by simp[dummy]

@[simp] lemma dummy_function {p} (f : L.fn p) (v : finitary (subterm L m n) p) :
  dummy (function f v) = function f (dummy ∘ v) := by simp[dummy]

end dummy

end rew

end subterm

namespace subformula
open subterm finitary
variables {L} {m m₁ m₂ m₃ n : ℕ}

@[simp] def complexity : Π {n}, subformula L m n → ℕ
| n verum          := 0
| n (relation p v) := 0
| n (equal t u)    := 0
| n (imply p q)    := max p.complexity q.complexity + 1
| n (neg p)        := p.complexity + 1
| n (fal p)        := p.complexity + 1

@[simp] lemma imply_complexity (p q : subformula L m n) : (p ⟶ q).complexity = max p.complexity q.complexity + 1 := by refl

def rew' {m₁ m₂} : Π {n}, finitary (subterm L m₂ n) m₁ → subformula L m₁ n → subformula L m₂ n
| n s verum          := ⊤
| n s (relation p v) := relation p (λ i, (v i).rew s)
| n s (equal t u)    := (t.rew s) =' (u.rew s)
| n s (imply p q)    := p.rew' s ⟶ q.rew' s
| n s (neg p)        := ∼p.rew' s
| n s (fal p)        := ∀'p.rew' (subterm.lift ∘ s)

def rew (s : finitary (subterm L m₂ n) m₁) : subformula L m₁ n →ₗ subformula L m₂ n :=
{ to_fun := rew' s,
  map_neg' := λ p, by refl,
  map_imply' := λ p q, by refl,
  map_and' := λ p q, by refl,
  map_or' := λ p q, by refl,
  map_top' := by refl,
  map_bot' := by refl }

section rew
variables (s : finitary (subterm L m₂ n) m₁)

lemma rew_def (p : subformula L m₁ n) : rew s p = rew' s p := rfl

variables {s}

@[simp] lemma rew_relation {p} (r : L.pr p) (v) :
  rew s (relation r v) = relation r (subterm.rew s ∘ v) := rfl

@[simp] lemma rew_equal (t u : subterm L m₁ n) :
  rew s (t =' u) = (t.rew s =' u.rew s) := rfl

@[simp] lemma rew_fal (p : subformula L m₁ (n + 1)) :
  rew s (∀'p) = ∀'rew (subterm.lift ∘ s) p := rfl

@[simp] lemma rew_ex (p : subformula L m₁ (n + 1)) :
  rew s (∃'p) = ∃'rew (subterm.lift ∘ s) p := by simp[ex_def]

lemma rew_eq_self_of_eq {s : finitary (subterm L m n) m} (h : s = metavar) (p : subformula L m n) : rew s p = p :=
by { induction p; simp[top_eq, equal_eq, imply_eq, neg_eq, fal_eq, subterm.mlift_rew, *],
     case relation : n p r v { funext x; simp },
     case fal : n p IH { refine IH (funext $ by simp) } }

@[simp] lemma rew_metavar (p : subformula L m n) : rew metavar p = p := rew_eq_self_of_eq rfl p

lemma nested_rew {m₁ m₂ m₃} : ∀ {n} (p : subformula L m₁ n) (s₀ : finitary (subterm L m₂ n) m₁) (s₁ : finitary (subterm L m₃ n) m₂),
  rew s₁ (rew s₀ p) = rew (subterm.rew s₁ ∘ s₀) p
| n verum          s₀ s₁ := by simp[top_eq]
| n (relation p v) s₀ s₁ := by simp; funext; simp[subterm.nested_rew]
| n (equal t u)    s₀ s₁ := by simp[equal_eq, subterm.nested_rew]
| n (imply p q)    s₀ s₁ := by simp[imply_eq, nested_rew p, nested_rew q]
| n (neg p)        s₀ s₁ := by simp[neg_eq, nested_rew p]
| n (fal p)        s₀ s₁ := by simp[fal_eq, nested_rew p]; { 
  have : subterm.rew (subterm.lift ∘ s₁) ∘ subterm.lift ∘ s₀ = subterm.lift ∘ subterm.rew s₁ ∘ s₀,
  { funext i; simp[lift_rew] },
  rw this }

lemma eq_rew_of_eq {p : subformula L m₁ n} {s₁ s₂ : finitary (subterm L m₂ n) m₁} (h : s₁ = s₂) :
  rew s₁ p = rew s₂ p := by rw[h]

end rew

def subst (t : subterm L m n) : subformula L (m + 1) n →ₗ subformula L m n :=
rew (@fin.cases m (λ _, subterm L m n) t metavar)

section subst
variables (u : subterm L m n)

@[simp] lemma subst_relation {p} (r : L.pr p) (v) :
  subst u (relation r v) = relation r (subterm.subst u ∘ v) := by simp[subst, subterm.subst]

@[simp] lemma subst_equal (t₁ t₂ : subterm L (m + 1) n) :
  subst u (t₁ =' t₂) = (u.subst t₁ =' u.subst t₂) := by simp[subst, subterm.subst]

@[simp] lemma subst_fal (p : subformula L (m + 1) (n + 1)) :
  subst u (∀'p) = ∀'subst u.lift p :=
by simp[subst]; refine eq_rew_of_eq (funext $ λ x, by rcases (fin.eq_zero_or_eq_succ x) with (rfl | ⟨x, rfl⟩); simp)

@[simp] lemma subst_ex (p : subformula L (m + 1) (n + 1)) :
  subst u (∃'p) = ∃'subst u.lift p := by simp[ex_def]

end subst

def mlift' {m} : Π {n}, subformula L m n → subformula L (m + 1) n
| n verum          := ⊤
| n (relation p v) := relation p (mlift ∘ v)
| n (equal t u)    := t.mlift =' u.mlift
| n (imply p q)    := p.mlift' ⟶ q.mlift'
| n (neg p)        := ∼p.mlift'
| n (fal p)        := ∀'p.mlift'

def mlift : subformula L m n →ₗ subformula L (m + 1) n :=
{ to_fun := mlift',
  map_neg' := λ p, by refl,
  map_imply' := λ p q, by refl,
  map_and' := λ p q, by refl,
  map_or' := λ p q, by refl,
  map_top' := by refl,
  map_bot' := by refl }

section mlift

@[simp] lemma mlift_relation {p} (r : L.pr p) (v : finitary (subterm L m n) p) :
  mlift (relation r v) = relation r (subterm.mlift ∘ v) := rfl

@[simp] lemma mlift_equal (t u : subterm L m n) :
  mlift (t =' u : subformula L m n) = (t.mlift =' u.mlift) := rfl

@[simp] lemma mlift_fal (p : subformula L m (n + 1)) :
  mlift (∀'p) = ∀'mlift p := rfl

@[simp] lemma mlift_ex (p : subformula L m₁ (n + 1)) :
  mlift (∃'p) = ∃'mlift p := by simp[ex_def]

variables (s : finitary (subterm L m₂ n) m₁)

lemma mlift_rew (p : subformula L m₁ n) : mlift (rew s p) = rew (subterm.mlift ∘ s) p :=
begin
  induction p; simp[top_eq, equal_eq, imply_eq, neg_eq, fal_eq, subterm.mlift_rew, *],
  case relation : n p r v { funext x; simp[subterm.mlift_rew] },
  case fal : n p IH {
    have : subterm.mlift ∘ subterm.lift ∘ s = subterm.lift ∘ subterm.mlift ∘ s,
    { funext x; simp[subterm.mlift_lift] },
    rw[this] }
end

lemma mlift_eq_rew : @mlift L m n = rew (metavar ∘ fin.succ) :=
by { ext p, induction p; simp[top_eq, equal_eq, imply_eq, neg_eq, fal_eq, subterm.mlift_eq_rew, *],
     exact eq_rew_of_eq (funext $ λ x, by simp) }

@[simp] lemma subst_mlift (u : subterm L m n) (p : subformula L m n) :
  subst u p.mlift = p :=
by { simp[mlift_eq_rew, subst, nested_rew], refine rew_eq_self_of_eq (funext $ by simp) _, }

lemma mlift_subst (u : subterm L m n) (p : subformula L (m + 1) n) :
  mlift (subst u p) = rew (@fin.cases m (λ _, subterm L (m + 1) n) u.mlift (subterm.mlift ∘ metavar)) p :=
by simp[subst, mlift_rew]; refine eq_rew_of_eq (funext $ λ x, by rcases (fin.eq_zero_or_eq_succ x) with (rfl | ⟨x, rfl⟩); simp)

end mlift

def push' {m} : Π {n}, subformula L m (n + 1) → subformula L (m + 1) n
| n verum          := ⊤
| n (relation p v) := relation p (subterm.push ∘ v)
| n (equal t u)    := t.push =' u.push
| n (imply p q)    := p.push' ⟶ q.push'
| n (neg p)        := ∼p.push'
| n (fal p)        := ∀'p.push'
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.complexity)⟩]}

def push : subformula L m (n + 1) →ₗ subformula L (m + 1) n :=
{ to_fun := push',
  map_neg' := λ p, by unfold has_negation.neg; simp[push']; refl,
  map_imply' := λ p q, by unfold has_arrow.arrow; simp[push']; refl,
  map_and' := λ p q, by unfold has_inf.inf; simp[and, push']; refl,
  map_or' := λ p q, by unfold has_sup.sup; simp[or, push']; refl,
  map_top' := by unfold has_top.top; simp[push']; refl,
  map_bot' := by unfold has_bot.bot; simp[push']; refl }

section push

lemma push_def (p : subformula L m (n + 1)) : push p = push' p := rfl

@[simp] lemma push_relation {p} (r : L.pr p) (v : finitary (subterm L m (n + 1)) p) :
  push (relation r v) = relation r (subterm.push ∘ v) := by simp[push_def, push']

@[simp] lemma push_equal (t u : subterm L m (n + 1)) :
  push (t =' u : subformula L m (n + 1)) = (t.push =' u.push) := by unfold has_eq.eq; simp[push_def, push']; refl

@[simp] lemma push_fal (p : subformula L m (n + 1 + 1)) :
  push (∀'p) = ∀'push p := by unfold has_univ_quantifier'.univ; simp[push_def, push']; refl

@[simp] lemma push_ex (p : subformula L m₁ (n + 1 + 1)) :
  push (∃'p) = ∃'push p := by simp[ex_def]

end push

def pull' {m} : Π {n}, subformula L (m + 1) n → subformula L m (n + 1)
| n verum          := ⊤
| n (relation p v) := relation p (subterm.pull ∘ v)
| n (equal t u)    := t.pull =' u.pull
| n (imply p q)    := p.pull' ⟶ q.pull'
| n (neg p)        := ∼p.pull'
| n (fal p)        := ∀'p.pull'

def pull : subformula L (m + 1) n →ₗ subformula L m (n + 1) :=
{ to_fun := pull',
  map_neg' := λ p, by refl,
  map_imply' := λ p q, by refl,
  map_and' := λ p q, by refl,
  map_or' := λ p q, by refl,
  map_top' := by refl,
  map_bot' := by refl }

section pull

lemma pull_def (p : subformula L (m + 1) n) : pull p = pull' p := rfl

@[simp] lemma pull_relation {p} (r : L.pr p) (v : finitary (subterm L (m + 1) n) p) :
  pull (relation r v) = relation r (subterm.pull ∘ v) := by refl

@[simp] lemma pull_equal (t u : subterm L (m + 1) n) :
  pull (t =' u : subformula L (m + 1) n) = (t.pull =' u.pull) := by refl

@[simp] lemma pull_fal (p : subformula L (m + 1) (n + 1)) :
  pull (∀'p) = ∀'pull p := by refl

@[simp] lemma pull_ex (p : subformula L (m + 1) (n + 1)) :
  pull (∃'p) = ∃'pull p := by simp[ex_def]

end pull

def dummy : subformula L m n →ₗ subformula L m (n + 1) := pull.comp mlift

section dummy

@[simp] lemma dummy_relation {p} (r : L.pr p) (v : finitary (subterm L m n) p) :
  dummy (relation r v) = relation r (subterm.dummy ∘ v) := by simp[dummy, subterm.dummy]

@[simp] lemma dummy_equal (t u : subterm L m n) :
  dummy (t =' u : subformula L m n) = (t.dummy =' u.dummy) := by simp[dummy, subterm.dummy]

@[simp] lemma dummy_fal (p : subformula L m (n + 1)) : dummy (∀'p) = ∀'(dummy p) := by simp[dummy]

@[simp] lemma dummy_ex (p : subformula L m (n + 1)) : dummy (∃'p) = ∃'(dummy p) := by simp[dummy]

end dummy

@[simp] lemma push_pull : ∀ {n} (p : subformula L m (n + 1)), p.push.pull = p
| n verum          := by simp[top_eq]
| n (relation p v) := by simp; funext x; simp
| n (equal t u)    := by simp[equal_eq]
| n (imply p q)    := by simp[imply_eq]; exact ⟨push_pull p, push_pull q⟩
| n (neg p)        := by simp[neg_eq]; exact push_pull p
| n (fal p)        := by simp[fal_eq]; exact push_pull p
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.complexity)⟩]}

@[simp] lemma pull_push : ∀ {n} (p : subformula L (m + 1) n), p.pull.push = p
| n verum          := by simp[top_eq]
| n (relation p v) := by simp; funext x; simp
| n (equal t u)    := by simp[equal_eq]
| n (imply p q)    := by simp[imply_eq]; exact ⟨pull_push p, pull_push q⟩
| n (neg p)        := by simp[neg_eq]; exact pull_push p
| n (fal p)        := by simp[fal_eq]; exact pull_push p

def qr {m} : Π {n}, subformula L m n → ℕ
| n verum          := 0
| n (relation r v) := 0
| n (equal t u)    := 0
| n (imply p q)    := max p.qr q.qr
| n (neg p)        := p.qr
| n (fal p)        := p.qr + 1

def is_open {m n} (p : subformula L m n) : Prop := p.qr = 0

section qr
variables {m n}

@[simp] lemma qr_top : (⊤ : subformula L m n).qr = 0 := rfl

@[simp] lemma qr_bot : (⊥ : subformula L m n).qr = 0 := rfl

@[simp] lemma qr_relation {p} (r : L.pr p) (v : finitary (subterm L m n) p) : (relation r v).qr = 0 := rfl

@[simp] lemma qr_equal (t u : subterm L m n) : (t =' u : subformula L m n).qr = 0 := rfl

@[simp] lemma qr_imply (p q : subformula L m n) : (p ⟶ q : subformula L m n).qr = max p.qr q.qr := rfl

@[simp] lemma qr_and (p q : subformula L m n) : (p ⊓ q : subformula L m n).qr = max p.qr q.qr := rfl

@[simp] lemma qr_or (p q : subformula L m n) : (p ⊔ q : subformula L m n).qr = max p.qr q.qr := rfl

@[simp] lemma qr_iff (p q : subformula L m n) : (p ⟷ q : subformula L m n).qr = max p.qr q.qr := by simp[lrarrow_def, max_comm]

@[simp] lemma qr_neg (p : subformula L m n) : (∼p).qr = p.qr := rfl

@[simp] lemma qr_fal (p : subformula L m (n + 1)) : (∀'p).qr = p.qr + 1 := rfl

@[simp] lemma qr_ex (p : subformula L m (n + 1)) : (∃'p).qr = p.qr + 1 := rfl

end qr

end subformula

namespace preTheory
variables {L} {m : ℕ} (T U : preTheory L m)

def mlift : preTheory L (m + 1) := subformula.mlift '' T

lemma mlift_insert (p : formula L m) : (insert p T).mlift = insert p.mlift T.mlift :=
by simp[mlift, set.image_insert_eq]

end preTheory

end fol
