import lib.lib tactic data.set_like.basic logic translation

universe u

namespace fol
open_locale logic_symbol

structure language : Type (u+1) :=
(fn : ℕ → Type u)
(pr : ℕ → Type u)

namespace language
variables (L : language.{u})
/-
class has_zero_symbol (L : language) := (zero : L.fn 0)

class has_succ_symbol (L : language) := (succ : L.fn 1)

class has_add_symbol (L : language) := (add : L.fn 2)

class has_mul_symbol (L : language) := (mul : L.fn 2)

class has_le_symbol (L : language) := (le : L.pr 2)

class has_mem_symbol (L : language) := (mem : L.pr 2)
-/

protected def empty : language.{u} :=
{ fn := λ _, pempty, pr := λ _, pempty }

instance (n) : is_empty (language.empty.fn n) := ⟨by rintros ⟨⟩⟩

instance (n) : is_empty (language.empty.pr n) := ⟨by rintros ⟨⟩⟩

instance (n) : has_to_string (language.empty.fn n) := ⟨by rintros ⟨⟩⟩

instance (n) : has_to_string (language.empty.pr n) := ⟨by rintros ⟨⟩⟩

end language

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

/-
instance [has_zero_symbol L] : has_zero (subterm L m n) := ⟨function has_zero_symbol.zero finitary.nil⟩

instance [has_succ_symbol L] : has_succ (subterm L m n) := ⟨λ t, function has_succ_symbol.succ ‹t›⟩

instance [has_add_symbol L] : has_add (subterm L m n) := ⟨λ t u, function has_add_symbol.add ‹t, u›⟩

instance [has_mul_symbol L] : has_mul (subterm L m n) := ⟨λ t u, function has_mul_symbol.mul ‹t, u›⟩

postfix `˙`:max := numeral
-/

/-
notation `##'` := idvar_inv _

@[simp] lemma idvar_inv_function (n : ℕ) (i : fin n) : (##' : finitary (term L) n) i = #(n - i - 1) := rfl

@[simp] lemma idvar_inv_nil : (##' : finitary (term L) 0) = finitary.nil := by ext

@[simp] lemma idvar_inv_eq_singleton : (##' : finitary (term L) 1) = ‹#0› := by ext; by simp

@[simp] lemma idvar_inv_eq_doubleton : (##' : finitary (term L) 2) = ‹#1, #0› := by ext; by simp

variables (L)


-/

variables (L) (m n)

def to_string [∀ n, has_to_string (L.fn n)] : subterm L m n → string
| &n                            := "&" ++ has_to_string.to_string n
| #n                            := "#" ++ has_to_string.to_string n
| (@function _ _ _ 0 c v)       := has_to_string.to_string c
| (@function _ _ _ 1 c v)       := has_to_string.to_string c ++ "(" ++ to_string (v 0) ++ ")"
| (@function _ _ _ 2 c v)       := to_string (v 0) ++ has_to_string.to_string c ++ to_string (v 1)
| (@function _ _ _ (n + 3) c v) :=
    has_to_string.to_string c ++ "(" ++ @has_to_string.to_string (finitary _ _) _ (λ i, to_string (v i)) ++ ")"

instance [∀ n, has_to_string (L.fn n)] : has_to_string (subterm L m n) := ⟨to_string L m n⟩

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

/-
instance [has_le_symbol L] : has_preceq (subterm L m n) (subformula L m n) := ⟨λ t u, relation has_le_symbol.le ‹t, u›⟩

instance [has_mem_symbol L] : has_elem (subterm L m n) (subformula L m n) := ⟨λ t u, relation has_mem_symbol.mem ‹t, u›⟩
-/
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

section ne
variables {k : ℕ} (r : L.pr k) (v : finitary (subterm L m n) k) (t u : subterm L m n)
  (p p₁ p₂ : subformula L m n) (q : subformula L m (n + 1))

@[simp] lemma verum_ne_predicate : ⊤ ≠ relation r v.
@[simp] lemma verum_ne_equal : ⊤ ≠ (t =' u : subformula L m n).
@[simp] lemma verum_ne_imply : ⊤ ≠ (p₁ ⟶ p₂).
@[simp] lemma verum_ne_neg : ⊤ ≠ ∼p.
@[simp] lemma verum_ne_fal : ⊤ ≠ ∀'q.
@[simp] lemma predicate_ne_verum : relation r v ≠ ⊤.
@[simp] lemma predicate_ne_equal : relation r v ≠ (t =' u).
@[simp] lemma predicate_ne_imply : relation r v ≠ p₁ ⟶ p₂.
@[simp] lemma predicate_ne_neg : relation r v ≠ ∼p.
@[simp] lemma predicate_ne_fal : relation r v ≠ ∀'q.
@[simp] lemma equal_ne_verum : (t =' u) ≠ (⊤ : subformula L m n).
@[simp] lemma equal_ne_predivate : (t =' u) ≠ relation r v.
@[simp] lemma equal_ne_imply : (t =' u) ≠ p₁ ⟶ p₂.
@[simp] lemma equal_ne_neg : (t =' u) ≠ ∼p.
@[simp] lemma equal_ne_fal : (t =' u) ≠ ∀'q.
@[simp] lemma imply_ne_verum : p₁ ⟶ p₂ ≠ ⊤.
@[simp] lemma imply_ne_relation : p₁ ⟶ p₂ ≠ relation r v.
@[simp] lemma imply_ne_equal : p₁ ⟶ p₂ ≠ (t =' u).
@[simp] lemma imply_ne_neg : p₁ ⟶ p₂ ≠ ∼p.
@[simp] lemma imply_ne_fal : p₁ ⟶ p₂ ≠ ∀'q.
@[simp] lemma neg_ne_verum : ∼p ≠ ⊤.
@[simp] lemma neg_ne_relation : ∼p ≠ relation r v.
@[simp] lemma neg_ne_equal : ∼p ≠ (t =' u).
@[simp] lemma neg_ne_imply : ∼p ≠ p₁ ⟶ p₂.
@[simp] lemma neg_ne_fal : ∼p ≠ ∀'q.
@[simp] lemma fal_ne_verum : ∀'q ≠ ⊤.
@[simp] lemma fal_ne_relation : ∀'q ≠ relation r v.
@[simp] lemma fal_ne_equal : ∀'q ≠ (t =' u).
@[simp] lemma fal_ne_imply : ∀'q ≠ p₁ ⟶ p₂.
@[simp] lemma fal_ne_neg : ∀'q ≠ ∼p.

end ne
variables (L) (m)

def to_string [∀ n, has_to_string (L.fn n)] [∀ n, has_to_string (L.pr n)] : Π n, subformula L m n → string
| n verum          := "⊤"
| n (relation p v) := has_to_string.to_string p
| n (equal t u)    := has_to_string.to_string t ++ " = " ++ has_to_string.to_string u
| n (imply p q)    := to_string _ p ++ " → " ++ to_string _ q
| n (neg p)        := "¬(" ++ to_string _ p ++ ")"
| n (fal p)        := "∀(" ++ to_string _ p ++ ")"

instance [∀ n, has_to_string (L.fn n)] [∀ n, has_to_string (L.pr n)] : has_to_string (subformula L m n) := ⟨to_string L m n⟩

end subformula

@[reducible] def preTheory (L : language.{u}) (m : ℕ) := logic.Theory (subformula L m 0)

@[reducible] def Theory (L : language.{u}) := logic.Theory (subformula L 0 0)

namespace subterm

section rew
variables {L} {m m₁ m₂ m₃ n : ℕ} {s : finitary (subterm L m₂ n) m₁}

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

lemma mlift_lift (t : subterm L m n) : t.mlift.lift = t.lift.mlift :=
by induction t; simp*

lemma mlift_inj : function.injective (@mlift L m n)
| (&x)             (&y)             := by simp
| (&x)             (#y)             := by simp
| (&x)             (function f v)   := by simp
| (#x)             (&y)             := by simp
| (#x)             (#y)             := by simp
| (#x)             (function f v)   := by simp
| (function f₁ v₁) (&y)             := by simp
| (function f₁ v₁) (#y)             := by simp
| (function f₁ v₁) (function f₂ v₂) :=
  by { simp, rintros rfl rfl,
       simp, intros h, funext i, exact @mlift_inj (v₁ i) (v₂ i) (congr_fun h i) }

end mlift
/-
  #0 #1 #2 #3 #4 ... #(n - 1) #n &0 &1 &3 &4 ... &(m - 1)
      ↓push                       ↑pull
  #0 #1 #2 #3 #4 ... #(n - 1) &0 &1 &3 &4 &5 ... &m
-/

def push : subterm L m (n + 1) → subterm L (m + 1) n
| (&x)           := &x.succ
| (#x)           := (var <* &0) x
| (function f v) := function f (λ i, (v i).push)

section push

@[simp] lemma push_metavar (x) : (&x : subterm L m (n + 1)).push = &x.succ := rfl

@[simp] lemma push_var_last : (#(fin.last n) : subterm L m (n + 1)).push = &0 := by simp[push]

@[simp] lemma push_var_cast (x) : (#(fin.cast_succ x) : subterm L m (n + 1)).push = #x := by simp[push]

@[simp] lemma push_function {p} (f : L.fn p) (v : fin p → subterm L m (n + 1)) :
  (function f v : subterm L m (n + 1)).push = function f (push ∘ v) := by simp[push]

lemma push_lift_comm (t : subterm L m (n + 1)) : t.lift.push = t.push.lift :=
by { induction t; simp*,
     case var : x { refine fin.last_cases _ _ x; simp[fin.succ_cast_succ] },
     case function : k f v IH
     { funext i, exact IH i } }

end push

def pull : subterm L (m + 1) n → subterm L m (n + 1)
| (&x)           := (#(fin.last n) *> metavar) x
| (#x)           := #x.cast_succ
| (function f v) := function f (λ i, (v i).pull)

section pull

@[simp] lemma pull_metavar_zero : (&0 : subterm L (m + 1) n).pull = #(fin.last n) := rfl

@[simp] lemma pull_metavar_succ (x : fin m) : (&x.succ : subterm L (m + 1) n).pull = &x := by simp[pull]

@[simp] lemma pull_var (x) : (#x : subterm L (m + 1) n).pull = #x.cast_succ := by simp[pull]

@[simp] lemma pull_function {p} (f : L.fn p) (v : fin p → subterm L (m + 1) n) :
  (function f v : subterm L (m + 1) n).pull = function f (pull ∘ v) := by simp[pull]

@[simp] lemma pull_push (t : subterm L m (n + 1)) : t.push.pull = t :=
by{ induction t, 
    case metavar : x { simp },
    case var : x { refine fin.last_cases _ _ x; simp },
    case function : p f v IH { simp, funext x, simp[IH] } }

@[simp] lemma push_pull (t : subterm L (m + 1) n) : t.pull.push = t :=
by{ induction t,
    case metavar : x { refine fin.cases _ _ x; simp },
    case var : x { simp },
    case function : p f v IH { simp, funext x, simp[IH] } }

lemma push_rew_pull (t : subterm L (m₁ + 1) n) (s : fin m₁ → subterm L m₂ (n + 1)) :
  (rew s t.pull).push = rew (&0 *> push ∘ s) t :=
by { induction t; simp*,
      case metavar : x { refine fin.cases _ _ x; simp },
      case function : k f v IH
      { funext i, exact IH i } }

end pull

/-
  #0 #1 ... #(n-1) &0 &1 ... &m
            ↓msubst u
  #0 #1 ... #(n-1) u  &0 ... &(m-1)
-/

def msubst (t : subterm L m n) : subterm L (m + 1) n → subterm L m n := rew (t *> metavar)

section msubst

@[simp] lemma msubst_var (u : subterm L m n) (x) : msubst u #x = #x := by simp[msubst]

@[simp] lemma msubst_metavar_zero (u : subterm L m n) : msubst u &0 = u := by simp[msubst]

@[simp] lemma msubst_metavar_succ (u : subterm L m n) (x : fin m) : msubst u &x.succ = &x := by simp[msubst]

@[simp] lemma msubst_function (u : subterm L m n) {p} (f : L.fn p) (v) :
  msubst u (function f v) = function f (msubst u ∘ v) := by simp[msubst]

end msubst

/-
  #0 #1 ... #(n-1) #n &0 &1 ... &(m-1)
            ↓subst u
  #0 #1 ... #(n-1) u  &0 &1 ... &(m-1)
-/

def subst (t : subterm L m n) : subterm L m (n + 1) → subterm L m n := msubst t ∘ push

section subst

@[simp] lemma subst_var_cast_succ (u : subterm L m n) (x : fin n) : subst u #x.cast_succ = #x := by simp[subst]

@[simp] lemma subst_var_last (u : subterm L m n) : subst u #(fin.last n) = u := by simp[subst]

@[simp] lemma subst_metavar (u : subterm L m n) (x) : subst u &x = &x := by simp[subst]

@[simp] lemma subst_function (u : subterm L m n) {p} (f : L.fn p) (v) :
  subst u (function f v) = function f (subst u ∘ v) := by simp[subst]

@[simp] lemma mlift_subst (u : subterm L m n) (t : subterm L m (n + 1)) :
  (subst u t).mlift = subst u.mlift t.mlift :=
by { induction t; simp*, case var : x { refine fin.last_cases _ _ x; simp } }

lemma msubst_push (u : subterm L m n) (t : subterm L m (n + 1)) : msubst u (push t) = subst u t := rfl

end subst

def dummy : subterm L m n → subterm L m (n + 1) := pull ∘ mlift

section dummy

@[simp] lemma dummy_metavar (x) : dummy (&x : subterm L m n) = &x := by simp[dummy]

@[simp] lemma dummy_var (x) : dummy (#x : subterm L m n) = #x.cast_succ := by simp[dummy]

@[simp] lemma dummy_function {p} (f : L.fn p) (v : finitary (subterm L m n) p) :
  dummy (function f v) = function f (dummy ∘ v) := by simp[dummy]

end dummy

@[simp] lemma pull_msubst_push_mlift (t : subterm L m (n + 1)) : (pull $ msubst &0 $ push $ mlift t) = t :=
begin
  induction t; simp, 
  case var : x { refine fin.last_cases _ _ x; simp },
  case function : k f v IH
  { funext i, simpa using IH i }
end

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

lemma mlift_inj : function.injective (@mlift L m n) := λ p q,
begin
  induction p,
  case verum { cases q; simp[top_eq, equal_eq, imply_eq, neg_eq, fal_eq] },
  case relation : n k r v₁
  { cases q; simp[top_eq, equal_eq, imply_eq, neg_eq, fal_eq];
    case relation : _ _ r₂ v₂
    { rintros rfl rfl, simp, intros h, funext i, exact @subterm.mlift_inj _ _ _ (v₁ i) (v₂ i) (congr_fun h i) } },
  case equal : n t₁ u₁
  { induction q; simp[top_eq, equal_eq, imply_eq, neg_eq, fal_eq],
    case equal : _ t₂ u₂ { intros ht hu, exact ⟨subterm.mlift_inj ht, subterm.mlift_inj hu⟩ } },
  case imply : _ p₁ p₂ IH₁ IH₂
  { cases q; simp[top_eq, equal_eq, imply_eq, neg_eq, fal_eq],
      case imply : _ q₁ q₂ { intros h₁ h₂, exact ⟨IH₁ _ h₁, IH₂ _ h₂⟩ } },
  case neg : n p IH
  { cases q; simp[top_eq, equal_eq, imply_eq, neg_eq, fal_eq],
      case neg : _ p₂ { intros h, exact IH _ h } },
  case fal : n p IH
  { cases q; simp[top_eq, equal_eq, imply_eq, neg_eq, fal_eq],
      case fal : _ p₂ { intros h, exact IH _ h } }
end

end mlift

def succ_rec {C : Π n, subformula L m (n + 1) → Sort*}
  (hverum : Π {n : ℕ}, C n ⊤)
  (hrelation : Π {n l : ℕ} (r : L.pr l) (v : fin l → subterm L m (n + 1)), C n (relation r v))
  (hequal : Π {n : ℕ} (t u : subterm L m (n + 1)), C n (t =' u))
  (himply : Π {n : ℕ} (p q : subformula L m (n + 1)), C n p → C n q → C n (p ⟶ q))
  (hneg : Π {n : ℕ} (p : subformula L m (n + 1)), C n p → C n ∼p)
  (hfal : Π {n : ℕ} (p : subformula L m (n + 1 + 1)), C (n + 1) p → C n (∀'p)) :
  Π {n : ℕ} (p : subformula L m (n + 1)), C n p
| n verum := hverum
| n (relation r v) := hrelation r v
| n (equal t u)    := hequal t u
| n (imply p q)    := himply p q (succ_rec p) (succ_rec q)
| n (neg p)        := hneg p (succ_rec p)
| n (fal p)        := hfal p (succ_rec p)
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.complexity)⟩]}

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

@[simp] lemma pull_push : ∀ {n} (p : subformula L m (n + 1)), p.push.pull = p
| n verum          := by simp[top_eq]
| n (relation p v) := by simp; funext x; simp
| n (equal t u)    := by simp[equal_eq]
| n (imply p q)    := by simp[imply_eq]; exact ⟨pull_push p, pull_push q⟩
| n (neg p)        := by simp[neg_eq]; exact pull_push p
| n (fal p)        := by simp[fal_eq]; exact pull_push p
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.complexity)⟩]}

@[simp] lemma push_pull : ∀ {n} (p : subformula L (m + 1) n), p.pull.push = p
| n verum          := by simp[top_eq]
| n (relation p v) := by simp; funext x; simp
| n (equal t u)    := by simp[equal_eq]
| n (imply p q)    := by simp[imply_eq]; exact ⟨push_pull p, push_pull q⟩
| n (neg p)        := by simp[neg_eq]; exact push_pull p
| n (fal p)        := by simp[fal_eq]; exact push_pull p

lemma push_inj : function.injective (@push L m n) :=
@function.left_inverse.injective _ _ (@pull L m n) _ pull_push

lemma pull_inj : function.injective (@pull L m n) :=
@function.left_inverse.injective _ _ (@push L m n) _ push_pull

lemma push_rew_pull : ∀ {n} (p : subformula L (m₁ + 1) n) (s : fin m₁ → subterm L m₂ (n + 1)),
  (rew s p.pull).push = rew (&0 *> subterm.push ∘ s) p
| n verum          s := by simp[top_eq]
| n (relation p v) s := by simp; funext x; simp[subterm.push_rew_pull]
| n (equal t u)    s := by simp[equal_eq, subterm.push_rew_pull]
| n (imply p q)    s := by simp[imply_eq]; exact ⟨push_rew_pull p s, push_rew_pull q s⟩
| n (neg p)        s := by simp[neg_eq]; exact push_rew_pull p s
| n (fal p)        s := by simp[fal_eq]; {
    have : subterm.lift ∘ subterm.push ∘ s = subterm.push ∘ subterm.lift ∘ s,
    { funext i; simp[subterm.push_lift_comm] },
    rw [fin.comp_left_concat, this],
    simpa using push_rew_pull p (subterm.lift ∘ s) }

end pull

def msubst (t : subterm L m n) : subformula L (m + 1) n →ₗ subformula L m n :=
rew (t *> metavar)

section msubst
variables (u : subterm L m n)

@[simp] lemma msubst_relation {p} (r : L.pr p) (v) :
  msubst u (relation r v) = relation r (subterm.msubst u ∘ v) := by simp[msubst, subterm.msubst]

@[simp] lemma msubst_equal (t₁ t₂ : subterm L (m + 1) n) :
  msubst u (t₁ =' t₂) = (u.msubst t₁ =' u.msubst t₂) := by simp[msubst, subterm.msubst]

@[simp] lemma msubst_fal (p : subformula L (m + 1) (n + 1)) :
  msubst u (∀'p) = ∀'msubst u.lift p :=
by simp[msubst]; refine eq_rew_of_eq (funext $ λ x, by rcases (fin.eq_zero_or_eq_succ x) with (rfl | ⟨x, rfl⟩); simp)

@[simp] lemma msubst_ex (p : subformula L (m + 1) (n + 1)) :
  msubst u (∃'p) = ∃'msubst u.lift p := by simp[ex_def]

@[simp] lemma msubst_mlift (u : subterm L m n) (p : subformula L m n) :
  msubst u p.mlift = p :=
by simp[mlift_eq_rew, msubst, nested_rew]; refine rew_eq_self_of_eq (funext $ by simp) _

lemma mlift_msubst (u : subterm L m n) (p : subformula L (m + 1) n) :
  mlift (msubst u p) = rew (u.mlift *> (subterm.mlift ∘ metavar)) p :=
by simp[msubst, mlift_rew]; refine eq_rew_of_eq (funext $ λ x, by rcases (fin.eq_zero_or_eq_succ x) with (rfl | ⟨x, rfl⟩); simp)

end msubst

def subst (u : subterm L m n) : subformula L m (n + 1) →ₗ subformula L m n := (msubst u).comp push

section subst
variables (u : subterm L m n)

@[simp] lemma subst_relation {p} (r : L.pr p) (v) :
  subst u (relation r v) = relation r (subterm.subst u ∘ v) := by simp[subst, subterm.subst, subterm.msubst]

@[simp] lemma subst_equal (t₁ t₂ : subterm L m (n + 1)) :
  subst u (t₁ =' t₂) = (u.subst t₁ =' u.subst t₂) := by simp[subst, subterm.subst, subterm.msubst]

@[simp] lemma subst_fal (p : subformula L m n.succ.succ) :
  subst u (∀'p) = ∀'subst u.lift p :=
by simp[subst]; refine eq_rew_of_eq (funext $ λ x, by rcases (fin.eq_zero_or_eq_succ x) with (rfl | ⟨x, rfl⟩); simp)

@[simp] lemma subst_ex (p : subformula L m n.succ.succ) :
  subst u (∃'p) = ∃'subst u.lift p := by simp[ex_def]

lemma mlift_subst : ∀ {m n} (u : subterm L m n) (p : subformula L m (n + 1)),
  (subst u p).mlift = subst u.mlift p.mlift
| m n u verum          := by simp[top_eq]
| m n u (relation p v) := by simp; funext x; simp[subterm.mlift_subst]
| m n u (equal t₁ t₂)  := by simp[equal_eq]
| m n u (imply p q)    := by simp[imply_eq]; exact ⟨mlift_subst u p, mlift_subst u q⟩
| m n u (neg p)        := by simp[neg_eq]; exact mlift_subst u p
| m n u (fal p)        := by simp[fal_eq, subterm.mlift_lift]; exact mlift_subst u.lift p
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.2.2.complexity)⟩]}

end subst

lemma pull_msubst_push_mlift : ∀ {n} (p : subformula L m (n + 1)), (pull $ msubst &0 $ push $ mlift p) = p
| n verum          := by simp[top_eq]
| n (relation r v) := by simp; funext i; exact subterm.pull_msubst_push_mlift _
| n (equal t u)    := by simp[equal_eq]
| n (imply p q)    := by simp[imply_eq]; exact ⟨pull_msubst_push_mlift p, pull_msubst_push_mlift q⟩
| n (neg p)        := by simp[neg_eq]; exact pull_msubst_push_mlift p
| n (fal p)        := by simp[fal_eq]; exact pull_msubst_push_mlift p
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.complexity)⟩]}

@[simp] lemma subst_mlift (p : subformula L m (n + 1)) : subst &0 (mlift p) = push p :=
by { suffices : (subst &0 $ mlift p) = (push $ pull $ msubst &0 $ push $ mlift p),
     by simpa[pull_msubst_push_mlift] using this,
     simp only [push_pull], refl }

def dummy : subformula L m n →ₗ subformula L m (n + 1) := pull.comp mlift

section dummy

@[simp] lemma dummy_relation {p} (r : L.pr p) (v : finitary (subterm L m n) p) :
  dummy (relation r v) = relation r (subterm.dummy ∘ v) := by simp[dummy, subterm.dummy]

@[simp] lemma dummy_equal (t u : subterm L m n) :
  dummy (t =' u : subformula L m n) = (t.dummy =' u.dummy) := by simp[dummy, subterm.dummy]

@[simp] lemma dummy_fal (p : subformula L m (n + 1)) : dummy (∀'p) = ∀'(dummy p) := by simp[dummy]

@[simp] lemma dummy_ex (p : subformula L m (n + 1)) : dummy (∃'p) = ∃'(dummy p) := by simp[dummy]

@[simp] lemma push_dummy  (p : subformula L m n) : push (dummy p) = mlift p := by simp[dummy]

end dummy

def qr {m} : Π {n}, subformula L m n → ℕ
| n verum          := 0
| n (relation r v) := 0
| n (equal t u)    := 0
| n (imply p q)    := max p.qr q.qr
| n (neg p)        := p.qr
| n (fal p)        := p.qr + 1

def is_open {m n} (p : subformula L m n) : Prop := p.qr = 0

section qr
open subformula
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

@[simp] def qr_push {m} : Π {n} (p : subformula L m (n + 1)), p.push.qr = p.qr
| n verum          := by simp[top_eq]
| n (relation p v) := by simp
| n (equal t u)    := by simp[equal_eq]
| n (imply p q)    := by simp[imply_eq, qr_push p, qr_push q]
| n (neg p)        := by simp[neg_eq, qr_push p]
| n (fal p)        := by simp[fal_eq, qr_push p]
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.complexity)⟩]}

@[simp] def qr_pull {m} : Π {n} (p : subformula L (m + 1) n), p.pull.qr = p.qr
| n verum          := by simp[top_eq]
| n (relation p v) := by simp
| n (equal t u)    := by simp[equal_eq]
| n (imply p q)    := by simp[imply_eq, qr_pull p, qr_pull q]
| n (neg p)        := by simp[neg_eq, qr_pull p]
| n (fal p)        := by simp[fal_eq, qr_pull p]

lemma top_open : (⊤ : subformula L m n).is_open := by simp[is_open] 

@[simp] lemma relation_open {k} (r : L.pr k) (v) : (relation r v : subformula L m n).is_open := by simp[is_open]

@[simp] lemma equal_open {t u : subterm L m n} : (t =' u : subformula L m n).is_open := by simp[is_open] 

@[simp] lemma imply_open {p q : subformula L m n} : (p ⟶ q).is_open ↔ p.is_open ∧ q.is_open := by simp[is_open] 

@[simp] lemma and_open {p q : subformula L m n} : (p ⊓ q).is_open ↔ p.is_open ∧ q.is_open := by simp[is_open] 

@[simp] lemma or_open {p q : subformula L m n} : (p ⊔ q).is_open ↔ p.is_open ∧ q.is_open := by simp[is_open] 

@[simp] lemma neg_open {p : subformula L m n} : (∼p).is_open ↔ p.is_open := by simp[is_open] 

@[simp] lemma fal_not_open {p : subformula L m (n + 1)} : ¬(∀'p).is_open := by simp[is_open] 

@[simp] lemma ex_not_open {p : subformula L m (n + 1)} : ¬(∃'p).is_open := by simp[is_open] 

end qr

end subformula

namespace preTheory
variables {L} {m : ℕ} (T U : preTheory L m)

def mlift : preTheory L (m + 1) := subformula.mlift '' T

variables {T U}

@[simp] lemma mlift_insert (p : formula L m) : (insert p T).mlift = insert p.mlift T.mlift :=
by simp[mlift, set.image_insert_eq]

@[simp] lemma mlift_mem_mlift_iff {p : formula L m} : p.mlift ∈ T.mlift ↔ p ∈ T :=
function.injective.mem_set_image subformula.mlift_inj

lemma mem_mlift_iff {p} :
  p ∈ T.mlift ↔ ∃ q ∈ T, subformula.mlift q = p :=
by simp[mlift]

end preTheory

def s : subformula language.empty 1 0 := (&0 =' &0) ⟶ ∀'((#0 =' &0) ⟶ ∀'((#0 =' #1) ⟶ (#0 =' &0)))

#eval to_string s
#eval to_string s.mlift
#eval to_string s.pull.mlift.push

end fol