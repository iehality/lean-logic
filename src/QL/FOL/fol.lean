import lib.lib tactic data.set_like.basic logic translation

universe u

namespace fol
open_locale logic_symbol

structure language : Type (u+1) :=
(fn : ℕ → Type u)
(pr : ℕ → Type u)

namespace language
variables (L : language.{u})

protected def empty : language.{u} :=
{ fn := λ _, pempty, pr := λ _, pempty }

instance (n) : is_empty (language.empty.fn n) := ⟨by rintros ⟨⟩⟩

instance (n) : is_empty (language.empty.pr n) := ⟨by rintros ⟨⟩⟩

instance (n) : has_to_string (language.empty.fn n) := ⟨by rintros ⟨⟩⟩

instance (n) : has_to_string (language.empty.pr n) := ⟨by rintros ⟨⟩⟩

class has_equal (L : language) := (eq : L.pr 2)

end language

variables (L : language.{u})

inductive subterm (n : ℕ) : Type u
| metavar {} : ℕ → subterm
| var     {} : fin n → subterm
| function   : ∀ {p}, L.fn p → (fin p → subterm) → subterm

@[reducible] def term := subterm L 0

variables {L}

namespace subterm
variables {n : ℕ}

prefix `#`:max := subterm.var
prefix `&`:max := subterm.metavar

def term.const (f : L.fn 0) : subterm L n := function f finitary.nil

instance : inhabited (subterm L n) := ⟨&default⟩

variables (L) (n)

def to_string [∀ n, has_to_string (L.fn n)] : subterm L n → string
| &n                            := "&" ++ has_to_string.to_string n
| #n                            := "#" ++ has_to_string.to_string n
| (@function _ _ 0 c v)       := "⟨" ++ has_to_string.to_string c ++ "⟩"
| (@function _ _ (n + 1) c v) :=
    "⟨" ++ has_to_string.to_string c ++ "⟩" ++ @has_to_string.to_string (finitary _ _) _ (λ i, to_string (v i))

instance [∀ n, has_to_string (L.fn n)] : has_to_string (subterm L n) := ⟨to_string L n⟩

end subterm

variables (L)
inductive subformula : ℕ → Type u
| verum    {n} : subformula n
| relation {n} : ∀ {p}, L.pr p → (fin p → subterm L n) → subformula n
| imply    {n} : subformula n → subformula n → subformula n
| neg      {n} : subformula n → subformula n
| fal      {n} : subformula (n + 1) → subformula n

attribute [pattern]  has_negation.neg has_arrow.arrow has_univ_quantifier.univ has_exists_quantifier.ex

@[reducible] def formula := subformula L 0

-- @[reducible] def sentence := formula L 0

namespace subformula
variables {L} {m n : ℕ}

def to_str [∀ n, has_to_string (L.fn n)] [∀ n, has_to_string (L.pr n)] : Π {n}, subformula L n → string
| n verum          := "⊤"
| n (relation p v) := has_to_string.to_string p
| n (imply p q)    := "(" ++ to_str p ++ " → " ++ to_str q ++ ")"
| n (neg p)        := "¬" ++ to_str p
| n (fal p)        := "∀" ++ to_str p

instance [∀ n, has_to_string (L.fn n)] [∀ n, has_to_string (L.pr n)] : has_to_string (subformula L n) := ⟨to_str⟩

def and (p : subformula L n) (q : subformula L n) : subformula L n := (p.imply q.neg).neg

def or (p : subformula L n) (q : subformula L n) : subformula L n := p.neg.imply q

def ex (p : subformula L (n + 1)) : subformula L n := p.neg.fal.neg

instance : has_logic_symbol (subformula L n) :=
{ bot := verum.neg,
  top := verum,
  sup := or,
  inf := and,
  arrow := imply,
  neg := neg }

instance : inhabited (subformula L n) := ⟨⊤⟩

def equal [L.has_equal] (t u : subterm L n) : subformula L n := relation language.has_equal.eq (t *> u *> fin.nil) 

instance [L.has_equal] : has_eq (subterm L n) (subformula L n) := ⟨equal⟩

instance : has_univ_quantifier' (subformula L) := ⟨@fal L⟩

instance : has_exists_quantifier' (subformula L) := ⟨@ex L⟩

lemma top_eq : @subformula.verum L n = (⊤) := rfl
lemma imply_eq : @subformula.imply L n = (⟶) := rfl
lemma equal_eq [L.has_equal] : @equal L n _ = (=') := rfl
lemma neg_eq : @subformula.neg L n = has_negation.neg := rfl
lemma fal_eq : @subformula.fal L n = has_univ_quantifier'.univ := rfl
lemma ex_eq : @subformula.ex L n = has_exists_quantifier'.ex := rfl

lemma ex_def (p : subformula L (n + 1)) : ∃'p = ∼∀'∼p := rfl

lemma bot_def : (⊥ : subformula L n) = ∼⊤ := rfl

@[simp] lemma equal.inj' [L.has_equal] (t₁ u₁ t₂ u₂ : subterm L n) : (t₁ =' t₂ : subformula L n) = (u₁ =' u₂) ↔ t₁ = u₁ ∧ t₂ = u₂ :=
⟨by simp[←equal_eq, equal]; intros h₁ h₂; exact ⟨h₁, h₂⟩, by simp; exact congr_arg2 (=')⟩

@[simp] lemma imply.inj' (p₁ q₁ p₂ q₂ : subformula L n) : p₁ ⟶ p₂ = q₁ ⟶ q₂ ↔ p₁ = q₁ ∧ p₂ = q₂ :=
⟨imply.inj, by simp; exact congr_arg2 (⟶)⟩

@[simp] lemma neg.inj' (p q : subformula L n) : ∼p = ∼q ↔ p = q := ⟨neg.inj, congr_arg _⟩

@[simp] lemma and.inj' (p₁ q₁ p₂ q₂ : subformula L n) : p₁ ⊓ p₂ = q₁ ⊓ q₂ ↔ p₁ = q₁ ∧ p₂ = q₂ :=
by simp[has_inf.inf, and]

@[simp] lemma or.inj' (p₁ q₁ p₂ q₂ : subformula L n) : p₁ ⊔ p₂ = q₁ ⊔ q₂ ↔ p₁ = q₁ ∧ p₂ = q₂ :=
by simp[has_sup.sup, or]

@[simp] lemma fal.inj' (p q : subformula L (n + 1)) : (∀'p : subformula L n) = ∀'q ↔ p = q := ⟨fal.inj, congr_arg _⟩

@[simp] lemma ex.inj' (p q : subformula L (n + 1)) : (∃'p : subformula L n) = ∃'q ↔ p = q := 
by simp[has_exists_quantifier'.ex, ex]

section ne
variables {k : ℕ} (r : L.pr k) (v : finitary (subterm L n) k) (t u : subterm L n)
  (p p₁ p₂ : subformula L n) (q : subformula L (n + 1))

@[simp] lemma verum_ne_predicate : ⊤ ≠ relation r v.
@[simp] lemma verum_ne_imply : ⊤ ≠ (p₁ ⟶ p₂).
@[simp] lemma verum_ne_neg : ⊤ ≠ ∼p.
@[simp] lemma verum_ne_fal : ⊤ ≠ ∀'q.
@[simp] lemma predicate_ne_verum : relation r v ≠ ⊤.
@[simp] lemma predicate_ne_imply : relation r v ≠ p₁ ⟶ p₂.
@[simp] lemma predicate_ne_neg : relation r v ≠ ∼p.
@[simp] lemma predicate_ne_fal : relation r v ≠ ∀'q.
@[simp] lemma imply_ne_verum : p₁ ⟶ p₂ ≠ ⊤.
@[simp] lemma imply_ne_relation : p₁ ⟶ p₂ ≠ relation r v.
@[simp] lemma imply_ne_neg : p₁ ⟶ p₂ ≠ ∼p.
@[simp] lemma imply_ne_fal : p₁ ⟶ p₂ ≠ ∀'q.
@[simp] lemma neg_ne_verum : ∼p ≠ ⊤.
@[simp] lemma neg_ne_relation : ∼p ≠ relation r v.
@[simp] lemma neg_ne_imply : ∼p ≠ p₁ ⟶ p₂.
@[simp] lemma neg_ne_fal : ∼p ≠ ∀'q.
@[simp] lemma fal_ne_verum : ∀'q ≠ ⊤.
@[simp] lemma fal_ne_relation : ∀'q ≠ relation r v.
@[simp] lemma fal_ne_imply : ∀'q ≠ p₁ ⟶ p₂.
@[simp] lemma fal_ne_neg : ∀'q ≠ ∼p.

end ne

end subformula

@[reducible] def preTheory (L : language.{u}) := logic.Theory (subformula L 0)

@[reducible] def Theory (L : language.{u}) := logic.Theory (subformula L 0)

namespace subterm

def const {n} (c : L.fn 0) : subterm L n := function c fin.nil

section rew
variables {L} {n : ℕ} {s : ℕ → subterm L n}

@[simp] def rew (s : ℕ → subterm L n) : subterm L n → subterm L n
| (&x)           := s x
| (#x)           := #x
| (function f v) := function f (λ i, (v i).rew)

section rew

lemma eq_rew_of_eq {t : subterm L n} {s₁ s₂ : ℕ → subterm L n} (h : s₁ = s₂) :
  rew s₁ t = rew s₂ t := by rw[h]

lemma nested_rew (s₀ : ℕ → subterm L n) (s₁ : ℕ → subterm L n) :
  ∀ t, rew s₁ (rew s₀ t) = rew (rew s₁ ∘ s₀) t
| (&x)           := by simp
| (#x)           := by simp
| (function f v) := by simp; funext i; exact nested_rew (v i)

@[simp] lemma rew_metavar (t : subterm L n) : rew metavar t = t :=
by induction t; simp*

end rew

def mlift' : subterm L n → subterm L n := rew (metavar ∘ nat.succ)

@[simp] def lift : subterm L n → subterm L (n + 1)
| (#x)           := #x.succ
| (&x)           := &x
| (function f v) := function f (λ i, (v i).lift)

section lift

lemma lift_rew (s : ℕ → subterm L n) (t : subterm L n) : (t.rew s).lift = t.lift.rew (lift ∘ s) :=
by induction t with x x p f v IH; simp; exact funext IH

@[simp] lemma lift_metavar : lift ∘ (metavar : ℕ → subterm L n) = metavar :=
funext (by simp)

end lift

@[simp] def mlift : subterm L n → subterm L n
| (&x)           := &x.succ
| (#x)           := #x
| (function f v) := function f (λ i, (v i).mlift)

section mlift

lemma mlift_eq_rew : @mlift L n = rew (metavar ∘ nat.succ) :=
funext (λ t, by induction t; simp*)

lemma mlift_rew (s : ℕ → subterm L n) (t : subterm L n) : (t.rew s).mlift = t.rew (mlift ∘ s) :=
by induction t with x x p f v IH; simp; exact funext IH

lemma mlift_lift (t : subterm L n) : t.mlift.lift = t.lift.mlift :=
by induction t; simp*

lemma mlift_inj : function.injective (@mlift L n)
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

def push : subterm L (n + 1) → subterm L n
| (&x)           := &x.succ
| (#x)           := (var <* &0) x
| (function f v) := function f (λ i, (v i).push)

section push

@[simp] lemma push_metavar (x) : (&x : subterm L (n + 1)).push = &x.succ := rfl

@[simp] lemma push_var_last : (#(fin.last n) : subterm L (n + 1)).push = &0 := by simp[push]

@[simp] lemma push_var_cast (x) : (#(fin.cast_succ x) : subterm L (n + 1)).push = #x := by simp[push]

@[simp] lemma push_function {p} (f : L.fn p) (v : fin p → subterm L (n + 1)) :
  (function f v : subterm L (n + 1)).push = function f (push ∘ v) := by simp[push]

lemma push_lift_comm (t : subterm L (n + 1)) : t.lift.push = t.push.lift :=
by { induction t; simp*,
     case var : x { refine fin.last_cases _ _ x; simp[fin.succ_cast_succ] },
     case function : k f v IH
     { funext i, exact IH i } }

end push

def pull : subterm L n → subterm L (n + 1)
| (&x)           := (#(fin.last n) .> metavar) x
| (#x)           := #x.cast_succ
| (function f v) := function f (λ i, (v i).pull)

section pull

@[simp] lemma pull_metavar_zero : (&0 : subterm L n).pull = #(fin.last n) := rfl

@[simp] lemma pull_metavar_succ (x : ℕ) : (&x.succ : subterm L n).pull = &x := by simp[pull]

@[simp] lemma pull_var (x) : (#x : subterm L n).pull = #x.cast_succ := by simp[pull]

@[simp] lemma pull_function {p} (f : L.fn p) (v : fin p → subterm L n) :
  (function f v : subterm L n).pull = function f (pull ∘ v) := by simp[pull]

@[simp] lemma pull_push (t : subterm L (n + 1)) : t.push.pull = t :=
by{ induction t, 
    case metavar : x { simp },
    case var : x { refine fin.last_cases _ _ x; simp },
    case function : p f v IH { simp, funext x, simp[IH] } }

@[simp] lemma push_pull (t : subterm L n) : t.pull.push = t :=
by{ induction t,
    case metavar : x { cases x; simp },
    case var : x { simp },
    case function : p f v IH { simp, funext x, simp[IH] } }

lemma push_rew_pull (t : subterm L n) (s : ℕ → subterm L (n + 1)) :
  (rew s t.pull).push = rew (&0 .> (push ∘ s)) t :=
by { induction t; simp*,
      case metavar : x { cases x; simp },
      case function : k f v IH
      { funext i, exact IH i } }

lemma pull_lift_comm (t : subterm L n) : t.lift.pull = t.pull.lift :=
by { induction t; simp[*, fin.succ_cast_succ],
     case metavar : x { cases x; simp },
     case function : k f v IH
     { funext i, exact IH i } }

end pull

/-
  #0 #1 ... #(n-1) &0 &1 ... &m
            ↓msubst u
  #0 #1 ... #(n-1) u  &0 ... &(m-1)
-/

def msubst (t : subterm L n) : subterm L n → subterm L n := rew (t .> metavar)

section msubst

@[simp] lemma msubst_var (u : subterm L n) (x) : msubst u #x = #x := by simp[msubst]

@[simp] lemma msubst_metavar_zero (u : subterm L n) : msubst u &0 = u := by simp[msubst]

@[simp] lemma msubst_metavar_succ (u : subterm L n) (x : ℕ) : msubst u &x.succ = &x := by simp[msubst]

@[simp] lemma msubst_function (u : subterm L n) {p} (f : L.fn p) (v) :
  msubst u (function f v) = function f (msubst u ∘ v) := by simp[msubst]

@[simp] lemma msubst_mlift (t u : subterm L n) : msubst u t.mlift = t :=
by { induction t; simp*, case function : k f v IH { funext i, simp, exact IH i } }

end msubst

/-
  #0 #1 ... #(n-1) #n &0 &1 ... &(m-1)
            ↓subst u
  #0 #1 ... #(n-1) u  &0 &1 ... &(m-1)
-/

def subst (t : subterm L n) : subterm L (n + 1) → subterm L n := msubst t ∘ push

section subst

@[simp] lemma subst_var_cast_succ (u : subterm L n) (x : fin n) : subst u #x.cast_succ = #x := by simp[subst]

@[simp] lemma subst_var_last (u : subterm L n) : subst u #(fin.last n) = u := by simp[subst]

@[simp] lemma subst_var_last_zero (u : subterm L 0) : subst u #0 = u :=
by rw[show 0 = fin.last 0, by simp]; exact subst_var_last u

@[simp] lemma subst_metavar (u : subterm L n) (x) : subst u &x = &x := by simp[subst]

@[simp] lemma subst_function (u : subterm L n) {p} (f : L.fn p) (v) :
  subst u (function f v) = function f (subst u ∘ v) := by simp[subst]

@[simp] lemma mlift_subst (u : subterm L n) (t : subterm L (n + 1)) :
  (subst u t).mlift = subst u.mlift t.mlift :=
by { induction t; simp*, case var : x { refine fin.last_cases _ _ x; simp } }

lemma msubst_push (u : subterm L n) (t : subterm L (n + 1)) : msubst u (push t) = subst u t := rfl

@[simp] lemma subst_zero (u : subterm L 0) (t : subterm L 0) : subst u t.lift = t :=
by { induction t; simp*,
     case var : i { exact fin_zero_elim i },
     case function : k f v IH { funext i, simp[IH] } }

@[simp] lemma subst_lift_lift (u : subterm L n) (t : subterm L (n + 1)) : subst u.lift t.lift = (subst u t).lift :=
by { induction t; simp*,
     case var : i { refine fin.last_cases _ _ i; simp[fin.succ_cast_succ], },
     case function : k f v IH { funext i, simp[IH] } }

end subst

def dummy : subterm L n → subterm L (n + 1) := pull ∘ mlift

section dummy

@[simp] lemma dummy_metavar (x) : dummy (&x : subterm L n) = &x := by simp[dummy]

@[simp] lemma dummy_var (x) : dummy (#x : subterm L n) = #x.cast_succ := by simp[dummy]

@[simp] lemma dummy_function {p} (f : L.fn p) (v : finitary (subterm L n) p) :
  dummy (function f v) = function f (dummy ∘ v) := by simp[dummy]

end dummy

@[simp] lemma pull_msubst_push_mlift (t : subterm L (n + 1)) : (pull $ msubst &0 $ push $ mlift t) = t :=
begin
  induction t; simp, 
  case var : x { refine fin.last_cases _ _ x; simp },
  case function : k f v IH
  { funext i, simpa using IH i }
end

@[simp] lemma pull_mlift (t : subterm L n) (u) : (subst u $ pull $ mlift t) = t :=
by simp[subst]

@[simp] lemma dummy_subst (u : subterm L n) (t : subterm L n) :
  subst u t.dummy = t :=
by simp[dummy]

lemma dummy_lift_comm (t : subterm L n) :
  t.lift.dummy = t.dummy.lift :=
by simp[dummy, ←mlift_lift, pull_lift_comm]

--@[simp] def dummys : subterm L 0 → Π {n}, subterm L n 
--| t 0 := t
--| t (n + 1) := dummy (dummys t)

def substs : Π {n}, (fin n → subterm L 0) → subterm L n → subterm L 0
| 0       w t := t
| (n + 1) w t := subst (w $ fin.last n) (substs (mlift ∘ w ∘ fin.cast_succ) t.push).pull

@[simp] lemma substs_zero (w : fin 0 → subterm L 0) : substs w = id := by funext i; simp[substs]

@[simp] lemma substs_function (w : fin n → subterm L 0) {k} (f : L.fn k) (v) :
  substs w (function f v) = function f (substs w ∘ v) :=
by { induction n with n IH, { simp },
     { simp[substs, IH], funext i, { simp, refl } } }

@[simp] lemma substs_metavar (w : fin n → subterm L 0) (x) :
  substs w &x = &x :=
by induction n with n IH generalizing x; simp[substs, *]

@[simp] lemma substs_var (w : fin n → subterm L 0) (x) :
  substs w #x = w x :=
by { induction n with n IH generalizing x; simp[substs],
     { exfalso, exact fin_zero_elim x },
     { refine fin.last_cases _ _ x; simp* } }

end rew

section symbol
variables {m n : ℕ}

def symbol : subterm L n → set (Σ k, L.fn k)
| &x             := ∅
| #x             := ∅
| (function f v) := insert ⟨_, f⟩ (⋃ i, symbol (v i))

end symbol

end subterm

namespace subformula
open subterm finitary
variables {L} {n : ℕ}

@[simp] def complexity : Π {n}, subformula L n → ℕ
| n verum          := 0
| n (relation p v) := 0
| n (imply p q)    := max p.complexity q.complexity + 1
| n (neg p)        := p.complexity + 1
| n (fal p)        := p.complexity + 1

@[simp] lemma complexity_top : (⊤ : subformula L n).complexity = 0 := by refl

@[simp] lemma complexity_neg (p : subformula L n) : (∼p).complexity = p.complexity + 1 := by refl

@[simp] lemma complexity_fal (p : subformula L (n + 1)) : (∀'p).complexity = p.complexity + 1 := by refl

@[simp] lemma imply_complexity (p q : subformula L n) : (p ⟶ q).complexity = max p.complexity q.complexity + 1 := by refl

def rew'  : Π {n}, (ℕ → subterm L n) → subformula L n → subformula L n
| n s verum          := ⊤
| n s (relation p v) := relation p (λ i, (v i).rew s)
| n s (imply p q)    := p.rew' s ⟶ q.rew' s
| n s (neg p)        := ∼p.rew' s
| n s (fal p)        := ∀'p.rew' (subterm.lift ∘ s)

def rew (s : ℕ → subterm L n) : subformula L n →ₗ subformula L n :=
{ to_fun := rew' s,
  map_neg' := λ p, by refl,
  map_imply' := λ p q, by refl,
  map_and' := λ p q, by refl,
  map_or' := λ p q, by refl,
  map_top' := by refl,
  map_bot' := by refl }

section rew
variables (s : ℕ → subterm L n)

lemma rew_def (p : subformula L n) : rew s p = rew' s p := rfl

variables {s}

@[simp] lemma rew_relation {p} (r : L.pr p) (v) :
  rew s (relation r v) = relation r (subterm.rew s ∘ v) := rfl

@[simp] lemma rew_equal [L.has_equal] (t u : subterm L n) :
  rew s (t =' u) = (t.rew s =' u.rew s) := by simp[←equal_eq, equal, fin.comp_left_concat]

@[simp] lemma rew_fal (p : subformula L (n + 1)) :
  rew s (∀'p) = ∀'rew (subterm.lift ∘ s) p := rfl

@[simp] lemma rew_ex (p : subformula L (n + 1)) :
  rew s (∃'p) = ∃'rew (subterm.lift ∘ s) p := by simp[ex_def]

lemma rew_eq_self_of_eq {s : ℕ → subterm L n} (h : s = metavar) (p : subformula L n) : rew s p = p :=
by { induction p; simp[top_eq, equal_eq, imply_eq, neg_eq, fal_eq, subterm.mlift_rew, *],
     case relation : n p r v { funext x; simp } }

@[simp] lemma rew_metavar (p : subformula L n) : rew metavar p = p := rew_eq_self_of_eq rfl p

lemma nested_rew : ∀ {n} (p : subformula L n) (s₀ : ℕ → subterm L n) (s₁ : ℕ → subterm L n),
  rew s₁ (rew s₀ p) = rew (subterm.rew s₁ ∘ s₀) p
| n verum          s₀ s₁ := by simp[top_eq]
| n (relation p v) s₀ s₁ := by simp; funext; simp[subterm.nested_rew]
| n (imply p q)    s₀ s₁ := by simp[imply_eq, nested_rew p, nested_rew q]
| n (neg p)        s₀ s₁ := by simp[neg_eq, nested_rew p]
| n (fal p)        s₀ s₁ := by simp[fal_eq, nested_rew p]; { 
  have : subterm.rew (subterm.lift ∘ s₁) ∘ subterm.lift ∘ s₀ = subterm.lift ∘ subterm.rew s₁ ∘ s₀,
  { funext i; simp[lift_rew] },
  rw this }

lemma eq_rew_of_eq {p : subformula L n} {s₁ s₂ : ℕ → subterm L n} (h : s₁ = s₂) :
  rew s₁ p = rew s₂ p := by rw[h]

@[simp] lemma complexity_rew (p : subformula L n) : complexity (rew s p) = complexity p :=
by induction p; simp[top_eq, equal_eq, imply_eq, neg_eq, fal_eq, *]

end rew

def mlift' : Π {n}, subformula L n → subformula L n
| n verum          := ⊤
| n (relation p v) := relation p (mlift ∘ v)
| n (imply p q)    := p.mlift' ⟶ q.mlift'
| n (neg p)        := ∼p.mlift'
| n (fal p)        := ∀'p.mlift'

def mlift : subformula L n →ₗ subformula L n :=
{ to_fun := mlift',
  map_neg' := λ p, by refl,
  map_imply' := λ p q, by refl,
  map_and' := λ p q, by refl,
  map_or' := λ p q, by refl,
  map_top' := by refl,
  map_bot' := by refl }

section mlift

@[simp] lemma mlift_relation {p} (r : L.pr p) (v : finitary (subterm L n) p) :
  mlift (relation r v) = relation r (subterm.mlift ∘ v) := rfl

@[simp] lemma mlift_equal [L.has_equal] (t u : subterm L n) :
  mlift (t =' u : subformula L n) = (t.mlift =' u.mlift) :=
by simp[←equal_eq, equal, fin.comp_left_concat]

@[simp] lemma mlift_fal (p : subformula L (n + 1)) :
  mlift (∀'p) = ∀'mlift p := rfl

@[simp] lemma mlift_ex (p : subformula L (n + 1)) :
  mlift (∃'p) = ∃'mlift p := by simp[ex_def]

@[simp] lemma mlift_univ_closure (p : subformula L n) :
  mlift (∀'*p) = ∀'* (mlift p) :=
by induction n; simp*

@[simp] lemma mlift_ex_closure (p : subformula L n) :
  mlift (∃'*p) = ∃'*(mlift p) :=
by induction n; simp*

variables (s : ℕ → subterm L n)

lemma mlift_rew (p : subformula L n) : mlift (rew s p) = rew (subterm.mlift ∘ s) p :=
begin
  induction p; simp[top_eq, equal_eq, imply_eq, neg_eq, fal_eq, subterm.mlift_rew, *],
  case relation : n p r v { funext x; simp[subterm.mlift_rew] },
  case fal : n p IH {
    have : subterm.mlift ∘ subterm.lift ∘ s = subterm.lift ∘ subterm.mlift ∘ s,
    { funext x; simp[subterm.mlift_lift] },
    rw[this] }
end

lemma mlift_eq_rew : @mlift L n = rew (metavar ∘ nat.succ) :=
by { ext p, induction p; simp[top_eq, equal_eq, imply_eq, neg_eq, fal_eq, subterm.mlift_eq_rew, *],
     exact eq_rew_of_eq (funext $ λ x, by simp) }

lemma mlift_inj : function.injective (@mlift L n) := λ p q,
begin
  induction p,
  case verum { cases q; simp[top_eq, equal_eq, imply_eq, neg_eq, fal_eq] },
  case relation : n k r v₁
  { cases q; simp[top_eq, equal_eq, imply_eq, neg_eq, fal_eq];
    case relation : _ _ r₂ v₂
    { rintros rfl rfl, simp, intros h, funext i, exact @subterm.mlift_inj _ _ (v₁ i) (v₂ i) (congr_fun h i) } },
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

@[simp] lemma complexity_mlift (p : subformula L n) : p.mlift.complexity = p.complexity :=
by induction p; simp[top_eq, equal_eq, imply_eq, neg_eq, fal_eq, *]

end mlift

def succ_rec {C : Π n, subformula L (n + 1) → Sort*}
  (hverum : Π {n : ℕ}, C n ⊤)
  (hrelation : Π {n l : ℕ} (r : L.pr l) (v : fin l → subterm L (n + 1)), C n (relation r v))
  (himply : Π {n : ℕ} (p q : subformula L (n + 1)), C n p → C n q → C n (p ⟶ q))
  (hneg : Π {n : ℕ} (p : subformula L (n + 1)), C n p → C n ∼p)
  (hfal : Π {n : ℕ} (p : subformula L (n + 1 + 1)), C (n + 1) p → C n (∀'p)) :
  Π {n : ℕ} (p : subformula L (n + 1)), C n p
| n verum := hverum
| n (relation r v) := hrelation r v
| n (imply p q)    := himply p q (succ_rec p) (succ_rec q)
| n (neg p)        := hneg p (succ_rec p)
| n (fal p)        := hfal p (succ_rec p)
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.complexity)⟩]}

def push' : Π {n}, subformula L (n + 1) → subformula L n
| n verum          := ⊤
| n (relation p v) := relation p (subterm.push ∘ v)
| n (imply p q)    := p.push' ⟶ q.push'
| n (neg p)        := ∼p.push'
| n (fal p)        := ∀'p.push'
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.complexity)⟩]}

def push : subformula L (n + 1) →ₗ subformula L n :=
{ to_fun := push',
  map_neg' := λ p, by unfold has_negation.neg; simp[push']; refl,
  map_imply' := λ p q, by unfold has_arrow.arrow; simp[push']; refl,
  map_and' := λ p q, by unfold has_inf.inf; simp[and, push']; refl,
  map_or' := λ p q, by unfold has_sup.sup; simp[or, push']; refl,
  map_top' := by unfold has_top.top; simp[push']; refl,
  map_bot' := by unfold has_bot.bot; simp[push']; refl }

section push

lemma push_def (p : subformula L (n + 1)) : push p = push' p := rfl

@[simp] lemma push_relation {p} (r : L.pr p) (v : finitary (subterm L (n + 1)) p) :
  push (relation r v) = relation r (subterm.push ∘ v) := by simp[push_def, push']

@[simp] lemma push_equal [L.has_equal] (t u : subterm L (n + 1)) :
  push (t =' u : subformula L (n + 1)) = (t.push =' u.push) := by simp[←equal_eq, equal, fin.comp_left_concat]

@[simp] lemma push_fal (p : subformula L (n + 1 + 1)) :
  push (∀'p) = ∀'push p := by unfold has_univ_quantifier'.univ; simp[push_def, push']; refl

@[simp] lemma push_ex (p : subformula L (n + 1 + 1)) :
  push (∃'p) = ∃'push p := by simp[ex_def]

@[simp] lemma complexity_push : ∀ {n} (p : subformula L (n + 1)), p.push.complexity = p.complexity :=
by apply succ_rec; intros; simp[top_eq, equal_eq, imply_eq, neg_eq, fal_eq, *]

end push

def pull' : Π {n}, subformula L n → subformula L (n + 1)
| n verum          := ⊤
| n (relation p v) := relation p (subterm.pull ∘ v)
| n (imply p q)    := p.pull' ⟶ q.pull'
| n (neg p)        := ∼p.pull'
| n (fal p)        := ∀'p.pull'

def pull : subformula L n →ₗ subformula L (n + 1) :=
{ to_fun := pull',
  map_neg' := λ p, by refl,
  map_imply' := λ p q, by refl,
  map_and' := λ p q, by refl,
  map_or' := λ p q, by refl,
  map_top' := by refl,
  map_bot' := by refl }

section pull

lemma pull_def (p : subformula L n) : pull p = pull' p := rfl

@[simp] lemma pull_relation {p} (r : L.pr p) (v : finitary (subterm L n) p) :
  pull (relation r v) = relation r (subterm.pull ∘ v) := by refl

@[simp] lemma pull_equal [L.has_equal] (t u : subterm L n) :
  pull (t =' u : subformula L n) = (t.pull =' u.pull) := by simp[←equal_eq, equal, fin.comp_left_concat]

@[simp] lemma pull_fal (p : subformula L (n + 1)) :
  pull (∀'p) = ∀'pull p := by refl

@[simp] lemma pull_ex (p : subformula L (n + 1)) :
  pull (∃'p) = ∃'pull p := by simp[ex_def]

@[simp] lemma pull_push : ∀ {n} (p : subformula L (n + 1)), p.push.pull = p
| n verum          := by simp[top_eq]
| n (relation p v) := by simp; funext x; simp
| n (imply p q)    := by simp[imply_eq]; exact ⟨pull_push p, pull_push q⟩
| n (neg p)        := by simp[neg_eq]; exact pull_push p
| n (fal p)        := by simp[fal_eq]; exact pull_push p
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.complexity)⟩]}

@[simp] lemma push_pull : ∀ {n} (p : subformula L n), p.pull.push = p
| n verum          := by simp[top_eq]
| n (relation p v) := by simp; funext x; simp
| n (imply p q)    := by simp[imply_eq]; exact ⟨push_pull p, push_pull q⟩
| n (neg p)        := by simp[neg_eq]; exact push_pull p
| n (fal p)        := by simp[fal_eq]; exact push_pull p

lemma push_inj : function.injective (@push L n) :=
@function.left_inverse.injective _ _ (@pull L n) _ pull_push

lemma pull_inj : function.injective (@pull L n) :=
@function.left_inverse.injective _ _ (@push L n) _ push_pull

lemma push_rew_pull : ∀ {n} (p : subformula L n) (s : ℕ → subterm L (n + 1)),
  (rew s p.pull).push = rew (&0 .> (subterm.push ∘ s)) p
| n verum          s := by simp[top_eq]
| n (relation p v) s := by simp; funext x; simp[subterm.push_rew_pull]
| n (imply p q)    s := by simp[imply_eq]; exact ⟨push_rew_pull p s, push_rew_pull q s⟩
| n (neg p)        s := by simp[neg_eq]; exact push_rew_pull p s
| n (fal p)        s := by simp[fal_eq]; {
    have : subterm.lift ∘ subterm.push ∘ s = subterm.push ∘ subterm.lift ∘ s,
    { funext i; simp[subterm.push_lift_comm] },
    rw [nat.comp_left_concat, this],
    simpa using push_rew_pull p (subterm.lift ∘ s) }

@[simp] lemma complexity_pull (p : subformula L n) : p.pull.complexity = p.complexity :=
by induction p; intros; simp[top_eq, equal_eq, imply_eq, neg_eq, fal_eq, *]

end pull

lemma forall_comm (p : subformula L (n + 1)) : ∀'*(∀'p) = ∀'(pull $ ∀'* (push p)) :=
by induction n with n IH; simp*

lemma exists_comm (p : subformula L (n + 1)) : ∃'*(∃'p) = ∃'(pull $ ∃'* (push p)) :=
by induction n with n IH; simp*

def msubst (t : subterm L n) : subformula L n →ₗ subformula L n :=
rew (t .> metavar)

section msubst
variables (u : subterm L n)

@[simp] lemma msubst_relation {p} (r : L.pr p) (v) :
  msubst u (relation r v) = relation r (subterm.msubst u ∘ v) := by simp[msubst, subterm.msubst]

@[simp] lemma msubst_equal [L.has_equal] (t₁ t₂ : subterm L n) :
  msubst u (t₁ =' t₂) = (u.msubst t₁ =' u.msubst t₂) := by simp[←equal_eq, equal, fin.comp_left_concat]

@[simp] lemma msubst_fal (p : subformula L (n + 1)) :
  msubst u (∀'p) = ∀'msubst u.lift p :=
by simp[msubst]; refine eq_rew_of_eq (funext $ λ x, by rcases x; simp)

@[simp] lemma msubst_ex (p : subformula L (n + 1)) :
  msubst u (∃'p) = ∃'msubst u.lift p := by simp[ex_def]

@[simp] lemma msubst_mlift (u : subterm L n) (p : subformula L n) :
  msubst u p.mlift = p :=
by simp[mlift_eq_rew, msubst, nested_rew]; refine rew_eq_self_of_eq (funext $ by simp) _

lemma mlift_msubst (u : subterm L n) (p : subformula L n) :
  mlift (msubst u p) = rew (u.mlift .> subterm.mlift ∘ metavar) p :=
by simp[msubst, mlift_rew]; refine eq_rew_of_eq (funext $ λ x, by cases x; simp)

@[simp] lemma complexity_msubst (p : subformula L n) : (msubst u p).complexity = p.complexity :=
by simp[msubst]

end msubst

def subst (u : subterm L n) : subformula L (n + 1) →ₗ subformula L n := (msubst u).comp push

section subst
variables (u : subterm L n)

@[simp] lemma subst_relation {p} (r : L.pr p) (v) :
  subst u (relation r v) = relation r (subterm.subst u ∘ v) := by simp[subst, subterm.subst, subterm.msubst]

@[simp] lemma subst_equal [L.has_equal] (t₁ t₂ : subterm L (n + 1)) :
  subst u (t₁ =' t₂) = (u.subst t₁ =' u.subst t₂) := by simp[subst, subterm.subst, subterm.msubst]

@[simp] lemma subst_fal (p : subformula L n.succ.succ) :
  subst u (∀'p) = ∀'subst u.lift p :=
by simp[subst]

@[simp] lemma subst_ex (p : subformula L n.succ.succ) :
  subst u (∃'p) = ∃'subst u.lift p := by simp[ex_def]

lemma mlift_subst : ∀ {n} (u : subterm L n) (p : subformula L (n + 1)),
  (subst u p).mlift = subst u.mlift p.mlift
| n u verum          := by simp[top_eq]
| n u (relation p v) := by simp; funext x; simp[subterm.mlift_subst]
| n u (imply p q)    := by simp[imply_eq]; exact ⟨mlift_subst u p, mlift_subst u q⟩
| n u (neg p)        := by simp[neg_eq]; exact mlift_subst u p
| n u (fal p)        := by simp[fal_eq, subterm.mlift_lift]; exact mlift_subst u.lift p
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.2.complexity)⟩]}

@[simp] lemma subst_pull_mlift (p : subformula L n) (u) : (subst u $ pull $ mlift p) = p :=
by simp[subst]

@[simp] lemma complexity_subst (p : subformula L (n + 1)) : (subst u p).complexity = p.complexity :=
by simp[subst]

def substs : Π {n}, (fin n → subterm L 0) → subformula L n →ₗ subformula L 0
| 0       w := logic.homomorphism.id
| (n + 1) w := (subst (w $ fin.last n)).comp (pull.comp ((substs (subterm.mlift ∘ w ∘ fin.cast_succ)).comp push))

/-
def substs : Π {m n}, (fin n → subterm L 0) → subterm L n → subterm L 0
| m 0       w t := t
| m (n + 1) w t := msubst (w $ fin.last n) (substs (mlift ∘ w ∘ fin.cast_succ) t.push)

-/

@[simp] lemma substs_zero (v : fin 0 → subterm L 0) (p : subformula L 0) : substs v p = p := rfl

@[simp] lemma substs_relation (w : fin n → subterm L 0) {k} (r : L.pr k) (v : fin k → subterm L n) :
  substs w (relation r v) = relation r (subterm.substs w ∘ v) :=
by induction n with n IH; simp[substs, *]; funext i; refl

@[simp] lemma substs_equal [L.has_equal] (w : fin n → subterm L 0) (t u : subterm L n) :
  substs w (t =' u) = (subterm.substs w t =' subterm.substs w u) :=
by simp[←equal_eq, equal, fin.comp_left_concat]

end subst

lemma pull_msubst_push_mlift : ∀ {n} (p : subformula L (n + 1)), (pull $ msubst &0 $ push $ mlift p) = p
| n verum          := by simp[top_eq]
| n (relation r v) := by simp; funext i; exact subterm.pull_msubst_push_mlift _
| n (imply p q)    := by simp[imply_eq]; exact ⟨pull_msubst_push_mlift p, pull_msubst_push_mlift q⟩
| n (neg p)        := by simp[neg_eq]; exact pull_msubst_push_mlift p
| n (fal p)        := by simp[fal_eq]; exact pull_msubst_push_mlift p
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.complexity)⟩]}

-- lemma subst_inj (u) : function.injective (@subst L m n u)

@[simp] lemma subst_mlift (p : subformula L (n + 1)) : subst &0 (mlift p) = push p :=
by { suffices : (subst &0 $ mlift p) = (push $ pull $ msubst &0 $ push $ mlift p),
     by simpa[pull_msubst_push_mlift] using this,
     simp only [push_pull], refl }

def dummy : subformula L n →ₗ subformula L (n + 1) := pull.comp mlift

section dummy

@[simp] lemma dummy_relation {p} (r : L.pr p) (v : finitary (subterm L n) p) :
  dummy (relation r v) = relation r (subterm.dummy ∘ v) := by simp[dummy, subterm.dummy]

@[simp] lemma dummy_equal [L.has_equal] (t u : subterm L n) :
  dummy (t =' u : subformula L n) = (t.dummy =' u.dummy) := by simp[dummy, subterm.dummy]

@[simp] lemma dummy_fal (p : subformula L (n + 1)) : dummy (∀'p) = ∀'(dummy p) := by simp[dummy]

@[simp] lemma dummy_ex (p : subformula L (n + 1)) : dummy (∃'p) = ∃'(dummy p) := by simp[dummy]

@[simp] lemma push_dummy  (p : subformula L n) : push (dummy p) = mlift p := by simp[dummy]

@[simp] lemma dummy_subst (p : subformula L n) (t) : (subst t $ dummy p) = p :=
by simp[dummy, subst]

@[simp] lemma complexity_dummy (p : subformula L n) : p.dummy.complexity = p.complexity :=
by simp[dummy]

end dummy

def qr : Π {n}, subformula L n → ℕ
| n verum          := 0
| n (relation r v) := 0
| n (imply p q)    := max p.qr q.qr
| n (neg p)        := p.qr
| n (fal p)        := p.qr + 1

def is_open {n} (p : subformula L n) : Prop := p.qr = 0

section qr
open subformula
variables {n}

@[simp] lemma qr_top : (⊤ : subformula L n).qr = 0 := rfl

@[simp] lemma qr_bot : (⊥ : subformula L n).qr = 0 := rfl

@[simp] lemma qr_relation {p} (r : L.pr p) (v : finitary (subterm L n) p) : (relation r v).qr = 0 := rfl

@[simp] lemma qr_equal [L.has_equal] (t u : subterm L n) : (t =' u : subformula L n).qr = 0 := rfl

@[simp] lemma qr_imply (p q : subformula L n) : (p ⟶ q : subformula L n).qr = max p.qr q.qr := rfl

@[simp] lemma qr_and (p q : subformula L n) : (p ⊓ q : subformula L n).qr = max p.qr q.qr := rfl

@[simp] lemma qr_or (p q : subformula L n) : (p ⊔ q : subformula L n).qr = max p.qr q.qr := rfl

@[simp] lemma qr_iff (p q : subformula L n) : (p ⟷ q : subformula L n).qr = max p.qr q.qr := by simp[lrarrow_def, max_comm]

@[simp] lemma qr_neg (p : subformula L n) : (∼p).qr = p.qr := rfl

@[simp] lemma qr_fal (p : subformula L (n + 1)) : (∀'p).qr = p.qr + 1 := rfl

@[simp] lemma qr_ex (p : subformula L (n + 1)) : (∃'p).qr = p.qr + 1 := rfl

@[simp] lemma qr_rew : Π {n} (p : subformula L n) (s : ℕ → subterm L n), (rew s p).qr = p.qr
| n verum          := by simp[top_eq]
| n (relation p v) := by simp
| n (imply p q)    := by simp[imply_eq, qr_rew p, qr_rew q]
| n (neg p)        := by simp[neg_eq, qr_rew p]
| n (fal p)        := by simp[fal_eq, qr_rew p]

@[simp] lemma qr_msubst (u : subterm L n) (p : subformula L n) : (msubst u p).qr = p.qr :=
by simp[msubst]

@[simp] def qr_push : Π {n} (p : subformula L (n + 1)), p.push.qr = p.qr
| n verum          := by simp[top_eq]
| n (relation p v) := by simp
| n (imply p q)    := by simp[imply_eq, qr_push p, qr_push q]
| n (neg p)        := by simp[neg_eq, qr_push p]
| n (fal p)        := by simp[fal_eq, qr_push p]
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.complexity)⟩]}

@[simp] def qr_pull : Π {n} (p : subformula L n), p.pull.qr = p.qr
| n verum          := by simp[top_eq]
| n (relation p v) := by simp
| n (imply p q)    := by simp[imply_eq, qr_pull p, qr_pull q]
| n (neg p)        := by simp[neg_eq, qr_pull p]
| n (fal p)        := by simp[fal_eq, qr_pull p]

@[simp] def qr_mlift : Π {n} (p : subformula L n), p.mlift.qr = p.qr
| n verum          := by simp[top_eq]
| n (relation p v) := by simp
| n (imply p q)    := by simp[imply_eq, qr_mlift p, qr_mlift q]
| n (neg p)        := by simp[neg_eq, qr_mlift p]
| n (fal p)        := by simp[fal_eq, qr_mlift p]

@[simp] lemma qr_subst (u : subterm L n) (p : subformula L (n + 1)) : (subst u p).qr = p.qr :=
by simp[subst]

@[simp] lemma top_open : (⊤ : subformula L n).is_open := by simp[is_open] 

@[simp] lemma relation_open {k} (r : L.pr k) (v) : (relation r v : subformula L n).is_open := by simp[is_open]

@[simp] lemma equal_open [L.has_equal] {t u : subterm L n} : (t =' u : subformula L n).is_open := by simp[is_open] 

@[simp] lemma bot_open : (⊥ : subformula L n).is_open := by simp[is_open]

@[simp] lemma imply_open {p q : subformula L n} : (p ⟶ q).is_open ↔ p.is_open ∧ q.is_open := by simp[is_open] 

@[simp] lemma and_open {p q : subformula L n} : (p ⊓ q).is_open ↔ p.is_open ∧ q.is_open := by simp[is_open]

@[simp] lemma iff_open {p q : subformula L n} : (p ⟷ q).is_open ↔ p.is_open ∧ q.is_open := by simp[is_open]

@[simp] lemma finitary_conjunction_open {k} {p : fin k → subformula L n} :
  (⋀ i, p i).is_open ↔ ∀ i, (p i).is_open :=
by { induction k with k IH; simp*,
  { refine ⟨by { rintros ⟨hlast, hcast⟩, refine fin.last_cases _ _, exact hlast, exact hcast },
    by { intros h, simp[h] }⟩ } }

@[simp] lemma or_open {p q : subformula L n} : (p ⊔ q).is_open ↔ p.is_open ∧ q.is_open := by simp[is_open] 

@[simp] lemma finitary_disjunction_open {k} {p : fin k → subformula L n} :
  (⋁ i, p i).is_open ↔ ∀ i, (p i).is_open :=
by { induction k with k IH; simp*,
  { refine ⟨by { rintros ⟨hcast, hlast⟩, refine fin.last_cases _ _, exact hlast, exact hcast },
    by { intros h, simp[h] }⟩ } }

@[simp] lemma neg_open {p : subformula L n} : (∼p).is_open ↔ p.is_open := by simp[is_open] 

@[simp] lemma fal_not_open {p : subformula L (n + 1)} : ¬(∀'p).is_open := by simp[is_open] 

@[simp] lemma ex_not_open {p : subformula L (n + 1)} : ¬(∃'p).is_open := by simp[is_open] 

@[simp] lemma rew_open {p : subformula L n} {s : ℕ → subterm L n} :
  (rew s p).is_open ↔ p.is_open := by simp[is_open]

@[simp] lemma mlift_open {p : subformula L n} : (mlift p).is_open ↔ p.is_open := by simp[is_open]

@[simp] lemma msubst_open {u} {p : subformula L n} : (msubst u p).is_open ↔ p.is_open := by simp[is_open]

@[simp] lemma push_open {p : subformula L (n + 1)} : (push p).is_open ↔ p.is_open := by simp[is_open]

@[simp] lemma pull_open {p : subformula L n} : (pull p).is_open ↔ p.is_open := by simp[is_open]

@[simp] lemma subst_open {u} {p : subformula L (n + 1)} : (subst u p).is_open ↔ p.is_open := by simp[is_open]

@[simp] lemma dummy_open {p : subformula L n} : (dummy p).is_open ↔ p.is_open := by simp[dummy]

@[simp] lemma substs_open {p : subformula L n} {v} : (substs v p).is_open ↔ p.is_open :=
by induction n with n IH; simp[substs, *]

def open_rec {C : Π p : subformula L n, p.is_open → Sort*}
  (hverum : C ⊤ top_open)
  (hrel : Π (k) (r : L.pr k) (v : fin k → subterm L n), C (subformula.relation r v) (relation_open r v))
  (himply : Π (p q : subformula L n) (hp hq), C p hp → C q hq → C (p ⟶ q) (by simp[hp, hq]))
  (hneg : Π (p : subformula L n) (hp), C p hp → C (∼p) (by simp[hp])) :
  Π (p : subformula L n) (h : p.is_open), C p h
| ⊤                         _ := hverum
| (subformula.relation r v) _ := hrel _ r v
| (p ⟶ q)                   h := have p.is_open ∧ q.is_open, by simpa using h,
    himply p q this.1 this.2 (open_rec p this.1) (open_rec q this.2)
| (∼p)                      h := have p.is_open, by simpa using h, hneg p this (open_rec p this)
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.1.complexity)⟩]}

def open_rec_on (p : subformula L n) (h : p.is_open) {C : Π p : subformula L n, p.is_open → Sort*}
  (hverum : C ⊤ top_open)
  (hrel : Π (k) (r : L.pr k) (v : fin k → subterm L n), C (subformula.relation r v) (relation_open r v))
  (himply : Π (p q : subformula L n) (hp hq), C p hp → C q hq → C (p ⟶ q) (by simp[hp, hq]))
  (hneg : Π (p : subformula L n) (hp), C p hp → C (∼p) (by simp[hp])) :
  C p h := open_rec hverum hrel himply hneg p h

section open_rec
variables {C : Π p : subformula L n, p.is_open → Sort*}

@[simp] lemma rec_app_top {hverum hrel himply hneg h} : @open_rec L n C hverum hrel himply hneg ⊤ h = hverum :=
by simp[open_rec]

@[simp] lemma rec_app_rel {hverum hrel himply hneg} {k} (r : L.pr k) (v : fin k → subterm L n) {h} :
  @open_rec L n C hverum hrel himply hneg (subformula.relation r v) h = hrel k r v := by simp[open_rec]

@[simp] lemma rec_app_imply {hverum hrel himply hneg} (p q : subformula L n) {h} :
  @open_rec L n C hverum hrel himply hneg (p ⟶ q) h =
  himply p q (by simp at h; exact h.1) (by simp at h; exact h.2)
    (open_rec hverum hrel himply hneg p (by simp at h; exact h.1))
    (open_rec hverum hrel himply hneg q (by simp at h; exact h.2)) :=
by simp[open_rec]

@[simp] lemma rec_app_neg {hverum hrel himply hneg} (p : subformula L n) {h} :
  @open_rec L n C hverum hrel himply hneg (∼p) h =
  hneg p (by simpa using h) (open_rec hverum hrel himply hneg p (by simpa using h)) :=
by simp[open_rec]

end open_rec

end qr

end subformula

section
variables (L) (m n : ℕ)

def open_subformula := {p : subformula L n // p.is_open}

@[reducible] def open_formula := open_subformula L 0

-- @[reducible] def open_sentence := open_formula L 0

end

namespace preTheory
variables {L} {m : ℕ} (T U : preTheory L)

def mlift : preTheory L:= subformula.mlift '' T

variables {T U}

@[simp] lemma mlift_insert (p : formula L) : (insert p T).mlift = insert p.mlift T.mlift :=
by simp[mlift, set.image_insert_eq]

@[simp] lemma mlift_mem_mlift_iff {p : formula L} : p.mlift ∈ T.mlift ↔ p ∈ T :=
function.injective.mem_set_image subformula.mlift_inj

lemma mem_mlift_iff {p} :
  p ∈ T.mlift ↔ ∃ q ∈ T, subformula.mlift q = p :=
by simp[mlift]

def is_open : Prop := ∀ p ∈ T, subformula.is_open p

end preTheory


end fol