import lib.lib tactic data.set_like.basic logic translation

universes u v

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

variables (L : language.{u}) (μ : Type v)

inductive subterm (n : ℕ) : Type (max u v)
| metavar {} : μ → subterm
| var     {} : fin n → subterm
| function   : ∀ {k}, L.fn k → (fin k → subterm) → subterm

@[reducible] def term := subterm L μ 0

@[reducible] def bounded_subterm (m n : ℕ) := subterm L (fin m) n

@[reducible] def bounded_term (m : ℕ) := bounded_subterm L m 0

variables {L μ}

namespace subterm
variables {n : ℕ}

prefix `#`:max := subterm.var
prefix `&`:max := subterm.metavar

def term.const (f : L.fn 0) : subterm L μ n := function f finitary.nil

instance [inhabited μ] : inhabited (subterm L μ n) := ⟨&default⟩

variables (L μ n)

instance inhabited_of_inhabited [inhabited (L.fn 0)] : inhabited (subterm L μ n) := ⟨function default fin.nil⟩

end subterm

variables (L μ)
inductive subformula : ℕ → Type (max u v)
| verum    {n} : subformula n
| relation {n} : ∀ {k}, L.pr k → (fin k → subterm L μ n) → subformula n
| imply    {n} : subformula n → subformula n → subformula n
| neg      {n} : subformula n → subformula n
| fal      {n} : subformula (n + 1) → subformula n

attribute [pattern]  has_negation.neg has_arrow.arrow has_univ_quantifier'.univ has_exists_quantifier'.ex

@[reducible] def formula := subformula L μ 0

@[reducible] def bounded_subformula (m n : ℕ) := subformula L (fin m) n

@[reducible] def bounded_formula (m : ℕ) := bounded_subformula L m 0

@[reducible] def sentence := bounded_formula L 0

namespace subformula
variables {L μ} {n : ℕ}

def and (p : subformula L μ n) (q : subformula L μ n) : subformula L μ n := (p.imply q.neg).neg

def or (p : subformula L μ n) (q : subformula L μ n) : subformula L μ n := p.neg.imply q

def ex (p : subformula L μ (n + 1)) : subformula L μ n := p.neg.fal.neg

instance : has_logic_symbol (subformula L μ n) :=
{ bot := verum.neg,
  top := verum,
  sup := or,
  inf := and,
  arrow := imply,
  neg := neg }

instance : inhabited (subformula L μ n) := ⟨⊤⟩

def equal [L.has_equal] (t u : subterm L μ n) : subformula L μ n := relation language.has_equal.eq (t *> u *> fin.nil) 

instance [L.has_equal] : has_eq (subterm L μ n) (subformula L μ n) := ⟨equal⟩

instance : has_univ_quantifier' (subformula L μ) := ⟨@fal L μ⟩

instance : has_exists_quantifier' (subformula L μ) := ⟨@ex L μ⟩

lemma top_eq : @subformula.verum L μ n = (⊤) := rfl
lemma imply_eq : @subformula.imply L μ n = (⟶) := rfl
lemma equal_eq [L.has_equal] : @equal L μ n _ = (=') := rfl
lemma neg_eq : @subformula.neg L μ n = has_negation.neg := rfl
lemma fal_eq : @subformula.fal L μ n = has_univ_quantifier'.univ := rfl
lemma ex_eq : @subformula.ex L μ n = has_exists_quantifier'.ex := rfl

lemma ex_def (p : subformula L μ (n + 1)) : ∃'p = ∼∀'∼p := rfl

lemma bot_def : (⊥ : subformula L μ n) = ∼⊤ := rfl

@[simp] lemma equal.inj' [L.has_equal] (t₁ u₁ t₂ u₂ : subterm L μ n) : (t₁ =' t₂ : subformula L μ n) = (u₁ =' u₂) ↔ t₁ = u₁ ∧ t₂ = u₂ :=
⟨by simp[←equal_eq, equal]; intros h₁ h₂; exact ⟨h₁, h₂⟩, by simp; exact congr_arg2 (=')⟩

@[simp] lemma imply.inj' (p₁ q₁ p₂ q₂ : subformula L μ n) : p₁ ⟶ p₂ = q₁ ⟶ q₂ ↔ p₁ = q₁ ∧ p₂ = q₂ :=
⟨imply.inj, by simp; exact congr_arg2 (⟶)⟩

@[simp] lemma neg.inj' (p q : subformula L μ n) : ∼p = ∼q ↔ p = q := ⟨neg.inj, congr_arg _⟩

@[simp] lemma and.inj' (p₁ q₁ p₂ q₂ : subformula L μ n) : p₁ ⊓ p₂ = q₁ ⊓ q₂ ↔ p₁ = q₁ ∧ p₂ = q₂ :=
by simp[has_inf.inf, and]

@[simp] lemma or.inj' (p₁ q₁ p₂ q₂ : subformula L μ n) : p₁ ⊔ p₂ = q₁ ⊔ q₂ ↔ p₁ = q₁ ∧ p₂ = q₂ :=
by simp[has_sup.sup, or]

@[simp] lemma fal.inj' (p q : subformula L μ (n + 1)) : (∀'p : subformula L μ n) = ∀'q ↔ p = q := ⟨fal.inj, congr_arg _⟩

@[simp] lemma ex.inj' (p q : subformula L μ (n + 1)) : (∃'p : subformula L μ n) = ∃'q ↔ p = q := 
by simp[has_exists_quantifier'.ex, ex]

section ne
variables {k : ℕ} (r : L.pr k) (v : finitary (subterm L μ n) k) (t u : subterm L μ n)
  (p p₁ p₂ : subformula L μ n) (q : subformula L μ (n + 1))

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

@[simp] def complexity : Π {n}, subformula L μ n → ℕ
| n verum          := 0
| n (relation p v) := 0
| n (imply p q)    := max p.complexity q.complexity + 1
| n (neg p)        := p.complexity + 1
| n (fal p)        := p.complexity + 1

@[simp] lemma complexity_top : (⊤ : subformula L μ n).complexity = 0 := by refl

@[simp] lemma complexity_neg (p : subformula L μ n) : (∼p).complexity = p.complexity + 1 := by refl

@[simp] lemma complexity_fal (p : subformula L μ (n + 1)) : (∀'p).complexity = p.complexity + 1 := by refl

@[simp] lemma imply_complexity (p q : subformula L μ n) : (p ⟶ q).complexity = max p.complexity q.complexity + 1 := by refl

def ind {C : Π n, subformula L μ n → Sort*}
  (hverum : Π {n : ℕ}, C n ⊤)
  (hrelation : Π {n l : ℕ} (r : L.pr l) (v : fin l → subterm L μ n), C n (relation r v))
  (himply : Π {n : ℕ} (p q : subformula L μ n), C n p → C n q → C n (p ⟶ q))
  (hneg : Π {n : ℕ} (p : subformula L μ n), C n p → C n ∼p)
  (hfal : Π {n : ℕ} (p : subformula L μ (n + 1)), C (n + 1) p → C n (∀'p)) :
  Π {n : ℕ} (p : subformula L μ n), C n p
| n verum := hverum
| n (relation r v) := hrelation r v
| n (imply p q)    := himply p q (ind p) (ind q)
| n (neg p)        := hneg p (ind p)
| n (fal p)        := hfal p (ind p)

--普通に帰納法をすると論理記号で表示されないから
@[elab_as_eliminator]
protected def ind_on {C : Π n, subformula L μ n → Sort*}
  {n : ℕ} (p : subformula L μ n)
  (verum : Π {n : ℕ}, C n ⊤)
  (relation : Π {n l : ℕ} (r : L.pr l) (v : fin l → subterm L μ n), C n (relation r v))
  (imply : Π {n : ℕ} (p q : subformula L μ n), C n p → C n q → C n (p ⟶ q))
  (neg : Π {n : ℕ} (p : subformula L μ n), C n p → C n ∼p)
  (fal : Π {n : ℕ} (p : subformula L μ (n + 1)), C (n + 1) p → C n (∀'p)) :
  C n p :=
ind @verum @relation @imply @neg @fal p

def ind_succ {C : Π n, subformula L μ (n + 1) → Sort*}
  (hverum : Π {n : ℕ}, C n ⊤)
  (hrelation : Π {n l : ℕ} (r : L.pr l) (v : fin l → subterm L μ (n + 1)), C n (relation r v))
  (himply : Π {n : ℕ} (p q : subformula L μ (n + 1)), C n p → C n q → C n (p ⟶ q))
  (hneg : Π {n : ℕ} (p : subformula L μ (n + 1)), C n p → C n ∼p)
  (hfal : Π {n : ℕ} (p : subformula L μ (n + 1 + 1)), C (n + 1) p → C n (∀'p)) :
  Π {n : ℕ} (p : subformula L μ (n + 1)), C n p
| n verum := hverum
| n (relation r v) := hrelation r v
| n (imply p q)    := himply p q (ind_succ p) (ind_succ q)
| n (neg p)        := hneg p (ind_succ p)
| n (fal p)        := hfal p (ind_succ p)
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.complexity)⟩]}

@[elab_as_eliminator]
def ind_succ_on {C : Π n, subformula L μ (n + 1) → Sort*}
  {n : ℕ} (p : subformula L μ (n + 1))
  (verum : Π {n : ℕ}, C n ⊤)
  (relation : Π {n l : ℕ} (r : L.pr l) (v : fin l → subterm L μ (n + 1)), C n (relation r v))
  (imply : Π {n : ℕ} (p q : subformula L μ (n + 1)), C n p → C n q → C n (p ⟶ q))
  (neg : Π {n : ℕ} (p : subformula L μ (n + 1)), C n p → C n ∼p)
  (fal : Π {n : ℕ} (p : subformula L μ (n + 1 + 1)), C (n + 1) p → C n (∀'p)) :
  C n p :=
ind_succ @verum @relation @imply @neg @fal p

end subformula

@[reducible] def preTheory (L : language.{u}) (μ) := logic.Theory (subformula L μ 0)

@[reducible] def bounded_preTheory (L : language.{u}) (m : ℕ) := logic.Theory (subformula L (fin m) 0)

@[reducible] def Theory (L : language.{u}) := logic.Theory (subformula L (fin 0) 0)

namespace subterm

def const {n} (c : L.fn 0) : subterm L μ n := function c fin.nil

variables {L μ} {μ₁ : Type*} {μ₂ : Type*} {n : ℕ}

@[simp] def rew (s : μ₁ → subterm L μ₂ n) : subterm L μ₁ n → subterm L μ₂ n
| (&x)           := s x
| (#x)           := #x
| (function f v) := function f (λ i, (v i).rew)

def map (f : μ₁ → μ₂) : subterm L μ₁ n → subterm L μ₂ n := rew (λ x, &(f x))

section rew
variables {s : μ₁ → subterm L μ₂ n}

@[simp] lemma map_metavar (f : μ₁ → μ₂) (x) : map f (&x : subterm L μ₁ n) = &(f x) := rfl

@[simp] lemma map_var (f : μ₁ → μ₂) (x) : map f (#x : subterm L μ₁ n) = #x := rfl

@[simp] lemma map_function (f : μ₁ → μ₂) {k} (g : L.fn k) (v : fin k → subterm L μ₁ n) :
  map f (function g v) = function g (λ i, map f (v i)) := rfl

lemma eq_rew_of_eq {t : subterm L μ₁ n} {s₁ s₂ : μ₁ → subterm L μ₂ n} (h : s₁ = s₂) :
  rew s₁ t = rew s₂ t := by rw[h]

lemma rew_rew {μ₁ μ₂ μ₃} (s₀ : μ₁ → subterm L μ₂ n) (s₁ : μ₂ → subterm L μ₃ n) :
  ∀ t, rew s₁ (rew s₀ t) = rew (λ i, rew s₁ (s₀ i)) t
| (&x)           := by simp
| (#x)           := by simp
| (function f v) := by simp; funext i; exact rew_rew (v i)

@[simp] lemma map_map {μ₁ μ₂ μ₃} (f₁ : μ₁ → μ₂) (f₂ : μ₂ → μ₃) (t : subterm L μ₁ n) :
  map f₂ (map f₁ t) = map (f₂ ∘ f₁) t :=
by simp[map, rew_rew]

@[simp] lemma rew_metavar (t : subterm L μ n) : rew metavar t = t :=
by induction t; simp*

@[simp] lemma map_id (t : subterm L μ n) : map id t = t := by simp[map]

lemma map_inj_of_inj (f : μ₁ → μ₂) (I : function.injective f) :
  function.injective (map f : subterm L μ₁ n → subterm L μ₂ n)
| &x               &y               := by simp[map]; exact λ h, I h
| &x               #y               := by simp[map]
| &x               (function f v)   := by simp[map]
| #x               &y               := by simp[map]
| #x               #y               := by simp[map]
| #x               (function f v)   := by simp[map]
| (function f₁ v₁) &y               := by simp[map]
| (function f₁ v₁) #y               := by simp[map]
| (function f₁ v₁) (function f₂ v₂) :=
  by { simp[map], rintros rfl rfl,
       simp, intros h, funext i, exact @map_inj_of_inj (v₁ i) (v₂ i) (congr_fun h i) }

end rew

@[simp] def lift : subterm L μ n → subterm L μ (n + 1)
| #x             := #x.succ
| &x             := &x
| (function f v) := function f (λ i, (v i).lift)

section lift

lemma lift_rew (s : μ₁ → subterm L μ₂ n) (t : subterm L μ₁ n) : (t.rew s).lift = t.lift.rew (λ i, lift (s i)) :=
by induction t with x x p f v IH; simp; exact funext IH

@[simp] lemma lift_metavar : lift ∘ (metavar : μ → subterm L μ n) = metavar :=
funext (by simp)

variables {μ₁ μ₂} {f : μ₁ → μ₂}

lemma map_lift (t : subterm L μ₁ n) : map f t.lift = (map f t).lift :=
by induction t; simp*

end lift

section subst

/-
  #0 #1 ... #(n-1) #n &x ...
            ↓subst u
  #0 #1 ... #(n-1) u  &x ...
-/

def subst (u : subterm L μ n) : subterm L μ (n + 1) → subterm L μ n
| &x             := &x
| #x             := (var <* u) x
| (function f v) := function f (λ i, subst $ v i)

variables (u : subterm L μ n)

@[simp] lemma subst_metavar (x) : subst u (&x : subterm L μ (n + 1)) = &x := rfl

@[simp] lemma subst_var_last : subst u (#(fin.last n) : subterm L μ (n + 1)) = u := by simp[subst]

@[simp] lemma subst_var_cast (x : fin n) : subst u (#(x.cast_succ) : subterm L μ (n + 1)) = #x := by simp[subst]

@[simp] lemma subst_var_function {k} (f : L.fn k) (v : fin k → subterm L μ (n + 1)) :
  subst u (function f v) = function f (λ i, subst u $ v i) := by simp[subst]

variables {μ₁ μ₂} (f : μ₁ → μ₂)

lemma map_subst (u : subterm L μ₁ n) (t : subterm L μ₁ (n + 1)) :
  (subst u t).map f = subst (u.map f) (t.map f) :=
by { induction t; simp*, case var : x { refine fin.last_cases _ _ x; simp } }

end subst

section bounded_subterm
variables {L} {m m₁ m₂ : ℕ} {n}

def mlift : bounded_subterm L m n → bounded_subterm L (m + 1) n := map fin.cast_succ

section mlift

@[simp] lemma mlift_metavar (x : fin m) : (&x : bounded_subterm L m n).mlift = &x.cast_succ := rfl

@[simp] lemma mlift_var (x : fin n) : (#x : bounded_subterm L m n).mlift = #x := rfl

@[simp] lemma mlift_function {k} (f : L.fn k) (v : fin k → bounded_subterm L m n) :
  (function f v).mlift = function f (λ i, (v i).mlift) := rfl

lemma mlift_rew (s : fin m₁ → bounded_subterm L m₂ n) (t : bounded_subterm L m₁ n) : (t.rew s).mlift = t.rew (mlift ∘ s) :=
by induction t with x x p f v IH; simp; exact funext IH

lemma mlift_lift (t : bounded_subterm L m n) : t.mlift.lift = t.lift.mlift :=
by induction t; simp*

lemma mlift_inj : function.injective (@mlift L m n) := map_inj_of_inj _ (rel_embedding.injective _)

@[simp] lemma mlift_subst (u : bounded_subterm L m n) (t : bounded_subterm L m (n + 1)) :
  (subst u t).mlift = subst u.mlift t.mlift :=
by { induction t; simp*, case var : x { refine fin.last_cases _ _ x; simp } }

def cast_le (h : m₁ ≤ m₂) : bounded_subterm L m₁ n → bounded_subterm L m₂ n := map (fin.cast_le h)

variables {m₁ m₂} (h : m₁ ≤ m₂)

@[simp] lemma cast_le_metavar (x : fin m₁) : cast_le h (&x : bounded_subterm L m₁ n) = &(fin.cast_le h x) :=
by simp[cast_le]

@[simp] lemma cast_le_var (x : fin n) : cast_le h (#x : bounded_subterm L m₁ n) = #x :=
by simp[cast_le]

@[simp] lemma cast_le_function {k} (f : L.fn k) (v : fin k → bounded_subterm L m₁ n) :
  cast_le h (function f v) = function f (λ i, cast_le h (v i)) :=
by simp[cast_le]

@[simp] lemma cast_le_inj (p q : bounded_subterm L m₁ n) : cast_le h p = cast_le h q ↔ p = q :=
⟨λ h, map_inj_of_inj _ (rel_embedding.injective _) h, λ h, by simp[h]⟩

@[simp] lemma case_le_lift (t : bounded_subterm L m₁ n) : (cast_le h t).lift = cast_le h t.lift :=
by induction t; simp*

@[simp] lemma cast_le_mlift (t : bounded_subterm L m₁ n) (h : m₁ + 1 ≤ m₂) :
  cast_le h (mlift t) = cast_le (nat.le_of_succ_le h) t :=
by { induction t; simp*, case metavar : x { ext; simp } }

@[simp] lemma mlift_cast_le (t : bounded_subterm L m₁ n) (h : m₁ ≤ m₂) :
  mlift (cast_le h t) = cast_le (le_add_right h) t :=
by { induction t; simp*, case metavar : x { ext; simp } }

end mlift

/-
  #0 #1 #2 #3 #4 ... #(n - 1) #n &(m - 1) ... &3 &2 &1 &0 
      ↓push                       ↑pull
  #0 #1 #2 #3 #4 ... #(n - 1) &m &(m - 1) ... &3 &2 &1 &0 
-/

def push : bounded_subterm L m (n + 1) → bounded_subterm L (m + 1) n
| (&x)           := &x.cast_succ
| (#x)           := (var <* &(fin.last m)) x
| (function f v) := function f (λ i, (v i).push)

section push

@[simp] lemma push_metavar (x) : (&x : bounded_subterm L m (n + 1)).push = &x.cast_succ := rfl

@[simp] lemma push_var_last : (#(fin.last n) : bounded_subterm L m (n + 1)).push = &(fin.last m) := by simp[push]

@[simp] lemma push_var_cast (x) : (#(fin.cast_succ x) : bounded_subterm L m (n + 1)).push = #x := by simp[push]

@[simp] lemma push_function {k} (f : L.fn k) (v : fin k → bounded_subterm L m (n + 1)) :
  (function f v).push = function f (push ∘ v) := by simp[push]

lemma push_lift_comm (t : bounded_subterm L m (n + 1)) : t.lift.push = t.push.lift :=
by { induction t; simp*,
     case var : x { refine fin.last_cases _ _ x; simp[fin.succ_cast_succ], },
     case function : k f v IH
     { funext i, exact IH i } }

@[simp] lemma subst_mlift (t : bounded_subterm L m (n + 1)) : subst &(fin.last m) (mlift t) = push t :=
by { induction t; simp*, case var : x { refine fin.last_cases _ _ x; simp } }

end push

def pull : bounded_subterm L (m + 1) n → bounded_subterm L m (n + 1)
| (&x)           := (metavar <* #(fin.last n)) x
| (#x)           := #x.cast_succ
| (function f v) := function f (λ i, (v i).pull)

section pull

@[simp] lemma pull_metavar_zero : (&(fin.last m) : bounded_subterm L (m + 1) n).pull = #(fin.last n) := by simp[pull]

@[simp] lemma pull_metavar_succ (x : fin m) : (&x.cast_succ : bounded_subterm L (m + 1) n).pull = &x := by simp[pull]

@[simp] lemma pull_var (x) : (#x : bounded_subterm L (m + 1) n).pull = #x.cast_succ := by simp[pull]

@[simp] lemma pull_function {k} (f : L.fn k) (v : fin k → bounded_subterm L (m + 1) n) :
  (function f v).pull = function f (λ i, (v i).pull) := by simp[pull]

@[simp] lemma pull_push (t : bounded_subterm L m (n + 1)) : t.push.pull = t :=
by{ induction t, 
    case metavar : x { simp, },
    case var : x { refine fin.last_cases _ _ x; simp },
    case function : p f v IH { simp, funext x, simp[IH] } }

@[simp] lemma push_pull (t : bounded_subterm L (m + 1) n) : t.pull.push = t :=
by{ induction t,
    case metavar : x { refine fin.last_cases _ _ x; simp },
    case var : x { simp },
    case function : p f v IH { simp, funext x, simp[IH] } }

lemma push_rew_pull (t : bounded_subterm L (m₁ + 1) n) (s : fin m₁ → bounded_subterm L m₂ (n + 1)) :
  (rew s t.pull).push = rew (push ∘ s <* &(fin.last m₂)) t :=
by { induction t; simp*,
      case metavar : x { refine fin.last_cases _ _ x; simp },
      case function : k f v IH
      { funext i, exact IH i } }

lemma pull_lift_comm (t : bounded_subterm L (m + 1) n) : t.lift.pull = t.pull.lift :=
by { induction t; simp[*, fin.succ_cast_succ],
     case metavar : x { refine fin.last_cases _ _ x; simp } }

end pull

def dummy : bounded_subterm L m n → bounded_subterm L m (n + 1) := pull ∘ mlift

section dummy

@[simp] lemma dummy_metavar (x) : dummy (&x : bounded_subterm L m n) = &x := by simp[dummy]

@[simp] lemma dummy_var (x) : dummy (#x : bounded_subterm L m n) = #x.cast_succ := by simp[dummy]

@[simp] lemma dummy_function {k} (f : L.fn k) (v : fin k → bounded_subterm L m n) :
  dummy (function f v) = function f (λ i, dummy (v i)) := by simp[dummy]

@[simp] lemma dummy_subst (u : bounded_subterm L m n) (t : bounded_subterm L m n) :
  subst u t.dummy = t :=
by induction t; simp*

lemma dummy_lift_comm (t : bounded_subterm L m n) :
  t.lift.dummy = t.dummy.lift :=
by simp[dummy, ←mlift_lift, pull_lift_comm]

end dummy

end bounded_subterm

end subterm

namespace subformula
open subterm finitary
variables {L μ} {μ₁ : Type*} {μ₂ : Type*} {n : ℕ}

section rew

def rew' {μ₁ μ₂} : Π {n}, (μ₁ → subterm L μ₂ n) → subformula L μ₁ n → subformula L μ₂ n
| n s verum          := ⊤
| n s (relation p v) := relation p (λ i, (v i).rew s)
| n s (imply p q)    := p.rew' s ⟶ q.rew' s
| n s (neg p)        := ∼p.rew' s
| n s (fal p)        := ∀'p.rew' (subterm.lift ∘ s)

def rew (s : μ₁ → subterm L μ₂ n) : subformula L μ₁ n →ₗ subformula L μ₂ n :=
{ to_fun := rew' s,
  map_neg' := λ p, by refl,
  map_imply' := λ p q, by refl,
  map_and' := λ p q, by refl,
  map_or' := λ p q, by refl,
  map_top' := by refl,
  map_bot' := by refl }

def map (f : μ₁ → μ₂) : subformula L μ₁ n →ₗ subformula L μ₂ n := rew (λ x, &(f x))

variables (s : μ₁ → subterm L μ₂ n) (f : μ₁ → μ₂)

lemma rew_def (p : subformula L μ₁ n) : rew s p = rew' s p := rfl

variables {s}

@[simp] lemma rew_relation {k} (r : L.pr k) (v) :
  rew s (relation r v) = relation r (λ x, subterm.rew s (v x)) := rfl

@[simp] lemma rew_fal (p : subformula L μ₁ (n + 1)) :
  rew s (∀'p) = ∀'rew (λ x, (s x).lift) p := rfl

@[simp] lemma rew_ex (p : subformula L μ₁ (n + 1)) :
  rew s (∃'p) = ∃'rew (λ x, (s x).lift) p := by simp[ex_def]

@[simp] lemma map_relation {k} (r : L.pr k) (v : fin k → subterm L μ₁ n) :
  map f (relation r v) = relation r (λ x, subterm.map f (v x)) := rfl

@[simp] lemma map_fal (p : subformula L μ₁ (n + 1)) :
  map f (∀'p) = ∀'map f p := rfl

@[simp] lemma map_ex (p : subformula L μ₁ (n + 1)) :
  map f (∃'p) = ∃'map f p := by simp[ex_def]

lemma rew_eq_self_of_eq {s : μ → subterm L μ n} (h : s = metavar) (p : subformula L μ n) : rew s p = p :=
by induction p using fol.subformula.ind_on; simp[subterm.mlift_rew, *]

@[simp] lemma rew_metavar (p : subformula L μ n) : rew metavar p = p := rew_eq_self_of_eq rfl p

@[simp] lemma map_id (p : subformula L μ n) : map id p = p := rew_eq_self_of_eq rfl p

lemma eq_rew_of_eq {p : subformula L μ₁ n} {s₁ s₂ : μ₁ → subterm L μ₂ n} (h : s₁ = s₂) :
  rew s₁ p = rew s₂ p := by rw[h]

lemma rew_rew {μ₁ μ₂ μ₃} : ∀ {n} (p : subformula L μ₁ n) (s₀ : μ₁ → subterm L μ₂ n) (s₁ : μ₂ → subterm L μ₃ n),
  rew s₁ (rew s₀ p) = rew (λ x, subterm.rew s₁ (s₀ x)) p
| n verum          s₀ s₁ := by simp[top_eq]
| n (relation p v) s₀ s₁ := by simp; funext; simp[subterm.rew_rew]
| n (imply p q)    s₀ s₁ := by simp[imply_eq, rew_rew p, rew_rew q]
| n (neg p)        s₀ s₁ := by simp[neg_eq, rew_rew p]
| n (fal p)        s₀ s₁ := by simp[fal_eq, rew_rew p]; refine eq_rew_of_eq (by funext x; simp[subterm.lift_rew])

@[simp] lemma map_map {μ₁ μ₂ μ₃} (f₁ : μ₁ → μ₂) (f₂ : μ₂ → μ₃) (p : subformula L μ₁ n) :
  map f₂ (map f₁ p) = map (f₂ ∘ f₁) p :=
by simp[map, rew_rew]

@[simp] lemma complexity_rew (p : subformula L μ₁ n) : complexity (rew s p) = complexity p :=
by induction p using fol.subformula.ind_on; simp*

lemma map_inj_of_inj (f : μ₁ → μ₂) (I : function.injective f) :
  function.injective (map f : subformula L μ₁ n → subformula L μ₂ n) := λ p q,
begin
  induction p using fol.subformula.ind_on,
  case verum { cases q; simp[top_eq, equal_eq, imply_eq, neg_eq, fal_eq], },
  case relation : n k r v₁
  { cases q; simp[top_eq, equal_eq, imply_eq, neg_eq, fal_eq];
    case relation : _ _ r₂ v₂
    { rintros rfl rfl, simp, intros h, funext i, exact subterm.map_inj_of_inj f I (congr_fun h i) } },
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

end rew

section subst

@[simp] def subst' : Π {n}, subterm L μ n → subformula L μ (n + 1) → subformula L μ n
| n u verum          := ⊤
| n u (relation r v) := relation r (λ i, subterm.subst u $ v i)
| n u (imply p q)    := subst' u p ⟶ subst' u q
| n u (neg p)        := ∼subst' u p
| n u (fal p)        := ∀' (subst' u.lift p)
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.2.complexity)⟩]}

def subst (u : subterm L μ n) : subformula L μ (n + 1) →ₗ subformula L μ n :=
{ to_fun := subst' u,
  map_neg' := λ p, by unfold has_negation.neg; simp; refl,
  map_imply' := λ p q, by unfold has_arrow.arrow; simp; refl,
  map_and' := λ p q, by unfold has_inf.inf; simp[and]; refl,
  map_or' := λ p q, by unfold has_sup.sup; simp[or]; refl,
  map_top' := by unfold has_top.top; simp; refl,
  map_bot' := by unfold has_bot.bot; simp; refl }

variables (u : subterm L μ n)

@[simp] lemma subst_relation {k} (r : L.pr k) (v : fin k → subterm L μ (n + 1)) :
  subst u (relation r v) = relation r (λ i, u.subst (v i)) := by simp[subst]

@[simp] lemma subst_fal (p : subformula L μ (n + 1 + 1)) :
  subst u (∀'p) = ∀'subst u.lift p := by simp[←fal_eq, subst]

@[simp] lemma subst_ex (p : subformula L μ (n + 1 + 1)) :
  subst u (∃'p) = ∃'subst u.lift p := by simp[ex_def]

variables {μ₁ μ₂} (f : μ₁ → μ₂)

lemma map_subst (p : subformula L μ₁ (n + 1)) : ∀ (u : subterm L μ₁ n),
  map f (subst u p) = subst (u.map f) (map f p) :=
by apply ind_succ_on p; intros; simp[*, subterm.map_subst, subterm.map_lift]

end subst

section bounded_formula
variables {m : ℕ}

def mlift {m n} : bounded_subformula L m n →ₗ bounded_subformula L (m + 1) n := map fin.cast_succ

section mlift

@[simp] lemma mlift_relation {k} (r : L.pr k) (v : fin k → bounded_subterm L m n) :
  mlift (relation r v) = relation r (λ i, subterm.mlift (v i)) := rfl

@[simp] lemma mlift_fal (p : bounded_subformula L m (n + 1)) :
  mlift (∀'p) = ∀'mlift p := rfl

@[simp] lemma mlift_ex (p : bounded_subformula L m (n + 1)) :
  mlift (∃'p) = ∃'mlift p := by simp[ex_def]

variables {m₁ m₂ : ℕ} (s : fin m₁ → bounded_subterm L m₂ n)

lemma mlift_rew (p : bounded_subformula L m₁ n) : mlift (rew s p) = rew (λ x, (s x).mlift) p :=
by induction p using fol.subformula.ind_on; simp[subterm.mlift_rew, subterm.mlift_lift, *]

@[simp] lemma complexity_mlift (p : bounded_subformula L m n) : p.mlift.complexity = p.complexity :=
by induction p using fol.subformula.ind_on; simp*

lemma mlift_inj : function.injective (@mlift L m n) :=
map_inj_of_inj _ (rel_embedding.injective _)

def cast_le {n} (h : m₁ ≤ m₂) : bounded_subformula L m₁ n →ₗ bounded_subformula L m₂ n := map (fin.cast_le h)

variables (h : m₁ ≤ m₂)

@[simp] lemma cast_le_of_eq (p : bounded_subformula L m n) {h} : cast_le h p = p := 
by simp[cast_le, show ⇑(fin.cast_le h) = id, by ext; simp]

@[simp] lemma cast_le_function {k} (r : L.pr k) (v : fin k → bounded_subterm L m₁ n) :
  cast_le h (relation r v) = relation r (subterm.cast_le h ∘ v) :=
by simp[cast_le]; refl

@[simp] lemma cast_le_fal (p : bounded_subformula L m₁ (n + 1)) :
  cast_le h (∀'p) = ∀'(cast_le h p) :=
by simp[cast_le]; refl

@[simp] lemma cast_le_ex (p : bounded_subformula L m₁ (n + 1)) :
  cast_le h (∃'p) = ∃'(cast_le h p) :=
by simp[cast_le]; refl

lemma cast_le_inj : function.injective (@cast_le L m₁ m₂ n h) :=
map_inj_of_inj _ (rel_embedding.injective _)

end mlift

def push' {m} : Π {n}, bounded_subformula L m (n + 1) → bounded_subformula L (m + 1) n
| n verum          := ⊤
| n (relation p v) := relation p (subterm.push ∘ v)
| n (imply p q)    := p.push' ⟶ q.push'
| n (neg p)        := ∼p.push'
| n (fal p)        := ∀'p.push'
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.complexity)⟩]}

def push : bounded_subformula L m (n + 1) →ₗ bounded_subformula L (m + 1) n :=
{ to_fun := push',
  map_neg' := λ p, by unfold has_negation.neg; simp[push']; refl,
  map_imply' := λ p q, by unfold has_arrow.arrow; simp[push']; refl,
  map_and' := λ p q, by unfold has_inf.inf; simp[and, push']; refl,
  map_or' := λ p q, by unfold has_sup.sup; simp[or, push']; refl,
  map_top' := by unfold has_top.top; simp[push']; refl,
  map_bot' := by unfold has_bot.bot; simp[push']; refl }

section push

lemma push_def (p : bounded_subformula L m (n + 1)) : push p = push' p := rfl

@[simp] lemma push_relation {k} (r : L.pr k) (v : fin k → bounded_subterm L m (n + 1)) :
  push (relation r v) = relation r (λ i, subterm.push (v i)) := by simp[push_def, push']

@[simp] lemma push_fal (p : bounded_subformula L m (n + 1 + 1)) :
  push (∀'p) = ∀'push p := by unfold has_univ_quantifier'.univ; simp[push_def, push']; refl

@[simp] lemma push_ex (p : bounded_subformula L m (n + 1 + 1)) :
  push (∃'p) = ∃'push p := by simp[ex_def]

@[simp] lemma complexity_push {n} (p : bounded_subformula L m (n + 1)) : p.push.complexity = p.complexity :=
by apply ind_succ_on p; intros; simp*

variables {m₁ m₂ : ℕ} (f : fin m₁ → fin m₂)

end push

def pull' {m} : Π {n}, bounded_subformula L (m + 1) n → bounded_subformula L m (n + 1)
| n verum          := ⊤
| n (relation p v) := relation p (subterm.pull ∘ v)
| n (imply p q)    := p.pull' ⟶ q.pull'
| n (neg p)        := ∼p.pull'
| n (fal p)        := ∀'p.pull'

def pull : bounded_subformula L (m + 1) n →ₗ bounded_subformula L m (n + 1) :=
{ to_fun := pull',
  map_neg' := λ p, by refl,
  map_imply' := λ p q, by refl,
  map_and' := λ p q, by refl,
  map_or' := λ p q, by refl,
  map_top' := by refl,
  map_bot' := by refl }

section pull

lemma pull_def (p : bounded_subformula L (m + 1) n) : pull p = pull' p := rfl

@[simp] lemma pull_relation {k} (r : L.pr k) (v : fin k → bounded_subterm L (m + 1) n) :
  pull (relation r v) = relation r (λ i, subterm.pull (v i)) := by refl

@[simp] lemma pull_fal (p : bounded_subformula L (m + 1) (n + 1)) :
  pull (∀'p) = ∀'pull p := by refl

@[simp] lemma pull_ex (p : bounded_subformula L (m + 1) (n + 1)) :
  pull (∃'p) = ∃'pull p := by simp[ex_def]

@[simp] lemma pull_push : ∀ {n} (p : bounded_subformula L m (n + 1)), p.push.pull = p
| n verum          := by simp[top_eq]
| n (relation p v) := by simp; funext x; simp
| n (imply p q)    := by simp[imply_eq]; exact ⟨pull_push p, pull_push q⟩
| n (neg p)        := by simp[neg_eq]; exact pull_push p
| n (fal p)        := by simp[fal_eq]; exact pull_push p
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.complexity)⟩]}

@[simp] lemma push_pull : ∀ {n} (p : bounded_subformula L (m + 1) n), p.pull.push = p
| n verum          := by simp[top_eq]
| n (relation p v) := by simp; funext x; simp
| n (imply p q)    := by simp[imply_eq]; exact ⟨push_pull p, push_pull q⟩
| n (neg p)        := by simp[neg_eq]; exact push_pull p
| n (fal p)        := by simp[fal_eq]; exact push_pull p

lemma push_inj : function.injective (@push L m n) :=
@function.left_inverse.injective _ _ (@pull L m n) _ pull_push

lemma pull_inj : function.injective (@pull L m n) :=
@function.left_inverse.injective _ _ (@push L m n) _ push_pull

lemma push_rew_pull {m₁ m₂} : ∀ {n} (p : bounded_subformula L (m₁ + 1) n) (s : fin m₁ → bounded_subterm L m₂ (n + 1)),
  (rew s p.pull).push = rew (subterm.push ∘ s <* &(fin.last m₂)) p
| n verum          s := by simp[top_eq]
| n (relation p v) s := by simp; funext x; simp[subterm.push_rew_pull]
| n (imply p q)    s := by simp[imply_eq]; exact ⟨push_rew_pull p s, push_rew_pull q s⟩
| n (neg p)        s := by simp[neg_eq]; exact push_rew_pull p s
| n (fal p)        s := by simp[fal_eq]; {
    simp[push_rew_pull p (subterm.lift ∘ s)],
    refine eq_rew_of_eq (by { funext x, refine fin.last_cases _ _ x; simp[subterm.push_lift_comm] }) }

@[simp] lemma complexity_pull (p : bounded_subformula L (m + 1) n) : p.pull.complexity = p.complexity :=
by induction p using fol.subformula.ind_on; intros; simp*

end pull

@[simp] lemma subst_mlift {n} (p : bounded_subformula L m (n + 1)) : subst &(fin.last m) (mlift p) = push p :=
by apply ind_succ_on p; intros; simp*

def dummy : bounded_subformula L m n →ₗ bounded_subformula L m (n + 1) := pull.comp mlift

section dummy

@[simp] lemma dummy_relation {k} (r : L.pr k) (v : fin k → bounded_subterm L m n) :
  dummy (relation r v) = relation r (λ i, (v i).dummy) := by simp[dummy, subterm.dummy]

@[simp] lemma dummy_fal (p : bounded_subformula L m (n + 1)) : dummy (∀'p) = ∀'(dummy p) := by simp[dummy]

@[simp] lemma dummy_ex (p : bounded_subformula L m (n + 1)) : dummy (∃'p) = ∃'(dummy p) := by simp[dummy]

@[simp] lemma push_dummy  (p : bounded_subformula L m n) : push (dummy p) = mlift p := by simp[dummy]

@[simp] lemma dummy_subst (p : bounded_subformula L m n) (t) : (subst t $ dummy p) = p :=
by induction p; intros; simp[top_eq, equal_eq, imply_eq, neg_eq, fal_eq, *]

@[simp] lemma complexity_dummy (p : bounded_subformula L m n) : p.dummy.complexity = p.complexity :=
by simp[dummy]

end dummy

end bounded_formula

def qr : Π {n}, subformula L μ n → ℕ
| n verum          := 0
| n (relation r v) := 0
| n (imply p q)    := max p.qr q.qr
| n (neg p)        := p.qr
| n (fal p)        := p.qr + 1

def is_open (p : subformula L μ n) : Prop := p.qr = 0

section qr
open subformula
variables {n}

@[simp] lemma qr_top : (⊤ : subformula L μ n).qr = 0 := rfl

@[simp] lemma qr_bot : (⊥ : subformula L μ n).qr = 0 := rfl

@[simp] lemma qr_relation {p} (r : L.pr p) (v : finitary (subterm L μ n) p) : (relation r v).qr = 0 := rfl

@[simp] lemma qr_equal [L.has_equal] (t u : subterm L μ n) : (t =' u : subformula L μ n).qr = 0 := rfl

@[simp] lemma qr_imply (p q : subformula L μ n) : (p ⟶ q : subformula L μ n).qr = max p.qr q.qr := rfl

@[simp] lemma qr_and (p q : subformula L μ n) : (p ⊓ q : subformula L μ n).qr = max p.qr q.qr := rfl

@[simp] lemma qr_or (p q : subformula L μ n) : (p ⊔ q : subformula L μ n).qr = max p.qr q.qr := rfl

@[simp] lemma qr_iff (p q : subformula L μ n) : (p ⟷ q : subformula L μ n).qr = max p.qr q.qr := by simp[lrarrow_def, max_comm]

@[simp] lemma qr_neg (p : subformula L μ n) : (∼p).qr = p.qr := rfl

@[simp] lemma qr_fal (p : subformula L μ (n + 1)) : (∀'p).qr = p.qr + 1 := rfl

@[simp] lemma qr_ex (p : subformula L μ (n + 1)) : (∃'p).qr = p.qr + 1 := rfl

@[simp] lemma qr_rew {μ₁ μ₂} : Π {n} (p : subformula L μ₁ n) (s : μ₁ → subterm L μ₂ n), (rew s p).qr = p.qr
| n verum          := by simp[top_eq]
| n (relation p v) := by simp
| n (imply p q)    := by simp[imply_eq, qr_rew p, qr_rew q]
| n (neg p)        := by simp[neg_eq, qr_rew p]
| n (fal p)        := by simp[fal_eq, qr_rew p]

@[simp] def qr_push {m} : Π {n} (p : bounded_subformula L m (n + 1)), p.push.qr = p.qr
| n verum          := by simp[top_eq]
| n (relation p v) := by simp
| n (imply p q)    := by simp[imply_eq, qr_push p, qr_push q]
| n (neg p)        := by simp[neg_eq, qr_push p]
| n (fal p)        := by simp[fal_eq, qr_push p]
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.complexity)⟩]}

@[simp] def qr_pull {m} : Π {n} (p : bounded_subformula L (m + 1) n), p.pull.qr = p.qr
| n verum          := by simp[top_eq]
| n (relation p v) := by simp
| n (imply p q)    := by simp[imply_eq, qr_pull p, qr_pull q]
| n (neg p)        := by simp[neg_eq, qr_pull p]
| n (fal p)        := by simp[fal_eq, qr_pull p]

@[simp] def qr_mlift {m} : Π {n} (p : bounded_subformula L m n), p.mlift.qr = p.qr
| n verum          := by simp[top_eq]
| n (relation p v) := by simp
| n (imply p q)    := by simp[imply_eq, qr_mlift p, qr_mlift q]
| n (neg p)        := by simp[neg_eq, qr_mlift p]
| n (fal p)        := by simp[fal_eq, qr_mlift p]

@[simp] lemma qr_subst (p : subformula L μ (n + 1)) : ∀ (u : subterm L μ n), (subst u p).qr = p.qr :=
by apply ind_succ_on p ; intros; simp*

@[simp] lemma top_open : (⊤ : subformula L μ n).is_open := by simp[is_open] 

@[simp] lemma relation_open {k} (r : L.pr k) (v) : (relation r v : subformula L μ n).is_open := by simp[is_open]

@[simp] lemma equal_open [L.has_equal] {t u : subterm L μ n} : (t =' u : subformula L μ n).is_open := by simp[is_open] 

@[simp] lemma bot_open : (⊥ : subformula L μ n).is_open := by simp[is_open]

@[simp] lemma imply_open {p q : subformula L μ n} : (p ⟶ q).is_open ↔ p.is_open ∧ q.is_open := by simp[is_open] 

@[simp] lemma and_open {p q : subformula L μ n} : (p ⊓ q).is_open ↔ p.is_open ∧ q.is_open := by simp[is_open]

@[simp] lemma iff_open {p q : subformula L μ n} : (p ⟷ q).is_open ↔ p.is_open ∧ q.is_open := by simp[is_open]

@[simp] lemma finitary_conjunction_open {k} {p : fin k → subformula L μ n} :
  (⋀ i, p i).is_open ↔ ∀ i, (p i).is_open :=
by { induction k with k IH; simp*,
  { refine ⟨by { rintros ⟨hlast, hcast⟩, refine fin.last_cases _ _, exact hlast, exact hcast },
    by { intros h, simp[h] }⟩ } }

@[simp] lemma or_open {p q : subformula L μ n} : (p ⊔ q).is_open ↔ p.is_open ∧ q.is_open := by simp[is_open] 

@[simp] lemma finitary_disjunction_open {k} {p : fin k → subformula L μ n} :
  (⋁ i, p i).is_open ↔ ∀ i, (p i).is_open :=
by { induction k with k IH; simp*,
  { refine ⟨by { rintros ⟨hcast, hlast⟩, refine fin.last_cases _ _, exact hlast, exact hcast },
    by { intros h, simp[h] }⟩ } }

@[simp] lemma neg_open {p : subformula L μ n} : (∼p).is_open ↔ p.is_open := by simp[is_open] 

@[simp] lemma fal_not_open {p : subformula L μ (n + 1)} : ¬(∀'p).is_open := by simp[is_open] 

@[simp] lemma ex_not_open {p : subformula L μ (n + 1)} : ¬(∃'p).is_open := by simp[is_open] 

@[simp] lemma rew_open {μ₁ μ₂} {p : subformula L μ₁ n} {s : μ₁ → subterm L μ₂ n} :
  (rew s p).is_open ↔ p.is_open := by simp[is_open]

@[simp] lemma subst_open {u} {p : subformula L μ (n + 1)} : (subst u p).is_open ↔ p.is_open := by simp[is_open]

section bounded_formula
variables {m : ℕ}

@[simp] lemma mlift_open {p : bounded_subformula L m n} : (mlift p).is_open ↔ p.is_open := by simp[is_open]

@[simp] lemma push_open {p : bounded_subformula L m (n + 1)} : (push p).is_open ↔ p.is_open := by simp[is_open]

@[simp] lemma pull_open {p : bounded_subformula L (m + 1) n} : (pull p).is_open ↔ p.is_open := by simp[is_open]

@[simp] lemma dummy_open {p : bounded_subformula L m n} : (dummy p).is_open ↔ p.is_open := by simp[dummy]

end bounded_formula

def open_rec {C : Π p : subformula L μ n, p.is_open → Sort*}
  (hverum : C ⊤ top_open)
  (hrel : Π (k) (r : L.pr k) (v : fin k → subterm L μ n), C (subformula.relation r v) (relation_open r v))
  (himply : Π (p q : subformula L μ n) (hp hq), C p hp → C q hq → C (p ⟶ q) (by simp[hp, hq]))
  (hneg : Π (p : subformula L μ n) (hp), C p hp → C (∼p) (by simp[hp])) :
  Π (p : subformula L μ n) (h : p.is_open), C p h
| ⊤                         _ := hverum
| (subformula.relation r v) _ := hrel _ r v
| (p ⟶ q)                   h := have p.is_open ∧ q.is_open, by simpa using h,
    himply p q this.1 this.2 (open_rec p this.1) (open_rec q this.2)
| (∼p)                      h := have p.is_open, by simpa using h, hneg p this (open_rec p this)
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.1.complexity)⟩]}

def open_rec_on (p : subformula L μ n) (h : p.is_open) {C : Π p : subformula L μ n, p.is_open → Sort*}
  (hverum : C ⊤ top_open)
  (hrel : Π (k) (r : L.pr k) (v : fin k → subterm L μ n), C (subformula.relation r v) (relation_open r v))
  (himply : Π (p q : subformula L μ n) (hp hq), C p hp → C q hq → C (p ⟶ q) (by simp[hp, hq]))
  (hneg : Π (p : subformula L μ n) (hp), C p hp → C (∼p) (by simp[hp])) :
  C p h := open_rec hverum hrel himply hneg p h

section open_rec
variables {C : Π p : subformula L μ n, p.is_open → Sort*}

@[simp] lemma rec_app_top {hverum hrel himply hneg h} : @open_rec L μ n C hverum hrel himply hneg ⊤ h = hverum :=
by simp[open_rec]

@[simp] lemma rec_app_rel {hverum hrel himply hneg} {k} (r : L.pr k) (v : fin k → subterm L μ n) {h} :
  @open_rec L μ n C hverum hrel himply hneg (subformula.relation r v) h = hrel k r v := by simp[open_rec]

@[simp] lemma rec_app_imply {hverum hrel himply hneg} (p q : subformula L μ n) {h} :
  @open_rec L μ n C hverum hrel himply hneg (p ⟶ q) h =
  himply p q (by simp at h; exact h.1) (by simp at h; exact h.2)
    (open_rec hverum hrel himply hneg p (by simp at h; exact h.1))
    (open_rec hverum hrel himply hneg q (by simp at h; exact h.2)) :=
by simp[open_rec]

@[simp] lemma rec_app_neg {hverum hrel himply hneg} (p : subformula L μ n) {h} :
  @open_rec L μ n C hverum hrel himply hneg (∼p) h =
  hneg p (by simpa using h) (open_rec hverum hrel himply hneg p (by simpa using h)) :=
by simp[open_rec]

end open_rec

end qr

end subformula

namespace bounded_preTheory
variables {L} {m : ℕ} (T U : bounded_preTheory L m)

def mlift : bounded_preTheory L (m + 1) := subformula.mlift '' T

instance : has_coe (bounded_preTheory L m) (bounded_preTheory L (m + 1)) := ⟨mlift⟩

variables {T U}

@[simp] lemma mlift_insert (p : bounded_formula L m) : mlift (insert p T) = insert p.mlift (mlift T) :=
by simp[mlift, set.image_insert_eq]

@[simp] lemma mlift_mem_mlift_iff {p : bounded_formula L m} : p.mlift ∈ T.mlift ↔ p ∈ T :=
function.injective.mem_set_image subformula.mlift_inj

lemma mem_mlift_iff {p} :
  p ∈ T.mlift ↔ ∃ q ∈ T, subformula.mlift q = p :=
by simp[mlift]

def is_open : Prop := ∀ p ∈ T, subformula.is_open p

end bounded_preTheory

end fol