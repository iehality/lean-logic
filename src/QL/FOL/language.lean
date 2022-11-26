import QL.FOL.deduction

universes u

namespace fol
open_locale logic_symbol aclogic
open subterm subformula logic logic.Theory
variables {L R : language.{u}} {L₁ L₂ L₃ : language} {m n : ℕ}

namespace language

structure translation (L₁ : language) (L₂ : language) :=
(fn : Π n, L₁.fn n → L₂.fn n)
(pr : Π n, L₁.pr n → L₂.pr n)
(fn_inj : ∀ n, function.injective (fn n))
(pr_inj : ∀ n, function.injective (pr n))

infix ` ⤳ᴸ `:25 := translation

protected def translation.refl : L ⤳ᴸ L :=
{ fn := λ _, id,
  pr := λ _, id,
  fn_inj := λ _, function.injective_id,
  pr_inj := λ _, function.injective_id }

protected def translation.comp (τ₁ : L₁ ⤳ᴸ L₂) (τ₂ : L₂ ⤳ᴸ L₃) : L₁ ⤳ᴸ L₃ :=
{ fn := λ n, τ₂.fn n ∘ τ₁.fn n,
  pr := λ n, τ₂.pr n ∘ τ₁.pr n,
  fn_inj := λ n, function.injective.comp (τ₂.fn_inj n) (τ₁.fn_inj n),
  pr_inj := λ n, function.injective.comp (τ₂.pr_inj n) (τ₁.pr_inj n) }

instance : has_add language := ⟨λ L₁ L₂ : language.{u}, ⟨λ n, L₁.fn n ⊕ L₂.fn n, λ n, L₁.pr n ⊕ L₂.pr n⟩⟩ 

section add
variables {L} {R}

instance add_to_string_fn [∀ n, has_to_string (L.fn n)] [∀ n, has_to_string (R.fn n)] (n) : has_to_string ((L + R).fn n) :=
⟨by { rintros (x | x), { exact to_string x }, { exact to_string x } }⟩

instance add_to_string_pr [∀ n, has_to_string (L.pr n)] [∀ n, has_to_string (R.pr n)] (n) : has_to_string ((L + R).pr n) :=
⟨by { rintros (x | x), { exact to_string x }, { exact to_string x } }⟩

def add_left : L ⤳ᴸ L + R :=
{ fn := λ n f, sum.inl f, pr := λ n r, sum.inl r,
  fn_inj := λ n, sum.inl_injective,
  pr_inj := λ n, sum.inl_injective }

def add_right : R ⤳ᴸ L + R :=
{ fn := λ n f, sum.inr f, pr := λ n r, sum.inr r,
  fn_inj := λ n, sum.inr_injective,
  pr_inj := λ n, sum.inr_injective }

end add

end language

namespace subterm
open language

structure hom (L₁ : language) (L₂ : language) :=
(func {} : Π {k m n}, L₁.fn k → (fin k → subterm L₂ m n) → subterm L₂ m n)
(to_fun : Π {m n}, subterm L₁ m n → subterm L₂ m n)
(map_var' : ∀ {m n x}, to_fun (#x : subterm L₁ m n) = #x)
(map_metavar' : ∀ {m n x}, to_fun (&x : subterm L₁ m n) = &x)
(map_function' : ∀ {k m n} (f : L₁.fn k) (v : fin k → subterm L₁ m n),
  to_fun (function f v) = func f (to_fun ∘ v))
(map_mlift' : ∀ {m n} (t : subterm L₁ m n), to_fun t.mlift = (to_fun t).mlift)
(map_push' : ∀ {m n} (t : subterm L₁ m (n + 1)), to_fun t.push = (to_fun t).push)
(map_pull' : ∀ {m n} (t : subterm L₁ (m + 1) n), to_fun t.pull = (to_fun t).pull)

instance {L₁ L₂ : language} :
  has_coe_to_fun (hom L₁ L₂) (λ _, Π {m n}, subterm L₁ m n → subterm L₂ m n) :=
⟨hom.to_fun⟩

namespace hom
variables {L₁ L₂} {m n} (τ : hom L₁ L₂)

@[simp] lemma map_var {m n x} : τ (#x : subterm L₁ m n) = #x := τ.map_var'

@[simp] lemma map_metavar {m n x} : τ (&x : subterm L₁ m n) = &x := τ.map_metavar'

lemma map_function {k m n} (f : L₁.fn k) (v : fin k → subterm L₁ m n) :
  τ (function f v) = func τ f (λ i, τ (v i)) := τ.map_function' f v

@[simp] lemma map_mlift {m n} (t : subterm L₁ m n) : τ t.mlift = (τ t).mlift := τ.map_mlift' t

@[simp] lemma map_push {m n} (t : subterm L₁ m (n + 1)) : τ t.push = (τ t).push := τ.map_push' t

@[simp] lemma map_pull {m n} (t : subterm L₁ (m + 1) n) : τ t.pull = (τ t).pull := τ.map_pull' t

end hom

@[simp] def of_fn_hom (fn : Π n, L₁.fn n → L₂.fn n) : subterm L₁ m n → subterm L₂ m n
| &x             := &x
| #x             := #x
| (function f v) := function (fn _ f) (λ i, of_fn_hom (v i))

def of_fn (fn : Π n, L₁.fn n → L₂.fn n) : hom L₁ L₂ :=
{ func := λ k m n f, function (fn _ f),
  to_fun := λ m n, @of_fn_hom _ _ m n fn,
  map_var' := by intros; refl,
  map_metavar' := by intros; refl,
  map_function' := by intros; simp,
  map_mlift' := by intros m n t; induction t; simp*,
  map_push' := by {intros m n t; induction t; simp*, case var : x { refine fin.last_cases _ _ x; simp } },
  map_pull' := by {intros m n t; induction t; simp*, case metavar : x { refine fin.cases _ _ x; simp } } }

def of_lhom (l : L₁ ⤳ᴸ L₂) : hom L₁ L₂ := of_fn l.fn

variables (l : L₁ ⤳ᴸ L₂)

@[simp] lemma of_lhom_map_function {k m n} (f : L₁.fn k) (v : fin k → subterm L₁ m n) :
  (of_lhom l) (function f v) = function (l.fn _ f) (λ i, of_lhom l (v i)) :=
by simp[of_lhom]; refl

variables {L R}

def left : subterm.hom L (L + R) := subterm.of_lhom add_left

def right : subterm.hom R (L + R) := subterm.of_lhom add_right

end subterm

namespace subformula
open language

structure hom (L₁ : language) (L₂ : language) :=
(hom : Π {m n}, subformula L₁ m n →ₗ subformula L₂ m n)
(map_univ' : ∀ {m n} (p : subformula L₁ m (n + 1)), hom (∀'p) = ∀' hom p)
(map_mlift' : ∀ {m n} (p : subformula L₁ m n), hom p.mlift = (hom p).mlift)
(map_push' : ∀ {m n} (p : subformula L₁ m (n + 1)), hom p.push = (hom p).push)
(map_pull' : ∀ {m n} (p : subformula L₁ (m + 1) n), hom p.pull = (hom p).pull)

instance {L₁ L₂ : language} :
  has_coe_to_fun (hom L₁ L₂) (λ _, Π {m n}, subformula L₁ m n →ₗ subformula L₂ m n) :=
⟨hom.hom⟩

namespace hom
variables (τ : subformula.hom L₁ L₂) {m}

@[simp] lemma map_univ {m n} (p : subformula L₁ m (n + 1)) : τ (∀'p) = ∀'τ p := τ.map_univ' p

@[simp] lemma map_ex {m n} (p : subformula L₁ m (n + 1)) : τ (∃'p) = ∃'τ p := by simp[ex_def]

@[simp] lemma map_mlift {m n} (p : subformula L₁ m n) : τ p.mlift = (τ p).mlift := τ.map_mlift' p

@[simp] lemma map_push {m n} (p : subformula L₁ m (n + 1)) : τ p.push = (τ p).push := τ.map_push' p

@[simp] lemma map_pull {m n} (p : subformula L₁ (m + 1) n) : τ p.pull = (τ p).pull := τ.map_pull' p

@[simp] lemma map_dummy {m n} (p : subformula L₁ m n) : τ p.dummy = (τ p).dummy :=
by simp[dummy]

@[simp] lemma map_univ_closure {m n} (p : subformula L₁ m n) : τ (∀'*p) = ∀'*(τ p) :=
by induction n; simp*

@[simp] lemma map_exists_closure {m n} (p : subformula L₁ m n) : τ (∃'*p) = ∃'*(τ p) :=
by induction n; simp*

@[reducible] def on_Theory (T : preTheory L₁ m) : preTheory L₂ m := (λ p, τ p) '' T

@[simp] lemma on_Theory_map_mlift {m} (T : preTheory L₁ m) : τ.on_Theory T.mlift = (τ.on_Theory T).mlift :=
by ext p; simp[on_Theory, preTheory.mlift]

class provable :=
(subst : ∀ {m} (T : preTheory L₁ m) (p t), τ.on_Theory T ⊢ ∀'τ p ⟶ τ (subst t p))
(eq_refl : ∀ {m} (T : preTheory L₁ m), τ.on_Theory T ⊢ ∀'τ (#0 =' #0))
(eq_symm : ∀ {m} (T : preTheory L₁ m), τ.on_Theory T ⊢ ∀' ∀'(τ (#0 =' #1) ⟶ τ (#1 =' #0)))
(eq_trans : ∀ {m} (T : preTheory L₁ m), τ.on_Theory T ⊢ ∀' ∀' ∀'(τ (#0 =' #1) ⟶ τ (#1 =' #2) ⟶ τ (#0 =' #2)))

end hom

variables (l : L₁ ⤳ᴸ L₂) {m}

@[simp] def of_lhom_hom : Π {n}, subformula L₁ m n → subformula L₂ m n
| n verum          := ⊤
| n (relation r v) := relation (l.pr _ r) (λ i, subterm.of_lhom l (v i))
| n (equal t u)    := subterm.of_lhom l t =' subterm.of_lhom l u
| n (imply p q)    := of_lhom_hom p ⟶ of_lhom_hom q
| n (neg p)        := ∼of_lhom_hom p
| n (fal p)        := ∀' of_lhom_hom p

@[simp] def of_lhom_hom_verum : of_lhom_hom l (⊤ : subformula L₁ m n) = ⊤ := by refl

@[simp] def of_lhom_hom_relation {k} (r : L₁.pr k) (v : fin k → subterm L₁ m n) :
  of_lhom_hom l (relation r v : subformula L₁ m n) = relation (l.pr _ r) (λ i, subterm.of_lhom l (v i)) := by refl

@[simp] def of_lhom_hom_equal (t u) :
  of_lhom_hom l (t =' u : subformula L₁ m n) = (subterm.of_lhom l t =' subterm.of_lhom l u) := by refl

@[simp] def of_lhom_hom_imply (p q : subformula L₁ m n) :
  of_lhom_hom l (p ⟶ q) = (of_lhom_hom l p ⟶ of_lhom_hom l q) := by refl

@[simp] def of_lhom_hom_neg (p : subformula L₁ m n) :
  of_lhom_hom l (∼p) = ∼of_lhom_hom l p := by refl

@[simp] def of_lhom_hom_fal (p : subformula L₁ m (n + 1)) :
  of_lhom_hom l (∀'p) = ∀'of_lhom_hom l p := by refl

@[simp] def mlift_of_lhom_hom : Π {n} (p : subformula L₁ m n), mlift (of_lhom_hom l p) = of_lhom_hom l (mlift p)
| n verum          := by simp[top_eq]; refl
| n (relation r v) := by simp
| n (equal t u)    := by simp[equal_eq]
| n (imply p q)    := by simp[imply_eq, mlift_of_lhom_hom p, mlift_of_lhom_hom q]
| n (neg p)        := by simp[neg_eq, mlift_of_lhom_hom p]
| n (fal p)        := by simp[fal_eq, mlift_of_lhom_hom p]

@[simp] def push_of_lhom_hom : Π {n} (p : subformula L₁ m (n + 1)), push (of_lhom_hom l p) = of_lhom_hom l (push p)
| n verum          := by simp[top_eq]; refl
| n (relation r v) := by simp
| n (equal t u)    := by simp[equal_eq]
| n (imply p q)    := by simp[imply_eq, push_of_lhom_hom p, push_of_lhom_hom q]
| n (neg p)        := by simp[neg_eq, push_of_lhom_hom p]
| n (fal p)        := by simp[fal_eq, push_of_lhom_hom p]
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.complexity)⟩]}

@[simp] def pull_of_lhom_hom : Π {n} (p : subformula L₁ (m + 1) n), pull (of_lhom_hom l p) = of_lhom_hom l (pull p)
| n verum          := by simp[top_eq]; refl
| n (relation r v) := by simp
| n (equal t u)    := by simp[equal_eq]
| n (imply p q)    := by simp[imply_eq, pull_of_lhom_hom p, pull_of_lhom_hom q]
| n (neg p)        := by simp[neg_eq, pull_of_lhom_hom p]
| n (fal p)        := by simp[fal_eq, pull_of_lhom_hom p]

def of_lhom : subformula.hom L₁ L₂ :=
{ hom := λ m n,
  { to_fun := of_lhom_hom l,
    map_neg' := λ p, by refl,
    map_imply' := λ p q, by refl,
    map_and' := λ p q, by refl,
    map_or' := λ p q, by refl,
    map_top' := by refl,
    map_bot' := by refl },
  map_univ' := λ m n p, by refl,
  map_mlift' := by simp,
  map_push' := by simp,
  map_pull' := by simp }

@[simp] lemma of_lhom_relation {k} (r : L₁.pr k) (v : fin k → subterm L₁ m n) :
  of_lhom l (relation r v) = relation (l.pr _ r) (λ i, (subterm.of_lhom l) (v i)) :=
by refl

@[simp] lemma of_lhom_equal (t u : subterm L₁ m n) :
  of_lhom l (t =' u : subformula L₁ m n) = (subterm.of_lhom l t =' subterm.of_lhom l u) :=
by refl

@[simp] lemma rank_of_lhom : ∀ {n} (p : subformula L₁ m n), (of_lhom l p).qr = p.qr
| n verum          := by simp[top_eq]
| n (relation r v) := by simp
| n (equal t u)    := by simp[equal_eq]
| n (imply p q)    := by simp[imply_eq, rank_of_lhom p, rank_of_lhom q]
| n (neg p)        := by simp[neg_eq, rank_of_lhom p]
| n (fal p)        := by simp[fal_eq, rank_of_lhom p]

@[simp] lemma of_lhom_is_open (p : subformula L₁ m n) : (of_lhom l p).is_open ↔ p.is_open :=
by simp[is_open]

@[simp] lemma complexity_of_lhom : ∀ {n} (p : subformula L₁ m n), (of_lhom l p).complexity = p.complexity
| n verum          := by simp[top_eq]
| n (relation r v) := by simp
| n (equal t u)    := by simp[equal_eq]
| n (imply p q)    := by simp[imply_eq, complexity_of_lhom p, complexity_of_lhom q]
| n (neg p)        := by simp[neg_eq, complexity_of_lhom p]
| n (fal p)        := by simp[fal_eq, complexity_of_lhom p]

variables {L R}

def left : subformula.hom L (L + R) := subformula.of_lhom add_left

def right : subformula.hom R (L + R) := subformula.of_lhom add_right

end subformula

namespace provable
variables (φ : subformula.hom L₁ L₂) {m} {T : preTheory L₁ m} {p : subformula L₁ m 0}
 
lemma tr (h : T ⊢ p) : φ.on_Theory T ⊢ φ p :=
begin
  apply rec_on h,
  { intros m T p b IH,
    have : φ.on_Theory T ⊢ ∀' 𝗡 (φ p), from generalize (by simpa using IH),
    simpa using this },
  { intros m T p q b₁ b₂ IH₁ IH₂, from (by simpa using IH₁) ⨀ IH₂ },
  { intros m T p hp, from by_axiom (set.mem_image_of_mem _ hp) },
  { simp },
  { intros, simp },
  { intros, simp },
  { intros, simp },
  { intros, simp,sorry  },
  { intros, simp },
  { intros, simp,  },
  { intros, simp, sorry },
  { intros, simp, sorry },
  { intros, simp, sorry },
  { intros, simp, sorry },
  { intros, simp, sorry },
  sorry
end

end provable

end fol