import QL.FOL.semantics

universes u v

namespace fol
open_locale logic_symbol
variables (L : language.{u}) {m n : ℕ}

inductive uniform_subterm (n : ℕ) : Type u
| uvar  {} : ℕ → uniform_subterm
| var   {} : fin n → uniform_subterm
| function : ∀ {k}, L.fn k → (fin k → uniform_subterm) → uniform_subterm

@[reducible] def uniform_term := uniform_subterm L 0

inductive uniform_subformula : ℕ → Type u
| verum    {n} : uniform_subformula n
| relation {n} : ∀ {p}, L.pr p → (fin p → uniform_subterm L n) → uniform_subformula n
| imply    {n} : uniform_subformula n → uniform_subformula n → uniform_subformula n
| neg      {n} : uniform_subformula n → uniform_subformula n
| fal      {n} : uniform_subformula (n + 1) → uniform_subformula n

prefix `##`:max := uniform_subterm.var
prefix `&&`:max := uniform_subterm.uvar

namespace uniform_subterm
variables {L n}

@[simp] def arity : uniform_subterm L n → ℕ
| &&x            := x + 1
| ##x            := 0
| (function f v) := ⨆ᶠ i, (v i).arity

@[simp] def to_subterm : ∀ t : uniform_subterm L n, t.arity ≤ m → subterm L m n
| &&x                   h := &⟨x, h⟩
| ##x                   h := #x 
| (@function L n k f v) h := subterm.function f (λ i, to_subterm (v i) (by { haveI: inhabited (fin k) := ⟨i⟩, simp at h, exact h i}))

section subst

@[simp] def subst (t : uniform_subterm L n) : uniform_subterm L (n + 1) → uniform_subterm L n
| &&x            := &&x
| ##x            := (var <* t) x
| (function f v) := function f (λ i, subst $ v i)

@[simp] def lift : uniform_subterm L n → uniform_subterm L (n + 1)
| &&x            := &&x
| ##x            := ##x.succ
| (function f v) := function f (λ i, (v i).lift)

end subst

section semantics
variables (S : Structure L) {m} {m₁ m₂ : ℕ} {n} (me : ℕ → S) (e : fin n → S)

@[simp] def val (me : ℕ → S) (e : fin n → S) : uniform_subterm L n → S
| &&x           := me x
| ##x           := e x
| (function f v) := S.fn f (λ i, (v i).val)

@[simp] lemma val_rew (u : uniform_subterm L n) (me : ℕ → S) (e : fin n → S) : ∀ (t : uniform_subterm L (n + 1)),
  (subst u t).val S me e = t.val S me (e <* val S me e u)
| &&x            := by simp
| ##x            := by simp; refine fin.last_cases _ _ x; simp
| (function f v) := by simp; refine congr_arg _ (by ext i; exact val_rew (v i))

@[simp] lemma val_lift (x : S) (t : uniform_subterm L n) :
  t.lift.val S me (x *> e) = t.val S me e :=
by induction t; simp*

end semantics

end uniform_subterm

namespace subterm
open uniform_subterm
variables {L m n}

@[simp] def uniform : subterm L m n → uniform_subterm L n
| &x             := uniform_subterm.uvar x 
| #x             := uniform_subterm.var x 
| (function f v) := uniform_subterm.function f (λ i, (v i).uniform)

@[simp] lemma uniform_mlift (t : subterm L m n) : t.mlift.uniform = t.uniform :=
by induction t; simp*

@[simp] lemma uniform_to_subterm (t : subterm L m n) (h) : t.uniform.to_subterm h = t :=
by induction t; simp*

@[simp] lemma to_subterm_uniform (t : uniform_subterm L n) (h : t.arity ≤ m) : (t.to_subterm h).uniform = t :=
by induction t; simp*

@[simp] lemma subterm_arity (t : subterm L m n) : t.uniform.arity ≤ m :=
by { induction t; simp*, case metavar : i { exact nat.succ_le_iff.mpr i.property } }

section subst

@[simp] lemma uniform_subst (u : subterm L m n) (t : subterm L m (n + 1)) :
  (subst u t).uniform = uniform_subterm.subst u.uniform t.uniform :=
by { induction t; simp*, case var : x { refine fin.last_cases _ _ x; simp } }

@[simp] lemma uniform_push (t : subterm L m (n + 1)) :
  (push t).uniform = uniform_subterm.subst (&&m) t.uniform :=
by { induction t; simp*, case var : x { refine fin.last_cases _ _ x; simp } }

lemma uniform_lift (t : subterm L m n) :
  t.lift.uniform = t.uniform.lift :=
by induction t; simp*

end subst

section semantics
variables (S : Structure L) {m} {m₁ m₂ : ℕ} {n} (me : ℕ → S) (e : fin n → S)

@[simp] lemma uniform_val (t : subterm L m n) : t.uniform.val S me e = t.val S (λ i, me i) e :=
by induction t; simp*

end semantics

end subterm

namespace uniform_subformula
variables {L n}

@[simp] def arity : Π {n}, uniform_subformula L n → ℕ
| n verum          := 0
| n (relation r v) := ⨆ᶠ i, (v i).arity
| n (imply p q)    := max p.arity q.arity
| n (neg p)        := p.arity
| n (fal p)        := p.arity

@[simp] def to_subformula : ∀ {n} (p : uniform_subformula L n), p.arity ≤ m → subformula L m n
| n verum          h := ⊤
| n (relation r v) h := subformula.relation r (λ i, (v i).to_subterm (by show (v i).arity ≤ m; simp at h; exact h i))
| n (imply p q)    h := have h : p.arity ≤ m ∧ q.arity ≤ m, by simpa using h, p.to_subformula h.1 ⟶ q.to_subformula h.2
| n (neg p)        h := ∼p.to_subformula (by simpa using h)
| n (fal p)        h := ∀'p.to_subformula (by simpa using h)

end uniform_subformula

namespace subformula
open uniform_subformula
variables {L m n}

@[simp] def uniform : Π {n}, subformula L m n → uniform_subformula L n
| n verum          := uniform_subformula.verum
| n (relation r v) := uniform_subformula.relation r (subterm.uniform ∘ v)
| n (imply p q)    := uniform_subformula.imply p.uniform q.uniform
| n (neg p)        := uniform_subformula.neg p.uniform
| n (fal p)        := uniform_subformula.fal p.uniform

@[simp] lemma uniform_mlift (p : subformula L m n) : p.mlift.uniform = p.uniform :=
by simp[mlift]; induction p; simp[mlift', ←fal_eq, ←neg_eq, ←top_eq, ←imply_eq, (∘), *]

@[simp] lemma uniform_to_subterm (p : subformula L m n) (h) : p.uniform.to_subformula h = p :=
by induction p; simp*; refl

@[simp] lemma to_subterm_uniform (p : uniform_subformula L n) (h : p.arity ≤ m) : (p.to_subformula h).uniform = p :=
by induction p; simp[←fal_eq, ←neg_eq, ←top_eq, ←imply_eq, (∘), *]

end subformula

end fol