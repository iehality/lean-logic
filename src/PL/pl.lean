import lib.lib logic logic.encodable.basic

universe u

namespace pl
open_locale logic_symbol
variables (A : Type u)

inductive formula : Type u
| atom  : A → formula
| verum : formula
| imply : formula → formula → formula
| neg   : formula → formula

variables {A}

namespace formula

def and (p : formula A) (q : formula A) : formula A := (p.imply q.neg).neg

def or (p : formula A) (q : formula A) : formula A := p.neg.imply q

instance : has_logic_symbol (formula A) :=
{ bot := verum.neg,
  top := verum,
  sup := or,
  inf := and,
  arrow := imply,
  neg := neg }

attribute [pattern] has_negation.neg has_arrow.arrow
end formula

instance : inhabited (formula A) := ⟨⊤⟩

abbreviation Theory (A : Type u) := logic.Theory (formula A)

namespace formula

lemma bot_def : (⊥ : formula A) = ⁻⊤ := rfl

@[simp] lemma top_eq : @formula.verum A = (⊤) := rfl

@[simp] lemma imply_eq : @formula.imply A = (⟶) := rfl

@[simp] lemma neg_eq : @formula.neg A = has_negation.neg := rfl

@[simp] lemma imply.inj' (p₁ q₁ p₂ q₂ : formula A) : p₁ ⟶ p₂ = q₁ ⟶ q₂ ↔ p₁ = q₁ ∧ p₂ = q₂ :=
⟨formula.imply.inj, by simp; exact congr_arg2 (⟶)⟩

@[simp] lemma neg.inj' (p q : formula A) : ⁻p = ⁻q ↔ p = q := ⟨formula.neg.inj, congr_arg _⟩

@[simp] lemma and.inj' (p₁ q₁ p₂ q₂ : formula A) : p₁ ⊓ p₂ = q₁ ⊓ q₂ ↔ p₁ = q₁ ∧ p₂ = q₂ :=
by simp[has_inf.inf, formula.and]

@[simp] lemma or.inj' (p₁ q₁ p₂ q₂ : formula A) : p₁ ⊔ p₂ = q₁ ⊔ q₂ ↔ p₁ = q₁ ∧ p₂ = q₂ :=
by simp[has_sup.sup, formula.or]

end formula

section encode
open formula
variables (A)

def label := A ⊕ unit ⊕ unit ⊕ unit

def arity : label A → Type
| (sum.inl a)                      := empty
| (sum.inr $ sum.inl ())           := empty
| (sum.inr $ sum.inr $ sum.inl ()) := bool
| (sum.inr $ sum.inr $ sum.inr ()) := unit

def W := W_type (arity A)

variables {A}

def W.to_formula : W A → formula A
| ⟨sum.inl a, f⟩                      := atom a
| ⟨sum.inr $ sum.inl (), f⟩           := ⊤
| ⟨sum.inr $ sum.inr $ sum.inl (), f⟩ := W.to_formula (f ff) ⟶ W.to_formula (f tt)
| ⟨sum.inr $ sum.inr $ sum.inr (), f⟩ := ⁻W.to_formula (f ())

def frfrf (α : Type*) : empty → α := by refine empty.rec (λ (n : empty), α)

def formula.to_W : formula A → W A
| (atom a) := ⟨sum.inl a, by rintros ⟨⟩⟩
| ⊤        := ⟨sum.inr $ sum.inl (), by rintros ⟨⟩⟩
| (p ⟶ q) := ⟨sum.inr $ sum.inr $ sum.inl (), by { rintros (_ | _), { exact p.to_W }, { exact q.to_W } }⟩
| (⁻p) := ⟨sum.inr $ sum.inr $ sum.inr (), λ _, p.to_W⟩

def formula_equiv_W : equiv (formula A) (W A) :=
{ to_fun := formula.to_W,
  inv_fun := W.to_formula,
  left_inv := by intros p; induction p; simp[formula.to_W, W.to_formula, *],
  right_inv := by { intros w, induction w with a f IH, rcases a with (_ | _ | _ | _),
    { simp[formula.to_W, W.to_formula, *], congr, exact funext (by rintros ⟨⟩) },
    { rcases a, simp[formula.to_W, W.to_formula], congr, exact funext (by rintros ⟨⟩) },
    { rcases a, simp[formula.to_W, W.to_formula, IH], congr, exact funext (by rintros (_ | _); simp) },
    { rcases a, simp[formula.to_W, W.to_formula, IH], congr, exact funext (by rintros ⟨⟩; refl) } } }

instance : Π i, fintype (arity A i)
| (sum.inl a)                      := show fintype empty, from fintype.of_is_empty
| (sum.inr $ sum.inl ())           := show fintype empty, from fintype.of_is_empty
| (sum.inr $ sum.inr $ sum.inl ()) := bool.fintype
| (sum.inr $ sum.inr $ sum.inr ()) := unit.fintype

instance : Π i, encodable (arity A i)
| (sum.inl a)                      := show encodable empty, from is_empty.to_encodable
| (sum.inr $ sum.inl ())           := show encodable empty, from is_empty.to_encodable
| (sum.inr $ sum.inr $ sum.inl ()) := bool.encodable
| (sum.inr $ sum.inr $ sum.inr ()) := punit.encodable

variables [encodable A]

instance : encodable (label A) := sum.encodable

instance : encodable (W A) := W_type.encodable

instance : encodable (formula A) := encodable.of_equiv (W A) formula_equiv_W

end encode

end pl