import lib.lib logic logic.encodable.basic translation

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

lemma bot_def : (⊥ : formula A) = ∼⊤ := rfl

@[simp] lemma top_eq : @formula.verum A = (⊤) := rfl

@[simp] lemma imply_eq : @formula.imply A = (⟶) := rfl

@[simp] lemma neg_eq : @formula.neg A = has_negation.neg := rfl

@[simp] lemma imply.inj' (p₁ q₁ p₂ q₂ : formula A) : p₁ ⟶ p₂ = q₁ ⟶ q₂ ↔ p₁ = q₁ ∧ p₂ = q₂ :=
⟨formula.imply.inj, by simp; exact congr_arg2 (⟶)⟩

@[simp] lemma neg.inj' (p q : formula A) : ∼p = ∼q ↔ p = q := ⟨formula.neg.inj, congr_arg _⟩

@[simp] lemma and.inj' (p₁ q₁ p₂ q₂ : formula A) : p₁ ⊓ p₂ = q₁ ⊓ q₂ ↔ p₁ = q₁ ∧ p₂ = q₂ :=
by simp[has_inf.inf, formula.and]

@[simp] lemma or.inj' (p₁ q₁ p₂ q₂ : formula A) : p₁ ⊔ p₂ = q₁ ⊔ q₂ ↔ p₁ = q₁ ∧ p₂ = q₂ :=
by simp[has_sup.sup, formula.or]

end formula

end pl