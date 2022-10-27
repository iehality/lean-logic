import lib

universe u

namespace pl
variables (A : Type u)

inductive formula : Type u
| atom  : A → formula
| verum : formula
| imply : formula → formula → formula
| neg   : formula → formula

variables {A}

instance : has_top (formula A) := ⟨formula.verum⟩

instance : has_arrow (formula A) := ⟨formula.imply⟩

instance : has_negation (formula A) := ⟨formula.neg⟩

attribute [pattern] has_negation.neg has_arrow.arrow

instance : has_bot (formula A) := ⟨⁻⊤⟩

instance : inhabited (formula A) := ⟨⊤⟩

@[simp] lemma formula.top_eq : @formula.verum A = (⊤) := rfl
@[simp] lemma formula.imply_eq : @formula.imply A = (⟶) := rfl
@[simp] lemma formula.neg_eq : @formula.neg A = has_negation.neg := rfl

@[reducible] def theory (A : Type u) := set (formula A)

def formula.and (p : formula A) (q : formula A) : formula A := ⁻(p ⟶ ⁻q)

instance : has_inf (formula A) := ⟨formula.and⟩

def formula.or (p : formula A) (q : formula A) : formula A := ⁻p ⟶ q

instance : has_sup (formula A) := ⟨formula.or⟩

@[simp] lemma formula.imply.inj' (p₁ q₁ p₂ q₂ : formula A) : p₁ ⟶ p₂ = q₁ ⟶ q₂ ↔ p₁ = q₁ ∧ p₂ = q₂ :=
⟨formula.imply.inj, by simp; exact congr_arg2 (⟶)⟩

@[simp] lemma formula.neg.inj' (p q : formula A) : ⁻p = ⁻q ↔ p = q := ⟨formula.neg.inj, congr_arg _⟩

@[simp] lemma formula.and.inj' (p₁ q₁ p₂ q₂ : formula A) : p₁ ⊓ p₂ = q₁ ⊓ q₂ ↔ p₁ = q₁ ∧ p₂ = q₂ :=
by simp[has_inf.inf, formula.and]

@[simp] lemma formula.or.inj' (p₁ q₁ p₂ q₂ : formula A) : p₁ ⊔ p₂ = q₁ ⊔ q₂ ↔ p₁ = q₁ ∧ p₂ = q₂ :=
by simp[has_sup.sup, formula.or]

namespace formula

@[simp] def rew : (A → formula A) → formula A → formula A
| s (atom a) := s a
| s ⊤        := ⊤
| s (p ⟶ q) := p.rew s ⟶ q.rew s
| s (⁻p)     := ⁻p.rew s

end formula

end pl