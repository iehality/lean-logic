import PL.pl provability

universe u

namespace pl
open formula
variables {A : Type u}

inductive proof : theory A → formula A → Type u
| mdp : ∀ {T p q}, proof T (p ⟶ q) → proof T p → proof T q
| by_axiom : ∀ {T p}, p ∈ T → proof T p
| verum : ∀ {T}, proof T ⊤
| imply₁ : ∀ {T p q}, proof T (p ⟶ q ⟶ p)
| imply₂ : ∀ {T p q r}, proof T ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r)
| contraposition : ∀ {T p q}, proof T ((⁻p ⟶ ⁻q) ⟶ q ⟶ p)

def provable (T : theory A) (p : formula A) : Prop := nonempty (proof T p)

instance : axiomatic_classical_logic' (formula A) :=
{ turnstile := provable,
  classical := λ T,
  { modus_ponens := λ p q ⟨bpq⟩ ⟨bp⟩, ⟨bpq.mdp bp⟩,
    imply₁ := λ p q, ⟨proof.imply₁⟩, 
    imply₂ := λ p q r, ⟨proof.imply₂⟩,
    contraposition := λ p q, ⟨proof.contraposition⟩,
    provable_top := ⟨proof.verum⟩,
    bot_eq := by refl,
    and_def := λ p q, rfl,
    or_def := λ p q, rfl },
  by_axiom := λ T p mem, ⟨proof.by_axiom mem⟩ }

open axiomatic_classical_logic' axiomatic_classical_logic



end pl