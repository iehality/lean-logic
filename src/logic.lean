import lib.lib provability

universes u

namespace logic
variables (F : Type*) [has_logic_symbol F] [axiomatic_classical_logic F]

@[reducible] def theory := set F

variables {F}

namespace theory
variables (T : theory F)

def mk (S : set F) : theory F := S

def consistent : Prop := ¬∃p : F, (T ⊢ p) ∧ (T ⊢ ⁻p) 

lemma consistent_def : consistent T ↔ ¬∃p : F, (T ⊢ p) ∧ (T ⊢ ⁻p) := by refl

open axiomatic_classical_logic axiomatic_classical_logic'
variables {T}

lemma consistent_iff_bot : consistent T ↔ ¬T ⊢ ⊥ :=
⟨by { simp[consistent_def], intros h A, have : ¬T ⊢ ⁻⊤, from h ⊤ (by simp), 
      have : T ⊢ ⁻⊤, from of_equiv A (by simp), contradiction },
 by { intros h, simp[consistent_def], intros p hp hnp,
      have : T ⊢ ⊥, from explosion hp hnp,
      exact h this }⟩

lemma not_consistent_iff_bot : ¬consistent T ↔ T ⊢ ⊥ :=
by simp[consistent_iff_bot]

lemma not_consistent_iff : ¬consistent T ↔ ∃p : F, (T ⊢ p) ∧ (T ⊢ ⁻p) :=
by simp[consistent_def]

instance : has_le (theory F) := ⟨λ T U, ∀ ⦃p : F⦄, T ⊢ p → U ⊢ p⟩

@[simp, refl] lemma le_refl (T : theory F) : T ≤ T := λ p h, h

@[trans] lemma le_trans {T₁ T₂ T₃ : theory F} :
  T₁ ≤ T₂ → T₂ ≤ T₃ → T₁ ≤ T₃ := λ le₁₂ le₂₃ p b, le₂₃ (le₁₂ b)

class extend (T₀ T : set F) := (le : T₀ ≤ T)

namespace extend

instance extend_refl (T : set F) : extend T T := ⟨λ p h, h⟩

@[trans] def extend.trans (T₁ T₂ T₃ : set F) [extend T₁ T₂]  [extend T₂ T₃] :
  extend T₁ T₃ := ⟨λ p b, extend.le (extend.le b : T₂ ⊢ p)⟩

end extend

def th (T : theory F) : theory F := {p | T ⊢ p}

end theory

end logic