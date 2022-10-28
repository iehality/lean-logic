import lib.lib provability

universes u

open_locale logic_symbol

namespace logic

@[reducible] def Theory (F : Type*) [has_logic_symbol F] := set F

variables {F : Type*} [has_logic_symbol F] [axiomatic_classical_logic F]

namespace Theory
variables (T : Theory F)

def mk (S : set F) : Theory F := S

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

instance : has_le (Theory F) := ⟨λ T U, ∀ ⦃p : F⦄, T ⊢ p → U ⊢ p⟩

@[simp] lemma le_refl (T : Theory F) : T ≤ T := λ p h, h

@[trans] lemma le_trans {T₁ T₂ T₃ : Theory F} :
  T₁ ≤ T₂ → T₂ ≤ T₃ → T₁ ≤ T₃ := λ le₁₂ le₂₃ p b, le₂₃ (le₁₂ b)

class extend (T₀ T : set F) := (le : T₀ ≤ T)

namespace extend

instance extend_refl (T : set F) : extend T T := ⟨λ p h, h⟩

@[trans] def extend.trans (T₁ T₂ T₃ : set F) [extend T₁ T₂]  [extend T₂ T₃] :
  extend T₁ T₃ := ⟨λ p b, extend.le (extend.le b : T₂ ⊢ p)⟩

end extend

def th (T : Theory F) : Theory F := {p | T ⊢ p}

end Theory

variables (F)

class semantics (𝓢 : Type*) :=
(models : 𝓢 → F → Prop)

namespace semantics
variables {F} {𝓢 : Type*} [semantics F 𝓢] (S : 𝓢)

instance : has_double_turnstile 𝓢 F := ⟨models⟩

instance : has_double_turnstile 𝓢 (Theory F) := ⟨λ S T, ∀ ⦃p⦄, p ∈ T → S ⊧ p⟩

variables {S}

def Models_def {T : Theory F} : S ⊧ T ↔ ∀ p ∈ T, S ⊧ p := by refl

variables (𝓢)

def satisfiable (p : F) : Prop := ∃ S : 𝓢, S ⊧ p

def Satisfiable (T : Theory F) : Prop := ∃ S : 𝓢, S ⊧ T

def toutology (p : F) : Prop := ∀ ⦃S : 𝓢⦄, S ⊧ p

def consequence (T : Theory F) (p : F) : Prop := ∀ ⦃S : 𝓢⦄, S ⊧ T → S ⊧ p

variables {𝓢} {S} (T U : Theory F)

@[simp] lemma models_empty : S ⊧ (∅ : Theory F) := λ _, by simp

@[simp] lemma models_union : S ⊧ T ∪ U ↔ S ⊧ T ∧ S ⊧ U :=
⟨λ h, ⟨λ p hp, h (set.mem_union_left U hp), λ p hp, h (set.mem_union_right T hp)⟩,
  by { rintros ⟨hT, hU⟩ p (hp | hp), { exact hT hp}, { exact hU hp } }⟩

@[simp] lemma models_insert {T : Theory F} {p : F} : S ⊧ insert p T ↔ S ⊧ p ∧ S ⊧ T :=
by simp[Models_def]

@[simp] lemma models_Union {ι} {T : ι → Theory F} : S ⊧ (⋃ n, T n) ↔ ∀ n, S ⊧ T n :=
by simp[Models_def]; refine ⟨λ h i p, h p i, λ h p i, h i p⟩

end semantics

def soundness (𝓢 : Type*) [semantics F 𝓢] : Prop :=
  ∀ {T : Theory F} {p}, T ⊢ p → semantics.consequence 𝓢 T p

def complete (𝓢 : Type*) [semantics F 𝓢] : Prop :=
  ∀ {T : Theory F} {p}, T ⊢ p ↔ semantics.consequence 𝓢 T p

end logic