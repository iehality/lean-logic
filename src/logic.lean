import lib.lib provability

universes u v

open_locale logic_symbol

namespace logic

@[reducible] def Theory (F : Type*) [has_logic_symbol F] := set F

variables {F : Type*} [has_logic_symbol F]

namespace Theory
variables [axiomatic_classical_logic F] (T : Theory F) 

def mk (S : set F) : Theory F := S

def consistent : Prop := ¬∃p : F, (T ⊢ p) ∧ (T ⊢ ∼p)

class Consistent (T : Theory F) :=
(consis : consistent T)

lemma consistent_def : consistent T ↔ ¬∃p : F, (T ⊢ p) ∧ (T ⊢ ∼p) := by refl

open axiomatic_classical_logic axiomatic_classical_logic'
variables {T}

lemma consistent_iff_bot : consistent T ↔ ¬T ⊢ ⊥ :=
⟨by { simp[consistent_def], intros h A, have : ¬T ⊢ ∼⊤, from h ⊤ (by simp), 
      have : T ⊢ ∼⊤, from of_equiv A (by simp), contradiction },
 by { intros h, simp[consistent_def], intros p hp hnp,
      have : T ⊢ ⊥, from explosion hp hnp,
      exact h this }⟩

lemma not_consistent_iff_bot : ¬consistent T ↔ T ⊢ ⊥ :=
by simp[consistent_iff_bot]

lemma not_consistent_iff : ¬consistent T ↔ ∃p : F, (T ⊢ p) ∧ (T ⊢ ∼p) :=
by simp[consistent_def]

instance : has_le (Theory F) := ⟨λ T U, ∀ ⦃p : F⦄, T ⊢ p → U ⊢ p⟩

@[simp] lemma le_refl (T : Theory F) : T ≤ T := λ p h, h

@[trans] lemma le_trans {T₁ T₂ T₃ : Theory F} :
  T₁ ≤ T₂ → T₂ ≤ T₃ → T₁ ≤ T₃ := λ le₁₂ le₂₃ p b, le₂₃ (le₁₂ b)

class extend (T₀ T : set F) := (le : T₀ ≤ T)

namespace extend

instance extend_refl (T : set F) : extend T T := ⟨λ p h, h⟩

def of_ss {T U : Theory F} (ss : T ⊆ U) : extend T U :=
⟨by intros p h; exact weakening ss h⟩

@[trans] def extend.trans (T₁ T₂ T₃ : set F) [extend T₁ T₂]  [extend T₂ T₃] :
  extend T₁ T₃ := ⟨λ p b, extend.le (extend.le b : T₂ ⊢ p)⟩

lemma by_axiom (T₁ T₂ : set F) [extend T₁ T₂] {p : F} (hp : p ∈ T₁) : T₂ ⊢ p :=
extend.le (axiomatic_classical_logic'.by_axiom hp)

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

lemma Models_def {T : Theory F} : S ⊧ T ↔ ∀ p ∈ T, S ⊧ p := by refl

variables (𝓢)

def valid (p : F) : Prop := ∀ S : 𝓢, S ⊧ p

def satisfiable (p : F) : Prop := ∃ S : 𝓢, S ⊧ p

def Valid (T : Theory F) : Prop := ∀ S : 𝓢, S ⊧ T

def Satisfiable (T : Theory F) : Prop := ∃ S : 𝓢, S ⊧ T

def toutology (p : F) : Prop := ∀ ⦃S : 𝓢⦄, S ⊧ p

def consequence (T : Theory F) (p : F) : Prop := ∀ ⦃S : 𝓢⦄, S ⊧ T → S ⊧ p

variables {𝓢} {S} (T U : Theory F)

@[simp] lemma models_empty : S ⊧ (∅ : Theory F) := λ _, by simp

@[simp] lemma models_of_ss {U T : Theory F} (ss : U ⊆ T) : S ⊧ T → S ⊧ U := λ h p hp,
h (ss hp)

@[simp] lemma models_union {T U : Theory F} : S ⊧ T ∪ U ↔ S ⊧ T ∧ S ⊧ U :=
⟨λ h, ⟨λ p hp, h (set.mem_union_left U hp), λ p hp, h (set.mem_union_right T hp)⟩,
  by { rintros ⟨hT, hU⟩ p (hp | hp), { exact hT hp}, { exact hU hp } }⟩

@[simp] lemma models_insert {T : Theory F} {p : F} : S ⊧ insert p T ↔ S ⊧ p ∧ S ⊧ T :=
by simp[Models_def]

@[simp] lemma models_Union {ι} {T : ι → Theory F} : S ⊧ (⋃ n, T n) ↔ ∀ n, S ⊧ T n :=
by simp[Models_def]; refine ⟨λ h i p, h p i, λ h p i, h i p⟩

lemma Satisfiable_of_ss {T U : Theory F} (ss : T ⊆ U) : Satisfiable 𝓢 U → Satisfiable 𝓢 T :=
by rintros ⟨S, hS⟩; refine ⟨S, by { intros p hp,refine hS (ss hp) }⟩

variables (F 𝓢)

class nontrivial :=
(verum : ∀ S : 𝓢, S ⊧ (⊤ : F))
(falsum : ∀ S : 𝓢, ¬S ⊧ (⊥ : F))

attribute [simp] nontrivial.verum nontrivial.falsum

end semantics

variables (F) [axiomatic_classical_logic F]

class sound (𝓢 : Type*) [semantics F 𝓢] :=
(soundness : ∀ {T : Theory F} {p}, T ⊢ p → semantics.consequence 𝓢 T p)

namespace sound
variables {F} {𝓢 : Type*} [semantics F 𝓢] [sound F 𝓢] {S : 𝓢}


theorem consistent_of_Satisfiable [semantics.nontrivial F 𝓢] {T : Theory F} : semantics.Satisfiable 𝓢 T → Theory.consistent T :=
begin
  rintros ⟨S, hS⟩,
  by_contradiction A,
  have : T ⊢ ⊥, from Theory.not_consistent_iff_bot.mp A,
  exact semantics.nontrivial.falsum S (soundness this hS)
end

variables (S)

lemma tautology_of_tautology (p : F) (h : ⬝⊢ p) : S ⊧ p :=
by { have : semantics.consequence 𝓢 ∅ p, from soundness h, exact this (show S ⊧ ∅, by simp) }

end sound

class complete (𝓢 : Type*) [semantics F 𝓢] extends sound F 𝓢  :=
(completeness' : ∀ {T : Theory F} {p}, semantics.consequence 𝓢 T p → T ⊢ p)

namespace complete
variables {F} {𝓢 : Type*} [semantics F 𝓢] [complete F 𝓢] {S : 𝓢}

theorem completeness {T : Theory F} {p} : T ⊢ p ↔ semantics.consequence 𝓢 T p :=
⟨sound.soundness, completeness'⟩

theorem consistent_iff_Satisfiable [semantics.nontrivial F 𝓢] {T : Theory F} : Theory.consistent T ↔ semantics.Satisfiable 𝓢 T :=
⟨by { contrapose, intros h,
  have : semantics.consequence 𝓢 T ⊥, { intros S hS, exfalso, exact h ⟨S, hS⟩ },
  have : T ⊢ ⊥, from completeness.mpr this,
  exact Theory.not_consistent_iff_bot.mpr this }, sound.consistent_of_Satisfiable⟩

end complete

end logic
