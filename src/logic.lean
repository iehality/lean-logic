import lib.lib provability

universes u v

open_locale logic_symbol

section prop

instance : has_logic_symbol Prop :=
{ arrow := (→),
  neg := not }

@[simp] lemma top_to_true : (⊤ : Prop) ↔ true := by refl

@[simp] lemma bot_to_false : (⊥ : Prop) ↔ false := by refl

@[simp] lemma arrow_to_to (p q : Prop) : (p ⟶ q) ↔ (p → q) := by refl

@[simp] lemma lrarrow_to_iff (p q : Prop) : (p ⟷ q) ↔ (p ↔ q) := by simp[lrarrow_def]; exact iff_def.symm

@[simp] lemma neg_to_not (p : Prop) : ∼p ↔ ¬p := by refl

@[simp] lemma prop_finitary_conj {n} (p : finitary Prop n) : finitary.conjunction n p ↔ ∀ x, p x :=
by{ induction n with n IH, { simp },
    { simp[IH], split,
      { rintros ⟨hlast, h⟩, intros x, refine fin.last_cases hlast h x },
      { rintros h, simp[h] } } }

@[simp] lemma prop_finitary_disj {n} (p : finitary Prop n) : finitary.disjunction n p ↔ ∃ x, p x :=
by{ induction n with n IH, { simp },
    { simp[IH], split,
      { rintros (⟨_, h⟩ | hlast), { exact ⟨_, h⟩ }, { exact ⟨_, hlast⟩ } },
      { rintros ⟨x, h⟩, rcases fin.eq_last_or_eq_cast_succ x with (rfl | ⟨x, rfl⟩),
        { exact or.inr h }, { exact or.inl ⟨x, h⟩ } } } }

end prop

namespace logic

@[reducible] def Theory (F : Type*) [has_logic_symbol F] := set F

variables {F : Type*} [has_logic_symbol F] [axiomatic_classical_logic F]

namespace Theory
variables (T : Theory F)

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

variables (F)

class sound (𝓢 : Type*) [semantics F 𝓢] :=
(soundness : ∀ {T : Theory F} {p}, T ⊢ p → semantics.consequence 𝓢 T p)

section sound
open sound
variables {F} {𝓢 : Type*} [semantics F 𝓢] [sound F 𝓢] {S : 𝓢}

theorem Structure_consistent (h : ¬S ⊧ (⊥ : F)) {T : Theory F} : S ⊧ T → Theory.consistent T :=
by { contrapose, simp[Theory.consistent], intros p hp₁ hp₂ hyp,
     have : T ⊢ (⊥ : F), from axiomatic_classical_logic'.explosion hp₁ hp₂,
     exact h (soundness this hyp) }

variables (S)

lemma tautology_of_tautology (p : F) (h : ⬝⊢ p) : S ⊧ p :=
by { have : semantics.consequence 𝓢 ∅ p, from soundness h, exact this (show S ⊧ ∅, by simp) }

end sound

end logic
