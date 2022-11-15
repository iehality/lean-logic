import PL.deduction translation

universes u

namespace pl
open_locale logic_symbol
open formula logic
variables (A : Type u)

structure Structure := (val : A → Prop)

variables {A} (S : Structure A)
namespace formula

@[simp] def val' : formula A → Prop
| (atom a) := S.val a
| ⊤        := true
| (p ⟶ q) := p.val' → q.val'
| (∼p)     := ¬p.val'

def val : formula A →ₗ Prop :=
{ to_fun := formula.val' S,
  map_neg' := by simp,
  map_imply' := by simp,
  map_and' := by intros; unfold has_inf.inf; simp[formula.and]; refl,
  map_or' := by intros; unfold has_sup.sup; simp[formula.or, ←or_iff_not_imp_left]; refl,
  map_top' := by refl,
  map_bot' := by unfold has_bot.bot; simp; exact not_false }

variables {S}

@[simp] lemma val_app (a : A) : val S (atom a) =  S.val a := rfl

end formula

open formula

instance : semantics (formula A) (Structure A) := ⟨λ S p, val S p⟩

abbreviation Satisfiable (T : Theory A) : Prop := semantics.Satisfiable (Structure A) T

lemma models_def (S : Structure A) (p : formula A) : S ⊧ p ↔ formula.val S p :=
by refl 

instance : has_double_turnstile (Theory A) (formula A) := ⟨semantics.consequence (Structure A)⟩

lemma consequence_def {T : Theory A} {p : formula A} :
  T ⊧ p ↔ semantics.consequence (Structure A) T p := by refl

variables {T : Theory A} {p : formula A}

lemma soundness (b : T ⊢ p) : T ⊧ p :=
begin
  apply rec'_on b,
  { intros p q hpq hp IHpq IHp S h, exact (IHpq h) (IHp h) },
  { intros p hp S h, exact h hp },
  { intros S hS, simp[models_def] },
  { intros p q S hS h₁ h₂, exact h₁},
  { intros p q r S hS h₁ h₂ h₃, exact h₁ h₃ (h₂ h₃) },
  { intros p q S hS h₁ h₂, exact not_imp_not.mp h₁ h₂ }
end

instance : sound (formula A) (Structure A) := ⟨λ _ _, soundness⟩

namespace Structure
variables {S}

@[simp] lemma models_verum : S ⊧ (⊤ : formula A) := by simp[models_def]

@[simp] lemma models_falsum : ¬S ⊧ (⊥ : formula A) := by simp[models_def, bot_def]

@[simp] lemma models_imply {p q : formula A} : S ⊧ p ⟶ q ↔ (S ⊧ p → S ⊧ q) :=
by refl

@[simp] lemma models_not {p : formula A} : S ⊧ ∼p ↔ ¬S ⊧ p :=
by refl

end Structure

namespace completeness
open logic.Theory.consistent logic.semantics
variables {T}

def model (T : Theory A) : Structure A := ⟨λ a, atom a ∈ maximal T⟩

lemma model_models_iff (consis : T.consistent) : p ∈ maximal T ↔ model T ⊧ p :=
begin
  induction p,
  case atom { simp[models_def, model] },
  case verum { simp[models_def], refine (mem_maximal_iff consis).mpr (by simp) },
  case imply : p q IH₁ IH₂ { simp[imply_mem_maximal_iff consis, IH₁, IH₂] },
  case neg : p IH { simp[neg_mem_maximal_iff consis, IH] }
end

lemma model_models (consis : T.consistent) : model T ⊧ T := λ p hp,
(model_models_iff consis).mp (ss_maximal consis hp)

theorem consistent_iff_satisfiable : Theory.consistent T ↔ Satisfiable T :=
⟨λ consis,  ⟨_, model_models consis⟩, by { rintros ⟨M, hM⟩, by { exact Structure_consistent (by simp) hM }}⟩

theorem completeness {p : formula A} : T ⊢ p ↔ T ⊧ p :=
⟨soundness, by {
  simp[Theory.provable_iff_inconsistent, consistent_iff_satisfiable], rintros h ⟨S, hS⟩,
  have l : ¬val S p ∧ S ⊧ T, by simpa[models_def] using hS,
  have : S ⊧ p, from h l.2,
  have : ¬S ⊧ p, from l.1,
  contradiction }⟩

end completeness

end pl