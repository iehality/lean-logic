import QL.FOL.deduction

universes u v
open_locale logic_symbol

namespace fol
open logic subformula

structure Structure (L : language.{u}) :=
(dom : Type u)
(fn : ∀ {n}, L.fn n → (fin n → dom) → dom)
(pr : ∀ {n}, L.pr n → (fin n → dom) → Prop)

instance {L : language} : has_coe_to_sort (Structure L) (Type*) := ⟨Structure.dom⟩

variables {L : language.{u}} {μ : Type v} {μ₁ : Type*} {μ₂ : Type*} {S : Structure L}

variables (S) {n : ℕ}

open subterm subformula

namespace  subterm
variables {n} (Φ : μ → S) (e : fin n → S)

@[simp] def val (Φ : μ → S) (e : fin n → S) : subterm L μ n → S
| (&x)           := Φ x
| (#x)           := e x
| (function f v) := S.fn f (λ i, (v i).val)

lemma val_rew (s : μ₁ → subterm L μ₂ n) (Φ : μ₂ → S) (e : fin n → S) (t : subterm L μ₁ n) :
  (rew s t).val S Φ e = t.val S (λ x, val S Φ e (s x)) e :=
by induction t; simp*

lemma val_map (f : μ₁ → μ₂) (Φ : μ₂ → S) (e : fin n → S) (t : subterm L μ₁ n) :
  (map f t).val S Φ e = t.val S (λ x, Φ (f x)) e :=
by simp[map, val_rew]

lemma val_subst (u : subterm L μ n) (t : subterm L μ (n + 1)) :
  (subst u t).val S Φ e = t.val S Φ (e <* u.val S Φ e) :=
by { induction t; simp*, case var : x { refine fin.last_cases _ _ x; simp } }

lemma val_lift (x : S) (t : subterm L μ n) :
  t.lift.val S Φ (x *> e) = t.val S Φ e :=
by induction t; simp*

section bounded_subterm
variables {m : ℕ} {Ψ : fin m → S}

lemma val_mlift (x : S) (t : bounded_subterm L m n) :
  t.mlift.val S (Ψ <* x) e = t.val S Ψ e :=
by simp[mlift, val_rew]; congr; ext x; simp

lemma val_push (x : S) (e : fin n → S) (t : bounded_subterm L m (n + 1)) :
  val S (Ψ <* x) e t.push = val S Ψ (e <* x) t :=
by { induction t; simp*, case var : u { refine fin.last_cases _ _ u; simp } }

lemma val_pull (x : S) (e : fin n → S) (t : bounded_subterm L (m + 1) n) :
  val S Ψ (e <* x) t.pull = val S (Ψ <* x) e t :=
by { induction t; simp*, case metavar : u { refine fin.last_cases _ _ u; simp } }

end bounded_subterm

end  subterm

namespace subformula
variables {μ μ₁ μ₂} {Φ : μ → S} {e : fin n → S}

@[simp] def subval' (Φ : μ → S) : ∀ {n} (e : fin n → S), subformula L μ n → Prop
| n _ verum          := true
| n e (relation p v) := S.pr p (subterm.val S Φ e ∘ v)
| n e (imply p q)    := p.subval' e → q.subval' e
| n e (neg p)        := ¬(p.subval' e)
| n e (fal p)        := ∀ x : S.dom, (p.subval' (x *> e))

@[irreducible] def subval (Φ : μ → S) (e : fin n → S) : subformula L μ n →ₗ Prop :=
{ to_fun := subval' S Φ e,
  map_neg' := λ _, by refl,
  map_imply' := λ _ _, by refl,
  map_and' := λ p q, by unfold has_inf.inf; simp[and]; refl,
  map_or' := λ p q, by unfold has_sup.sup; simp[or, ←or_iff_not_imp_left]; refl,
  map_top' := by refl,
  map_bot' := by simp[bot_def]; unfold has_top.top has_negation.neg; simp }

@[reducible] def val (Φ : μ → S) : formula L μ →ₗ Prop := subformula.subval S Φ fin.nil

@[simp] lemma subval_relation {p} {r : L.pr p} {v} :
  subval S Φ e (relation r v) ↔ S.pr r (λ i, subterm.val S Φ e (v i)) :=  by simp[subval]; refl

@[simp] lemma subval_fal {p : subformula L μ (n + 1)} :
  subval S Φ e (∀'p) ↔ ∀ x : S, subval S Φ (x *> e) p := by simp[subval]; refl

@[simp] lemma subval_ex {p : subformula L μ (n + 1)} :
  subval S Φ e (∃'p) ↔ ∃ x : S, subval S Φ (x *> e) p := by simp[ex_def]

lemma subval_rew {Φ : μ₂ → S} {n} {e : fin n → S} {s : μ₁ → subterm L μ₂ n} {p : subformula L μ₁ n} :
  subval S Φ e (rew s p) ↔ subval S (λ x, subterm.val S Φ e (s x)) e p :=
by induction p using fol.subformula.ind_on; intros; simp[*, subterm.val_rew, subterm.val_lift]

lemma subval_map {Φ : μ₂ → S} {n} {e : fin n → S} {f : μ₁ → μ₂} {p : subformula L μ₁ n} :
  subval S Φ e (map f p) ↔ subval S (λ x, Φ (f x)) e p :=
by simp[map, subval_rew]

@[simp] lemma subval_subst {n} {p : subformula L μ (n + 1)} : ∀ {e : fin n → S} {t : subterm L μ n},
  subval S Φ e (subst t p) ↔ subval S Φ (e <* subterm.val S Φ e t) p :=
by apply ind_succ_on p; intros; simp[*, subterm.val_subst, subterm.val_lift, fin.left_right_concat_assoc]

section bounded_subformula
variables {m : ℕ} {Ψ : fin m → S}

lemma subval_mlift {x} {p : bounded_subformula L m n} :
  subval S (Ψ <* x) e p.mlift = subval S Ψ e p := by simp[mlift, (∘), subval_map]

lemma subval_push {x} {n} {p : bounded_subformula L m (n + 1)} : ∀ {e : fin n → S},
  subval S (Ψ <* x) e p.push ↔ subval S Ψ (e <* x) p :=
by apply ind_succ_on p; intros; simp[*, subterm.val_push, fin.left_right_concat_assoc]

lemma subval_pull {x} {n} {p : bounded_subformula L (m + 1) n} : ∀ {e : fin n → S},
  subval S Ψ (e <* x) p.pull ↔ subval S (Ψ <* x) e p :=
by induction p using fol.subformula.ind_on generalizing Ψ; intros; simp[*, subterm.val_pull, fin.left_right_concat_assoc]

lemma subval_dummy {x} : ∀ {n} {e : fin n → S} {p : bounded_subformula L m n},
  subval S Ψ (e <* x) p.dummy ↔ subval S Ψ e p :=
by simp[dummy, subval_pull, subval_mlift]

end bounded_subformula

end subformula

class Structure.proper_equal [L.has_equal] {Φ e} {t u : subterm L μ n}
(val_eq : subformula.subval S Φ e (t =' u) ↔ (t.val S Φ e = u.val S Φ e))

namespace subformula
variables (S) {Φ : μ → S}

notation S` ⊧[`:80 e`] `p :50 := val S e p

variables {S} {p q : formula L μ}

@[simp] lemma models_relation {k} {r : L.pr k} {v} :
  S ⊧[Φ] relation r v ↔ S.pr r (λ i, subterm.val S Φ fin.nil (v i)) := by simp[val]

section bounded
variables {m : ℕ} {Ψ : fin m → S}

@[simp] lemma val_fal {p : bounded_subformula L m 1} :
  S ⊧[Ψ] ∀'p ↔ ∀ x, S ⊧[Ψ <* x] p.push :=
by simp[val, subval_push, fin.concat_zero]

@[simp] lemma val_ex {p : bounded_subformula L m 1} :
  S ⊧[Ψ] ∃'p ↔ ∃ x, S ⊧[Ψ <* x] p.push :=
by simp[val, subval_push, fin.concat_zero]

@[simp] lemma val_subst {p : bounded_subformula L m 1} {t : bounded_subterm L m 0} :
  S ⊧[Ψ] subst t p ↔ S ⊧[Ψ <* subterm.val S Ψ fin.nil t] p.push :=
by simp[val, subval_subst, subval_push]

@[simp] lemma val_mlift {x : S} {p : bounded_subformula L m 0} : S ⊧[Ψ <* x] p.mlift ↔ S ⊧[Ψ] p :=
by simp[val, subval_mlift]

end bounded

end subformula

def models (S : Structure L) (p : formula L μ) : Prop := ∀ e, S ⊧[e] p

instance : semantics (formula L μ) (Structure L) := ⟨models⟩

lemma models_def {S : Structure L} {p : formula L μ} : S ⊧ p ↔ (∀ e, S ⊧[e] p) := by refl

lemma sentence_models_def {S : Structure L} {p : sentence L} : S ⊧ p ↔ S ⊧[fin.nil] p := by simp[models_def, fin.nil]

abbreviation valid (p : formula L μ) : Prop := semantics.valid (Structure L) p

abbreviation satisfiable (p : formula L μ) : Prop := semantics.satisfiable (Structure L) p

lemma valid_def (p : formula L μ) : valid p ↔ ∀ S : Structure L, S ⊧ p := by refl

lemma satisfiable_def (p : formula L μ) : satisfiable p ↔ ∃ S : Structure L, S ⊧ p := by refl

abbreviation Satisfiable (T : preTheory L μ) : Prop := semantics.Satisfiable (Structure L) T

lemma Satisfiable_def (T : preTheory L μ) : Satisfiable T ↔ ∃ S : Structure L, S ⊧ T := by refl

namespace subformula
variables {S}

@[simp] lemma models_mlift [inhabited S] {m} {p : bounded_formula L m} : S ⊧ p.mlift ↔ S ⊧ p :=
by{ simp[models_def], split,
    { intros h e,
      have : S ⊧[e <* default] p.mlift, from h _,
      simpa using this },
    { intros h e, rw ←fin.right_concat_eq e, simpa using h (e ∘ fin.cast_succ)} }

variables {S} {σ τ : sentence L}

@[simp] lemma sentence_models_verum : S ⊧ (⊤ : sentence L) := by simp[sentence_models_def]

@[simp] lemma sentence_models_relation {k} (r : L.pr k) (v : fin k → bounded_subterm L 0 0) :
  S ⊧ (relation r v) ↔ S.pr r (subterm.val S fin.nil fin.nil ∘ v) := by simp[sentence_models_def]

@[simp] lemma sentence_models_imply : S ⊧ σ ⟶ τ ↔ (S ⊧ σ → S ⊧ τ) := by simp[sentence_models_def]

@[simp] lemma sentence_models_neg : S ⊧ ∼σ ↔ ¬S ⊧ σ := by simp[sentence_models_def]

@[simp] lemma sentence_models_and : S ⊧ σ ⊓ τ ↔ S ⊧ σ ∧ S ⊧ τ := by simp[sentence_models_def]

@[simp] lemma sentence_models_or : S ⊧ σ ⊔ τ ↔ S ⊧ σ ∨ S ⊧ τ := by simp[sentence_models_def]

@[simp] lemma sentence_models_iff : S ⊧ σ ⟷ τ ↔ (S ⊧ σ ↔ S ⊧ τ) := by simp[sentence_models_def]

@[simp] lemma sentence_not_valid_iff_satisfiable (σ : sentence L) : ¬valid σ ↔ satisfiable (∼σ) :=
by simp[valid_def, satisfiable_def]

end subformula

namespace bounded_preTheory
open subformula
variables {S} {m : ℕ} {T : bounded_preTheory L m}

@[simp] lemma models_mlift [inhabited S] : S ⊧ T.mlift ↔ S ⊧ T :=
⟨by { intros h p hp,
      have : S ⊧ p.mlift, from @h p.mlift (by simpa using hp),
      exact models_mlift.mp this },
 by { intros h p hp,
      rcases mem_mlift_iff.mp hp with ⟨q, hq, rfl⟩,
      exact models_mlift.mpr (h hq) }⟩

end bounded_preTheory

instance : has_double_turnstile (preTheory L μ) (formula L μ) := ⟨semantics.consequence (Structure L)⟩

lemma consequence_def {T : preTheory L μ} {p : formula L μ} :
  T ⊧ p ↔ (∀ S : Structure L, S ⊧ T → S ⊧ p) := by refl

variables {S}

theorem soundness {m} {T : bounded_preTheory L m} {p} : T ⊢ p → T ⊧ p := λ h,
begin
  apply provable.rec_on h,
  { intros m T p b IH S hT Φ,
    simp[subformula.val], intros x,
    haveI : inhabited S, from ⟨x⟩,
    have : S ⊧ p, from @IH S (by simpa using hT),
    exact this (Φ <* x) },
  { intros m T p q b₁ b₂ m₁ m₂ S hT Φ,
    have h₁ : S ⊧[Φ] p → S ⊧[Φ] q, by simpa using m₁ hT Φ,
    have h₂ : S ⊧[Φ] p, from m₂ hT Φ,
    exact h₁ h₂ },
  { intros m T p hp S hS, exact hS hp },
  { intros m T S h Φ, simp },
  { intros m T p q S hS Φ, simp, intros h _, exact h },
  { intros m T p q r S hS Φ, simp,  intros h₁ h₂ h₃, exact h₁ h₃ (h₂ h₃) },
  { intros m T p q S hS Φ, simp, intros h₁, contrapose, exact h₁ },
  { intros m T p t S hS Φ, simp, intros h, exact h _ },
  { intros m T p q S hS Φ, simp, intros h₁ h₂ x, exact h₁ x h₂ }
end

instance {m} : logic.sound (bounded_formula L m) (Structure L) :=
⟨λ T p, soundness⟩

end fol