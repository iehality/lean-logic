import QL.FOL.Tait.calculus logic

universes u v

namespace fol
open_locale logic_symbol aclogic
variables {L : language.{u}} {μ : Type v} {μ₁ : Type*} {μ₂ : Type*} {m n : ℕ} {S : Structure L}

namespace Tait

namespace subformula

variables (S) {n} {Φ : μ → S} {e : fin n → S}

@[simp] def subval' (Φ : μ → S) : ∀ {n} (e : fin n → S), subformula L μ n → Prop
| n _ verum              := true
| n _ falsum             := false
| n e (relation p v)     := S.pr p (λ i, subterm.val S Φ e (v i))
| n e (neg_relation p v) := ¬S.pr p (λ i, subterm.val S Φ e (v i))
| n e (and p q)          := p.subval' e ∧ q.subval' e
| n e (or p q)           := p.subval' e ∨ q.subval' e
| n e (fal p)            := ∀ x : S, (p.subval' (x *> e))
| n e (ex p)             := ∃ x : S, (p.subval' (x *> e))

@[simp] lemma subval'_neg (p : subformula L μ n) : subval' S Φ e (∼p) = ¬subval' S Φ e p :=
by induction p generalizing Φ e; simp[mlift, ←verum_eq, ←falsum_eq, ←and_eq, ←or_eq, ←not_eq, ←fal_eq, ←ex_eq, or_iff_not_imp_left, *] at*

@[irreducible] def subval (Φ : μ → S) (e : fin n → S) : subformula L μ n →ₗ Prop :=
{ to_fun := subval' S Φ e,
  map_neg' := λ _, by simp,
  map_imply' := λ _ _, by simp[has_arrow.arrow, imply, or_iff_not_imp_left, not_eq],
  map_and' := λ p q, by unfold has_inf.inf; simp; refl,
  map_or' := λ p q, by unfold has_sup.sup; simp; refl,
  map_top' := by refl,
  map_bot' := by refl }

@[reducible] def val (Φ : μ → S) : formula L μ →ₗ Prop := subformula.subval S Φ fin.nil

@[simp] lemma subval_relation {p} {r : L.pr p} {v} :
  subval S Φ e (relation r v) ↔ S.pr r (subterm.val S Φ e ∘ v) :=  by simp[subval]; refl

@[simp] lemma subval_neg_relation {p} {r : L.pr p} {v} :
  subval S Φ e (neg_relation r v) ↔ ¬S.pr r (subterm.val S Φ e ∘ v) := by simp[subval]; refl

@[simp] lemma subval_fal {p : subformula L μ (n + 1)} :
  subval S Φ e (∀'p) ↔ ∀ x : S, subval S Φ (x *> e) p := by simp[subval]; refl

@[simp] lemma subval_ex {p : subformula L μ (n + 1)} :
  subval S Φ e (∃'p) ↔ ∃ x : S, subval S Φ (x *> e) p := by simp[subval]; refl

variables {μ₁ μ₂}

lemma subval_map {f : μ₁ → μ₂} {Φ : μ₂ → S} {p : subformula L μ₁ n} :
  subval S Φ e (map f p) ↔ subval S (Φ ∘ f) e p :=
by induction p using fol.Tait.subformula.ind_on; simp[*, (∘), subterm.val_map]

lemma subval_subst {p : subformula L μ (n + 1)} : ∀ {e} {u : subterm L μ n},
  subval S Φ e (subst u p) ↔ subval S Φ (e <* subterm.val S Φ e u) p :=
by apply ind_succ_on p; intros; simp[*, (∘), subterm.val_subst, subterm.val_lift, fin.left_right_concat_assoc]

end subformula

namespace subformula
variables (S) {Φ : μ → S}

notation S` ⊧ᵀ[`:80 e`] `p :50 := val S e p

variables {S} {p q : formula L μ}

@[simp] lemma models_relation {k} {r : L.pr k} {v} :
  S ⊧ᵀ[Φ] relation r v ↔ S.pr r (λ i, subterm.val S Φ fin.nil (v i)) := by simp[val]

end subformula

def models (S : Structure L) (p : formula L μ) : Prop := ∀ e, S ⊧ᵀ[e] p

instance : logic.semantics (formula L μ) (Structure L) := ⟨models⟩

lemma models_def {S : Structure L} {p : formula L μ} : S ⊧ p ↔ (∀ e, S ⊧ᵀ[e] p) := by refl

lemma sentence_models_def {S : Structure L} {σ : sentence L} : S ⊧ σ ↔ S ⊧ᵀ[fin.nil] σ := by simp[models_def, fin.nil]

--@[simp] lemma models_neg {σ : sentence L} :
--  S ⊧ ∼σ ↔ ¬S ⊧ σ := by simp[sentence_models_def]

@[simp] lemma models_coe {S : Structure L} {σ : sentence L} {e : μ → S} : S ⊧ᵀ[e] ↑σ ↔ S ⊧ σ :=
by { rw [subformula.sentence_coe_def], 
     simp[sentence_models_def, -subformula.map_sentence_coe, subformula.val, subformula.subval_map,
       show e ∘ fin.nil = fin.nil, by ext x; exact fin.nil x] }

instance : has_double_turnstile (Tait.preTheory L μ) (formula L μ) := ⟨logic.semantics.consequence (Structure L)⟩

lemma consequence_def {T : preTheory L μ} {p : formula L μ} :
  T ⊧ p ↔ (∀ S : Structure L, S ⊧ T → S ⊧ p) := by refl

namespace subformula
variables (S) {Φ : μ → S} {e : fin n → S}

@[simp] lemma subval_to_tait {p : fol.subformula L μ n} : subval S Φ e p.to_tait ↔ fol.subformula.subval S Φ e p :=
by induction p using fol.subformula.ind_on; simp*

@[simp] lemma subval_of_tait {p : Tait.subformula L μ n} : fol.subformula.subval S Φ e p.of_tait ↔ subval S Φ e p :=
by induction p using fol.Tait.subformula.ind_on; simp*

end subformula

@[simp] lemma models_to_tait {p : fol.formula L μ} : S ⊧ p.to_tait ↔ S ⊧ p :=
by simp[models_def, fol.models_def]

@[simp] lemma models_of_tait {p : Tait.formula L μ} : S ⊧ p.of_tait ↔ S ⊧ p :=
by simp[models_def, fol.models_def]

end Tait

end fol