import QL.FOL.Tait.calculus

universes u v

namespace fol
open_locale logic_symbol aclogic
variables {L : language.{u}} {m n : ℕ}

namespace Tait

namespace subformula

variables (S : Structure L) {n} {me : fin m → S} {e : fin n → S}

@[simp] def val' (me : fin m → S) : ∀ {n} (e : fin n → S), subformula L m n → Prop
| n _ verum              := true
| n _ falsum             := false
| n e (relation p v)     := S.pr p (subterm.val S me e ∘ v)
| n e (neg_relation p v) := ¬S.pr p (subterm.val S me e ∘ v)
| n e (and p q)          := p.val' e ∧ q.val' e
| n e (or p q)           := p.val' e ∨ q.val' e
| n e (fal p)            := ∀ x : S, (p.val' (x *> e))
| n e (ex p)             := ∃ x : S, (p.val' (x *> e))

@[simp] lemma val'_neg (p : subformula L m n) : val' S me e (∼p) = ¬val' S me e p :=
by induction p generalizing me e; simp[mlift, ←verum_eq, ←falsum_eq, ←and_eq, ←or_eq, ←not_eq, ←fal_eq, ←ex_eq, or_iff_not_imp_left, *] at*

@[irreducible] def val (me : fin m → S) (e : fin n → S) : subformula L m n →ₗ Prop :=
{ to_fun := val' S me e,
  map_neg' := λ _, by simp,
  map_imply' := λ _ _, by simp[has_arrow.arrow, imply, or_iff_not_imp_left, not_eq],
  map_and' := λ p q, by unfold has_inf.inf; simp; refl,
  map_or' := λ p q, by unfold has_sup.sup; simp; refl,
  map_top' := by refl,
  map_bot' := by refl }

@[simp] lemma val_relation {p} (r : L.pr p) (v) :
  val S me e (relation r v) ↔ S.pr r (subterm.val S me e ∘ v) :=  by simp[val]; refl

@[simp] lemma val_neg_relation {p} (r : L.pr p) (v) :
  val S me e (neg_relation r v) ↔ ¬S.pr r (subterm.val S me e ∘ v) := by simp[val]; refl

@[simp] lemma val_fal (p : subformula L m (n + 1)) :
  val S me e (∀'p) ↔ ∀ x : S, val S me (x *> e) p := by simp[val]; refl

@[simp] lemma val_ex (p : subformula L m (n + 1)) :
  val S me e (∃'p) ↔ ∃ x : S, val S me (x *> e) p := by simp[val]; refl

end subformula

namespace formula
variables (S : Structure L) {m n} (me : fin m → S)

def val : formula L m →ₗ Prop := subformula.val S me fin.nil  

end formula

def models (S : Structure L) (p : formula L m) : Prop := ∀ e, formula.val S e p

infix (name := Tait.models) ` ⊧ᵀ ` :55 := models

namespace sentence
variables (S : Structure L) (σ : sentence L)

lemma models_iff : S ⊧ᵀ σ ↔ formula.val S fin.nil σ :=
by simp[models, fin.nil]

end sentence
/-
namespace uniform_subformula

variables (S : Structure L) {n} {me : ℕ → S} {e : fin n → S}

@[simp] def val' (me : ℕ → S) : ∀ {n} (e : fin n → S), uniform_subformula L n → Prop
| n _ verum              := true
| n _ falsum             := false
| n e (relation p v)     := S.pr p (uniform_subterm.val S me e ∘ v)
| n e (neg_relation p v) := ¬S.pr p (uniform_subterm.val S me e ∘ v)
| n e (and p q)          := p.val' e ∧ q.val' e
| n e (or p q)           := p.val' e ∨ q.val' e
| n e (fal p)            := ∀ x : S, (p.val' (x *> e))
| n e (ex p)             := ∃ x : S, (p.val' (x *> e))

@[simp] lemma val'_neg (p : uniform_subformula L n) : val' S me e (∼p) = ¬val' S me e p :=
by simp[←not_eq]; induction p generalizing me e; simp[or_iff_not_imp_left, *]

@[irreducible] def val (me : ℕ → S) (e : fin n → S) : uniform_subformula L n →ₗ Prop :=
{ to_fun := val' S me e,
  map_neg' := λ _, by simp,
  map_imply' := λ _ _, by simp[imply_def, or_iff_not_imp_left, ←or_eq],
  map_and' := λ p q, by unfold has_inf.inf; simp; refl,
  map_or' := λ p q, by unfold has_sup.sup; simp; refl,
  map_top' := by refl,
  map_bot' := by refl }

@[simp] lemma val_relation {p} (r : L.pr p) (v) :
  val S me e (relation r v) ↔ S.pr r (uniform_subterm.val S me e ∘ v) :=  by simp[val]; refl

@[simp] lemma val_neg_relation {p} (r : L.pr p) (v) :
  val S me e (neg_relation r v) ↔ ¬S.pr r (uniform_subterm.val S me e ∘ v) := by simp[val]; refl

@[simp] lemma val_fal (p : uniform_subformula L (n + 1)) :
  val S me e (∀'p) ↔ ∀ x : S, val S me (x *> e) p := by simp[val]; refl

@[simp] lemma val_ex (p : uniform_subformula L (n + 1)) :
  val S me e (∃'p) ↔ ∃ x : S, val S me (x *> e) p := by simp[val]; refl

@[simp] lemma val_subst : ∀ {n} {e : fin n → S} (t : uniform_subterm L n) (p : uniform_subformula L (n + 1)),
  val S me e (subst t p) ↔ val S me (e <* t.val S me e) p
| n e t verum              := by simp[verum_eq]
| n e t falsum             := by simp[falsum_eq]
| n e t (relation r v)     := by simp[(∘)]
| n e t (neg_relation r v) := by simp[(∘)]
| n e t (and p q)          := by simp[and_eq, val_subst t p, val_subst t q]
| n e t (or p q)           := by simp[or_eq, val_subst t p, val_subst t q]
| n e t (fal p)            := by simp[fal_eq, val_subst t.lift p, fin.left_right_concat_assoc]
| n e t (ex p)             := by simp[ex_eq, val_subst t.lift p, fin.left_right_concat_assoc]
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.2.2.complexity)⟩]}

end uniform_subformula

namespace uniform_formula
variables (S : Structure L) {m n} (me : ℕ → S)

def val : uniform_formula L →ₗ Prop := uniform_subformula.val S me fin.nil  

end uniform_formula

def uniform_models (S : Structure L) (p : uniform_formula L) : Prop := ∀ e, uniform_formula.val S e p

infix (name := Tait.uniform_models) ` ⊧ᵀᵤ ` :55 := uniform_models

namespace subformula
variables (S : Structure L) {n} {me : ℕ → S} {e : fin n → S}

lemma val_uniform (p : subformula L m n) : uniform_subformula.val S me e p.uniform ↔ val S (λ i, me i) e p :=
by { induction p; simp[verum_eq, uniform_subformula.verum_eq, falsum_eq, uniform_subformula.falsum_eq,
     and_eq, uniform_subformula.and_eq, or_eq, uniform_subformula.or_eq, fal_eq, uniform_subformula.fal_eq,
     ex_eq, uniform_subformula.ex_eq, (∘), *] }

end subformula
-/
end Tait

end fol