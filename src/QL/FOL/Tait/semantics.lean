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
| n e (fal p)            := ∀ x : S.dom, (p.val' (x *> e))
| n e (ex p)             := ∃ x : S.dom, (p.val' (x *> e))

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


end Tait

end fol