import QL.FOL.Tait.tait QL.FOL.semantics logic

universes u v

namespace fol
open_locale logic_symbol aclogic

namespace Tait

variables {L : language.{u}} {m n : ℕ}
namespace subformula

variables (S : Structure L) {m n} {me : fin m → S} {e : fin n → S}

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


namespace sentence
variables (S : Structure L)

def models : sentence L →ₗ Prop := subformula.val S fin.nil fin.nil  

end sentence

open subformula

noncomputable def finset_mlift (Δ : finset (subformula L m n)) : finset (subformula L (m + 1) n) := Δ.image mlift

-- Tate caluculus
inductive derivative : Π {m}, finset (subformula L m 0) → Type u
| AxL {m} : ∀ (Δ : finset (subformula L m 0)) {k} (r : L.pr k) (v : fin k → subterm L m 0),
    relation r v ∈ Δ → neg_relation r v ∈ Δ → derivative Δ
| or_left {m} : ∀ (Δ : finset (subformula L m 0)) (p q : formula L m),
    derivative (insert p Δ) → derivative (insert (p ⊔ q) Δ)
| or_right {m} : ∀ (Δ : finset (subformula L m 0)) (p q : formula L m),
    derivative (insert q Δ) → derivative (insert (p ⊔ q) Δ)
| and {m} : ∀ (Δ : finset (subformula L m 0)) (p q : formula L m),
    derivative (insert p Δ) → derivative (insert q Δ) → derivative (insert (p ⊓ q) Δ)
| all {m} : ∀ (Δ : finset (subformula L m 0)) (p : subformula L m 1),
    derivative (insert p.push (finset_mlift Δ)) → derivative (insert (∀'p) Δ)

variables {Δ : finset (subformula L m 0)}
open axiomatic_classical_logic' axiomatic_classical_logic

prefix `⊢ᵀ `:45 := derivative

#check @derivative

lemma provable_of_derivative : ⊢ᵀ Δ → ∅ ⊢ (Δ.image to_fol).disjunction := λ h,
begin
  induction h,
  case AxL : m Δ k r v h nh
  { suffices : ∅ ⊢ fol.subformula.relation r v ⊔ ∼fol.subformula.relation r v ⟶ (finset.image to_fol Δ).disjunction,
    from this ⨀ excluded_middle,
    refine or_imply _ _ _ ⨀ _ ⨀ _,
    { refine imply_fdisj (by { simp, refine ⟨_, h, by simp⟩ }) },
    { refine imply_fdisj (by { simp, refine ⟨_, nh, by simp⟩ }) } },
  case or_left : m Δ p q b IH
  { refine fdisj_imply_of _ ⨀ IH,
    { simp, split,
      { refine imply_trans (imply_or_left p.to_fol q.to_fol) (imply_fdisj (by simp)) },
      { intros p hp, refine (imply_fdisj
          (finset.mem_insert_of_mem (finset.mem_image_of_mem to_fol hp))) } } },
  case or_right : m Δ p q b IH
  { refine fdisj_imply_of _ ⨀ IH,
    { simp, split,
      { refine imply_trans (imply_or_right p.to_fol q.to_fol) (imply_fdisj (by simp)) },
      { intros p hp, refine (imply_fdisj
          (finset.mem_insert_of_mem (finset.mem_image_of_mem to_fol hp))) } } },
  sorry
end

def is_terminal {m} (Δ : list (subformula L m 0)) : Prop := ∃ {k} (r : L.pr k) (v), relation r v ∈ Δ ∧ neg_relation r v ∈ Δ

inductive search_tree : (Σ m, list (subformula L m 0)) → (Σ m, list (subformula L m 0)) → Prop
| rel : ∀ {k} (r : L.pr k) (v) (Δ : list (subformula L m 0)), ¬is_terminal Δ →
    search_tree ⟨m, relation r v :: Δ⟩ ⟨m, relation r v :: Δ⟩

end Tait



end fol