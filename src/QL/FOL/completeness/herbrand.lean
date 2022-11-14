import QL.FOL.semantics QL.FOL.pnf QL.FOL.language PL.semantics

universes u

variables (L : fol.language.{u})
namespace fol
open_locale logic_symbol
open subformula logic logic.Theory

@[reducible] def herbrand_universe := subterm L 0 0

inductive herbrand_basis
| relation : Π {k} (r : L.pr k), (fin k → herbrand_universe L) → herbrand_basis
| equal    : herbrand_universe L → herbrand_universe L → herbrand_basis

variables {L}

namespace herbrand_basis

@[simp] def to_open_formula : herbrand_basis L → open_sentence L
| (relation r v) := ⟨subformula.relation r v, by simp⟩
| (equal t u)    := ⟨t =' u, by simp⟩

end herbrand_basis

namespace open_subformula
open subformula open_subformula pl.formula

def to_pl_formula' : open_sentence L → pl.formula (herbrand_basis L) :=
@open_subformula.rec _ _ _ (λ _, pl.formula (herbrand_basis L))
  ⊤
  (λ k r v, atom (herbrand_basis.relation r v))
  (λ t u, atom (herbrand_basis.equal t u))
  (λ _ _ p q, p ⟶ q)
  (λ _ p, ∼p)

def to_pl_formula : open_sentence L →ₗ pl.formula (herbrand_basis L) :=
{ to_fun := to_pl_formula',
  map_neg' := λ p, by simp[to_pl_formula'],
  map_imply' := λ p q, by simp[to_pl_formula'],
  map_and' := λ p q, by simp[to_pl_formula', default_and_def],
  map_or' := λ p q, by simp[to_pl_formula', default_or_def],
  map_top' := by simp[to_pl_formula'],
  map_bot' := by simp[to_pl_formula', default_bot_def] }

lemma to_pl_formula_app (p : open_sentence L) :
  to_pl_formula p = to_pl_formula' p := rfl

@[simp] lemma to_pl_formula_relation {k} (r : L.pr k) (v : fin k → herbrand_universe L) (h) :
  to_pl_formula ⟨relation r v, h⟩ = atom (herbrand_basis.relation r v) :=
by simp[to_pl_formula_app, to_pl_formula']

@[simp] lemma to_pl_formula_equal (t u : herbrand_universe L) (h) :
  to_pl_formula ⟨t =' u, h⟩ = atom (herbrand_basis.equal t u) :=
by simp[to_pl_formula_app, to_pl_formula']

end open_subformula

namespace Structure

section pl_Structure
open open_subformula
variables {S : Structure L}

def to_pl_Structure (S : Structure L) : pl.Structure (herbrand_basis L) :=
⟨λ a, S ⊧ a.to_open_formula.to_subformula⟩

@[simp] lemma to_pl_Structure_val (a) :
  S.to_pl_Structure.val a ↔ S ⊧ a.to_open_formula.to_subformula := by refl

lemma to_pl_Structure_models {p : open_sentence L} :
  S.to_pl_Structure ⊧ p.to_pl_formula ↔ S ⊧ p.to_subformula :=
begin
  apply open_subformula.rec_on p,
  { simp[models_def] },
  { intros k r v, simp[pl.models_def] },
  { intros t u, simp[pl.models_def] },
  { intros p q IHp IHq, simp[IHp, IHq] },
  { intros p IHp, simp[IHp] }
end

lemma to_pl_Structure_models_theory {Γ : set (open_sentence L)} :
  S.to_pl_Structure ⊧ to_pl_formula '' Γ ↔ S ⊧ to_subformula '' Γ :=
by simp[logic.semantics.Models_def, to_pl_Structure_models]

end pl_Structure

end Structure

namespace subterm
variables 

end subterm

end fol

namespace pl

namespace formula



end formula

end pl