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
open open_subformula subterm subformula
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

namespace Herbrand
open pl open_subformula open_sentence subterm subformula
variables {L} (V : pl.Structure (herbrand_basis L)) (H : V ⊧ to_pl_formula '' (equal_axioms L))

def pl_equiv (H : V ⊧ to_pl_formula '' (equal_axioms L)) (t u : herbrand_universe L) : Prop := V.val (herbrand_basis.equal t u)

@[refl, simp] lemma pl_equiv_refl (H : V ⊧ to_pl_formula '' (equal_axioms L)) (x : herbrand_universe L) :
  pl_equiv V H x x :=
by simpa[pl.models_def] using H (by simp; refine ⟨_, open_sentence.equal_axioms.eq_refl x, by simp⟩)

lemma pl_equiv_equivalence (H : V ⊧ to_pl_formula '' (equal_axioms L)) : equivalence (pl_equiv V H) :=
⟨by { intros x, simp[H] },
 by { intros x y,
      have : V ⊧ to_pl_formula ⟨(x =' y) ⟶ (y =' x), _⟩, 
      from H (by simp; exact ⟨_, open_sentence.equal_axioms.eq_symm x y, rfl⟩),
      simpa using this },
 by { intros x y z,
      have : V ⊧ to_pl_formula ⟨(x =' y) ⟶ (y =' z) ⟶ (x =' z), _⟩,
      from H (by simp; exact ⟨_, open_sentence.equal_axioms.eq_trans x y z, rfl⟩),
      simpa using this }⟩

def domain := quotient (⟨pl_equiv V H, pl_equiv_equivalence V H⟩ : setoid (herbrand_universe L))

def qu (t : herbrand_universe L) : domain V H := quotient.mk' t

@[elab_as_eliminator]
protected lemma ind_on {C : domain V H → Prop} (d : domain V H)
  (h : ∀ t, C (qu V H t)) : C d := quotient.induction_on' d h

@[elab_as_eliminator, reducible]
protected def lift_on {φ : Sort*} (p : domain V H) (f : herbrand_universe L → φ)
  (h : ∀ t u, pl_equiv V H t u → f t = f u) : φ := quotient.lift_on' p f h

@[elab_as_eliminator, reducible]
protected def lift_on_finitary {φ : Sort*} {n : ℕ} (v : finitary (domain V H) n) (f : finitary (herbrand_universe L) n → φ)
  (h : ∀ v₁ v₂ : finitary (herbrand_universe L) n, (∀ i, pl_equiv V H (v₁ i) (v₂ i)) → f v₁ = f v₂) : φ :=
quotient.lift_on_finitary v f h 

@[simp] protected lemma lift_on_finitary_eq {φ : Sort*} {n : ℕ}
  (v : finitary (herbrand_universe L) n) (f : finitary (herbrand_universe L) n → φ) (h) :
Herbrand.lift_on_finitary V H (λ x, qu V H (v x)) f h = f v :=
quotient.lift_on_finitary_eq v f h

@[simp] lemma of_eq_of {t u : herbrand_universe L} : qu V H t = qu V H u ↔ pl_equiv V H t u :=
by simp[qu, quotient.eq']

def function {k} (f : L.fn k) (v : finitary (domain V H) k) : domain V H :=
Herbrand.lift_on_finitary V H v (λ x, qu V H (subterm.function f x))
(begin
   intros v w h, simp,
   have : (∀ i, V.val (herbrand_basis.equal (v i) (w i))) → V.val (herbrand_basis.equal (function f v) (function f w)),
   by simpa[pl.models_def] using H (by simp; exact ⟨_, open_sentence.equal_axioms.func_ext f v w, rfl⟩),
   exact this h
 end)

@[simp] def function_qu {k} (f : L.fn k) (v : finitary (herbrand_universe L) k) :
  function V H f (λ i, qu V H (v i)) = qu V H (subterm.function f v) :=
by simp[function]; exact (pl_equiv_equivalence V H).1 _

def relation {k} (r : L.pr k) (v : finitary (domain V H) k) : Prop :=
Herbrand.lift_on_finitary V H v (λ x, V.val (herbrand_basis.relation r x))
(begin
   intros v w h, simp,
  have : (∀ i, V.val (herbrand_basis.equal (v i) (w i))) →
    (V.val (herbrand_basis.relation r v) ↔ V.val (herbrand_basis.relation r w)),
  by simpa[pl.models_def] using H (by simp; exact ⟨_, open_sentence.equal_axioms.rel_ext r v w, rfl⟩),
   exact this h
 end)

@[simp] def relation_qu {k} (r : L.pr k) (v : finitary (herbrand_universe L) k) :
  relation V H r (λ i, qu V H (v i)) ↔ V.val (herbrand_basis.relation r v) :=
by simp[relation]; exact (pl_equiv_equivalence V H).1 _

variables [inhabited (L.fn 0)]

@[reducible] def model : Structure L :=
{ dom := domain V H,
  dom_inhabited := ⟨function V H default fin_zero_elim⟩,
  fn := @function _ V H,
  pr := @relation _ V H, }

@[simp] lemma models_val (t : subterm L 0 0) : val (model V H) fin_zero_elim fin.nil t = qu V H t :=
by { induction t; simp*; { exact fin_zero_elim t } }

lemma models_relation_iff {k} (r : L.pr k) (v : fin k → subterm L 0 0) :
  model V H ⊧ subformula.relation r v ↔ V.val (herbrand_basis.relation r v) :=
by simp[models_def, (∘)]

lemma models {p : open_sentence L} : model V H ⊧ p.to_subformula ↔ V ⊧ p.to_pl_formula :=
begin
  apply open_subformula.rec_on p,
  { simp },
  { simp[pl.models_def, models_def, (∘)] },
  { simp[pl.models_def, models_def, pl_equiv] },
  { intros p q IHp IHq, simp* },
  { intros p IH, simp* }
end

end Herbrand

end Structure

namespace subterm
variables 

end subterm

end fol

namespace pl

namespace formula



end formula

end pl