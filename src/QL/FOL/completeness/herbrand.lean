import QL.FOL.semantics QL.FOL.pnf QL.FOL.language PL.semantics

universes u
open_locale logic_symbol

variables (L : fol.language.{u})
namespace fol

open subformula logic logic.Theory

@[reducible] def herbrand_universe := subterm L 0 0

inductive herbrand_basis
| relation : Π {k} (r : L.pr k), (fin k → herbrand_universe L) → herbrand_basis
| equal    : herbrand_universe L → herbrand_universe L → herbrand_basis

variables {L}

namespace herbrand_basis

@[simp] def to_sentence : herbrand_basis L → sentence L
| (relation r v) := subformula.relation r v
| (equal t u)    := t =' u

end herbrand_basis

end fol

namespace pl

namespace formula
variables {L}

def to_fol' : formula (fol.herbrand_basis L) → fol.sentence L
| (atom (fol.herbrand_basis.relation r v)) := fol.subformula.relation r v
| (atom (fol.herbrand_basis.equal t u))    := (t =' u)
| ⊤                                        := ⊤
| (p ⟶ q)                                  := p.to_fol' ⟶ q.to_fol'
| (∼p)                                     := ∼p.to_fol'

def to_fol : formula (fol.herbrand_basis L) →ₗ fol.sentence L :=
{ to_fun := to_fol',
  map_neg' := by intros; refl,
  map_imply' := by intros; refl,
  map_and' := by intros; refl,
  map_or' := by intros; refl,
  map_top' := by intros; refl,
  map_bot' := by intros; refl }

@[simp] lemma to_fol_atom_relation {k} (r : L.pr k) (v : fin k → fol.herbrand_universe L) :
  to_fol (atom (fol.herbrand_basis.relation r v)) = fol.subformula.relation r v := rfl

@[simp] lemma to_fol_atom_equal (t u : fol.herbrand_universe L) :
  to_fol (atom (fol.herbrand_basis.equal t u)) = (t =' u) := rfl

@[simp] lemma to_fol_open (p : formula (fol.herbrand_basis L)) : p.to_fol.is_open :=
by induction p; try { simp* }; case atom : η { rcases η; simp }

variables (L)

inductive equal_axioms : Theory (fol.herbrand_basis L)
| eq_refl : ∀ t, equal_axioms (atom (fol.herbrand_basis.equal t t))
| eq_symm : ∀ t₁ t₂, equal_axioms (atom (fol.herbrand_basis.equal t₁ t₂) ⟶ atom (fol.herbrand_basis.equal t₂ t₁))
| eq_trans : ∀ t₁ t₂ t₃,
    equal_axioms (atom (fol.herbrand_basis.equal t₁ t₂) ⟶ atom (fol.herbrand_basis.equal t₂ t₃) ⟶ atom (fol.herbrand_basis.equal t₁ t₃))
| func_ext : ∀ {k} (f : L.fn k) (v w : fin k → fol.herbrand_universe L),
    equal_axioms ((⋀ i, atom (fol.herbrand_basis.equal (v i) (w i))) ⟶
      atom (fol.herbrand_basis.equal (fol.subterm.function f v) (fol.subterm.function f w)))
| rel_ext : ∀ {k} (r : L.pr k) (v w : fin k → fol.herbrand_universe L),
    equal_axioms ((⋀ i, atom (fol.herbrand_basis.equal (v i) (w i))) ⟶
      (atom (fol.herbrand_basis.relation r v) ⟷ atom (fol.herbrand_basis.relation r w)))

end formula

end pl

namespace fol
open subformula logic logic.Theory
variables {L}

namespace sentence
open subformula

def to_pl : ∀ p : sentence L, p.is_open → pl.formula (herbrand_basis L) :=
open_rec
  ⊤
  (λ k r v, pl.formula.atom (herbrand_basis.relation r v))
  (λ t u, pl.formula.atom (herbrand_basis.equal t u))
  (λ _ _ _ _ p q, p ⟶ q) (λ _ _ p, ∼p)

end sentence

namespace Structure

def to_pl (S : Structure L) : pl.Structure (herbrand_basis L) := ⟨λ a, S ⊧ a.to_sentence⟩
namespace to_pl
open subterm subformula
variables {S : Structure L}

@[simp] protected lemma val (a) : S.to_pl.val a ↔ S ⊧ a.to_sentence := by refl

protected lemma models {p : pl.formula (herbrand_basis L)} :
  S.to_pl ⊧ p ↔ S ⊧ p.to_fol :=
by induction p; try {simp*}; case atom : η { cases η; simp[pl.models_def] }

protected lemma Models {Γ : pl.Theory (herbrand_basis L)} :
  S.to_pl ⊧ Γ ↔ S ⊧ pl.formula.to_fol '' Γ :=
by simp[logic.semantics.Models_def, to_pl.models]

end to_pl

namespace Herbrand
open subterm subformula
variables {L} (V : pl.Structure (herbrand_basis L)) (H : V ⊧ pl.formula.equal_axioms L)

def pl_equiv (H : V ⊧ pl.formula.equal_axioms L) (t u : herbrand_universe L) : Prop := V.val (herbrand_basis.equal t u)

@[refl, simp] lemma pl_equiv_refl (x : herbrand_universe L) :
  pl_equiv V H x x :=
by simpa[pl.models_def] using H (pl.formula.equal_axioms.eq_refl x)

lemma pl_equiv_equivalence : equivalence (pl_equiv V H) :=
⟨by { intros x, simp[H] },
 by { intros x y, simpa using H (pl.formula.equal_axioms.eq_symm x y) },
 by { intros x y z, simpa using H (pl.formula.equal_axioms.eq_trans x y z) }⟩

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

@[simp] lemma of_eq_of {t u : herbrand_universe L} : qu V H t = qu V H u ↔ V.val (herbrand_basis.equal t u) :=
by simp[qu, quotient.eq']; refl

def function {k} (f : L.fn k) (v : finitary (domain V H) k) : domain V H :=
Herbrand.lift_on_finitary V H v (λ x, qu V H (subterm.function f x))
(begin
   intros v w h, simp,
   have : (∀ i, V.val (herbrand_basis.equal (v i) (w i))) → V.val (herbrand_basis.equal (function f v) (function f w)),
   by simpa[pl.models_def] using H (pl.formula.equal_axioms.func_ext f v w),
   exact this h,
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
   by simpa[pl.models_def] using H (pl.formula.equal_axioms.rel_ext r v w),
   exact this h
 end)

@[simp] def relation_qu {k} (r : L.pr k) (v : finitary (herbrand_universe L) k) :
  relation V H r (λ i, qu V H (v i)) ↔ V.val (herbrand_basis.relation r v) :=
by simp[relation]; exact (pl_equiv_equivalence V H).1 _

end Herbrand

variables [inhabited (L.fn 0)]

@[reducible] def Herbrand (V : pl.Structure (herbrand_basis L)) (H : V ⊧ pl.formula.equal_axioms L) : Structure L :=
{ dom := Herbrand.domain V H,
  dom_inhabited := ⟨Herbrand.function V H default fin_zero_elim⟩,
  fn := @Herbrand.function _ V H,
  pr := @Herbrand.relation _ V H, }

namespace Herbrand
variables {L} (V : pl.Structure (herbrand_basis L)) (H : V ⊧ pl.formula.equal_axioms L)

@[simp] lemma models_val (t : herbrand_universe L) : subterm.val (Herbrand V H) fin.nil fin.nil t = qu V H t :=
by { induction t; simp[*, -of_eq_of]; { exact fin_zero_elim t } }

lemma models_relation_iff {k} (r : L.pr k) (v : fin k → herbrand_universe L) :
  Herbrand V H ⊧ subformula.relation r v ↔ V.val (herbrand_basis.relation r v) :=
by simp[sentence_models_def, (∘)]

protected lemma models : ∀ {p : pl.formula (fol.herbrand_basis L)}, Herbrand V H ⊧ p.to_fol ↔ V ⊧ p
| ⊤ := by simp
| (pl.formula.atom (herbrand_basis.relation r v)) := by simp[sentence_models_def, (∘), pl.models_def]
| (pl.formula.atom (herbrand_basis.equal t u))    := by simp[sentence_models_def, pl.models_def]
| (p ⟶ q)                                         := by simp[@models p, @models q]
| (∼p)                                            := by simp[@models p]

protected lemma Models {Γ : pl.Theory (herbrand_basis L)} : Herbrand V H ⊧ pl.formula.to_fol '' Γ ↔ V ⊧ Γ :=
by simp[logic.semantics.Models_def, Herbrand.models]

end Herbrand

end Structure

namespace subterm
variables 

end subterm

end fol