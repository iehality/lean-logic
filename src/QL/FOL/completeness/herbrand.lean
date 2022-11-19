import QL.FOL.semantics QL.FOL.pnf QL.FOL.language PL.semantics

universes u
open_locale logic_symbol

variables (L : fol.language.{u})
namespace fol

open subformula logic logic.Theory

@[reducible] def herbrand_universe := subterm L 0 0

instance [inhabited (L.fn 0)] : inhabited (herbrand_universe L) := ⟨subterm.function default fin.nil⟩

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

@[simp] lemma to_pl_verum (h) : to_pl (⊤ : sentence L) h = ⊤ := by simp[to_pl]

@[simp] lemma to_pl_relation {k} (r : L.pr k) (v : fin k → subterm L 0 0) (h) :
  to_pl (relation r v) h = pl.formula.atom (herbrand_basis.relation r v) := by simp[to_pl]

@[simp] lemma to_pl_equal (t u : subterm L 0 0) (h) :
  to_pl (t =' u) h = pl.formula.atom (herbrand_basis.equal t u) := by simp[to_pl]

@[simp] lemma to_pl_imply (p q : sentence L) (h) :
  to_pl (p ⟶ q) h = to_pl p (by simp at h; exact h.1) ⟶ to_pl q (by simp at h; exact h.2) := by simp[to_pl]

@[simp] lemma to_pl_neg (p : sentence L) (h) :
  to_pl (∼p) h = ∼to_pl p (by simpa using h) := by simp[to_pl]

@[simp] lemma to_fol_to_pl : ∀ (p : sentence L) (h : p.is_open), (p.to_pl h).to_fol = p :=
by apply open_rec; { intros, simp* }

@[simp] lemma to_pl_to_fol (p : pl.formula (herbrand_basis L)) (h) : p.to_fol.to_pl h = p :=
by { induction p; try { simp* }, case atom : η { rcases η; simp } }

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

instance : setoid (herbrand_universe L) := ⟨pl_equiv V H, pl_equiv_equivalence V H⟩

def domain := quotient (herbrand_universe.setoid V H)

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

lemma models_relation_iff' {k} (r : L.pr k) (v : fin k → herbrand_universe L) :
  Herbrand V H ⊧ subformula.relation r v ↔ V.val (herbrand_basis.relation r v) :=
by simp[sentence_models_def, (∘)]

lemma models_relation_iff {k} (r : L.pr k) (v : fin k → herbrand_universe L) :
  Herbrand V H ⊧ subformula.relation r v ↔ V.val (herbrand_basis.relation r v) :=
by simp[sentence_models_def, (∘)]

variables {V H}

noncomputable def qu_inv (x : Herbrand V H) : herbrand_universe L := classical.epsilon (λ t, qu V H t = x)

@[simp] lemma qu_to_hu (x : Herbrand V H) : qu V H (qu_inv x) = x := 
@classical.epsilon_spec (herbrand_universe L) (λ t, qu V H t = x)
(by induction x using fol.Structure.Herbrand.ind_on; exact ⟨x, by refl⟩)

lemma subterm_subst {n} (x) : ∀ (t : subterm L 0 n), subterm.val (Herbrand V H) fin.nil x t = qu V H (subterm.substs (qu_inv ∘ x) t)
| #x := by simp
| &x := fin_zero_elim x
| (subterm.function f v) := by simp[λ i, subterm_subst (v i), -of_eq_of]

lemma val_iff_subst {n} (p : subformula L 0 n) (hp : p.is_open) : ∀ x,
  val (Herbrand V H) fin.nil x p ↔ V ⊧ sentence.to_pl (substs (qu_inv ∘ x) p) (by simpa using hp) :=
begin
  apply open_rec_on p hp,
  { simp },
  { intros k r v x, simp[pl.models_def, (∘), subterm_subst] },
  { intros t u x, simp[pl.models_def, subterm_subst] },
  { intros p q hp hq IHp IHq x, simp[IHp, IHq] },
  { intros p hp IH x, simp[IH] }
end

protected lemma models : ∀ {p : pl.formula (fol.herbrand_basis L)}, Herbrand V H ⊧ p.to_fol ↔ V ⊧ p
| ⊤                                               := by simp
| (pl.formula.atom (herbrand_basis.relation r v)) := by simp[sentence_models_def, (∘), pl.models_def]
| (pl.formula.atom (herbrand_basis.equal t u))    := by simp[sentence_models_def, pl.models_def]
| (p ⟶ q)                                         := by simp[@models p, @models q]
| (∼p)                                            := by simp[@models p]

protected lemma Models {Γ : pl.Theory (herbrand_basis L)} : Herbrand V H ⊧ pl.formula.to_fol '' Γ ↔ V ⊧ Γ :=
by simp[logic.semantics.Models_def, Herbrand.models]

end Herbrand

namespace to_pl
variables (S : Structure L)

@[simp] lemma to_pl_equal_axioms : S.to_pl ⊧ pl.formula.equal_axioms L := λ p h,
begin
  induction h,
  case eq_refl { simp[to_pl.models, sentence_models_def] },
  case eq_symm : t₁ t₂ { simp[to_pl.models, sentence_models_def], exact eq.symm },
  case eq_trans : t₁ t₂ t₃ { simp[to_pl.models, sentence_models_def], exact eq.trans },
  case func_ext : k f v w { simp[to_pl.models, sentence_models_def], intros h, refine congr_arg _ (funext h) },
  case rel_ext : k r v w { simp[to_pl.models, sentence_models_def], intros h, refine iff_of_eq (congr_arg _ (funext h)) }
end

lemma Herbran_models {S : Structure L} (p : pl.formula (fol.herbrand_basis L)): 
  S ⊧ p.to_fol ↔ Herbrand (S.to_pl) (to_pl_equal_axioms S) ⊧ p.to_fol :=
to_pl.models.symm.trans Herbrand.models.symm

end to_pl

end Structure

namespace herbrand_universe
open Structure
variables {L} {m n : ℕ} [inhabited (L.fn 0)]

lemma Herbrand_aux (p : subformula L 0 n) (p_open : p.is_open)
  (H : ∀ (w : list (fin n → herbrand_universe L)), 
    ∃ V : pl.Structure (herbrand_basis L), V ⊧ pl.formula.equal_axioms L ∧
    ∀ x ∈ w, V ⊧ sentence.to_pl (∼substs x p) (by simpa using p_open)) :
  satisfiable (∼∃'*p) :=
begin
  let T := set.range (λ x, sentence.to_pl (∼substs x p) (by simpa using p_open)),
  have : pl.Satisfiable (T ∪ pl.formula.equal_axioms L),
  { refine pl.compactness.mpr _,
    simp[T, set.subset_range_iff_exists_image_eq, set.finite_image_iff],
    intros s s_ss s_fin,
    have : ∃ u' sₑ,
      sₑ ⊆ pl.formula.equal_axioms L ∧
      s = (λ x, ∼sentence.to_pl (substs x p) _) '' u' ∪ sₑ,
    by simpa[set.subset_union_iff_exists, set.subset_range_iff_exists_image_eq] using s_ss,
    rcases this with ⟨u', sₑ, hsₑ, rfl⟩,
    simp at s_fin,
    have : ∃ u : finset (fin n → subterm L 0 0),
      (λ x, ∼sentence.to_pl (substs x p) (by simpa using p_open)) '' u = (λ x, ∼sentence.to_pl (substs x p) (by simpa using p_open)) '' u',
    { have : ∃ u ⊆ u', u.finite ∧ (λ x, ∼sentence.to_pl (substs x p) _) '' u = (λ x, ∼sentence.to_pl (substs x p) _) '' u',
      from set.image_finite_inversion s_fin.1,
      rcases this with ⟨u, hu, u_fin, eqn⟩,
      refine ⟨set.finite.to_finset u_fin, by simpa using eqn⟩ },
    rcases this with ⟨u, eqn⟩,
    suffices : pl.Satisfiable ((λ x, ∼sentence.to_pl (substs x p) (by simpa using p_open)) '' u ∪ sₑ),
    by simpa[eqn] using this,
    rcases H u.to_list with ⟨V, hVₑ, hVᵤ⟩,
    refine ⟨V, _⟩,
    rintros q (hq | hq),
    { simp at hq, rcases hq with ⟨x, hx, rfl⟩,
      by simpa using hVᵤ x (by simpa using hx) },
    { exact hVₑ (hsₑ hq) } },
  rcases this with ⟨V, hV⟩, simp at hV,
  have hVT : V ⊧ T, from hV.1,
  have hVeq : V ⊧ pl.formula.equal_axioms L, from hV.2,
  refine ⟨Herbrand V hVeq, _⟩,
  simp[sentence_models_def, Herbrand.val_iff_subst p p_open], intros x,
  have : V ⊧ ∼sentence.to_pl (substs (Herbrand.qu_inv ∘ x) p) (by simpa using p_open), from hVT (by simp[T]),
  simpa using this
end

theorem valid_iff_consequence (p : subformula L 0 n) (hp : p.is_open) :
  valid (∃'*p) ↔
  ∃ v : list (fin n → herbrand_universe L),
  pl.formula.equal_axioms L ⊧ (v.map (λ t, sentence.to_pl (substs t p) (by simpa using hp))).disjunction :=
⟨ begin
    contrapose, assume h,
    have : ∀ (w : list (fin n → herbrand_universe L)),
     ∃ V : pl.Structure (herbrand_basis L), V ⊧ pl.formula.equal_axioms L ∧
     ∀ x ∈ w, V ⊧ sentence.to_pl (∼substs x p) (by simpa using hp),
    by simpa[pl.tautology_iff, pl.models_def, pl.consequence_def] using h,
    have : satisfiable (∼∃'* p), from Herbrand_aux p hp this,
    simpa using this,
  end, 
  begin
    rintros ⟨v, h⟩ S, simp[sentence_models_def],
    have : ∃ x ∈ v, val S fin.nil (subterm.val S fin.nil fin.nil ∘ x) p,
    by simpa [to_pl.models, sentence_models_def] using
      pl.consequence_def.mp h S.to_pl (Structure.to_pl.to_pl_equal_axioms S),
    rcases this with ⟨x, _, h⟩,
    exact ⟨subterm.val S fin.nil fin.nil ∘ x, h⟩
  end⟩

end herbrand_universe

namespace subterm
variables 

end subterm

end fol