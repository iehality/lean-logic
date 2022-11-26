import QL.FOL.completeness.skolem QL.FOL.completeness.herbrand

universes u
open_locale logic_symbol aclogic

variables {L : fol.language.{u}}

namespace pl
variables {T : Theory (fol.herbrand_basis L)}

namespace provable

lemma to_fol {p : formula (fol.herbrand_basis L)} (h : equal_axioms L ⊢ p) : ⬝⊢ p.to_fol :=
begin
  simp[axiomatic_classical_logic.empty_axiom],
  apply rec'_on h,
  { intros p q _ _ IHpq IHp, simp at IHpq, refine IHpq ⨀ IHp },
  { intros p hp, rcases hp; simp },
  { simp },
  { simp },
  { simp },
  { simp }
end

end provable

end pl

namespace fol

namespace formula
variables {m : ℕ}

lemma to_snf_univ_closure (p : formula L m) :
  ∃ n (p₀ : subformula (L + L.skolem) m n) (h : p₀.is_open), p.to_snf = ∀'*p₀ :=
pnf.univ_closure_to_formula p.to_pnf.skolemize (pnf.forall_pnf_skolemize _)

end formula

section compactness
open subformula language

def Theory.to_pl (T : Theory L) : pl.Theory (fol.herbrand_basis (L + L.skolem)) :=
⋃ (σ : sentence L) (hσ : σ ∈ T) {n} (p₀ : subformula (L + L.skolem) 0 n) (hp₀ : p₀.is_open)
  (h : σ.to_snf = (∀'*p₀ : subformula _ _ _)),
  set.range (λ x, sentence.to_pl (substs x p₀) (by simpa using hp₀))

lemma Satisfiable_of_to_pl_Satisfiable (T : Theory L) (h : pl.Satisfiable (T.to_pl ∪ pl.equal_axioms (L + L.skolem))) : Satisfiable T :=
begin
  rcases h with ⟨V, hV⟩,
  have hVΓ : V ⊧ T.to_pl, from (logic.semantics.models_union.mp hV).1,
  have hVeq : V ⊧ pl.equal_axioms _, from (logic.semantics.models_union.mp hV).2,
  let S := Structure.Herbrand V hVeq,
  have : ∀ {σ : sentence L} (hσ : σ ∈ T), S ⊧ σ.to_snf,
  { intros σ hσ, rcases formula.to_snf_univ_closure σ with ⟨n, p₀, hp₀, h⟩,
    have : ∀ x, S ⊧ substs x p₀,
    { intros x,
      have : V ⊧ sentence.to_pl (substs (Structure.Herbrand.qu_inv ∘ subterm.val S fin.nil fin.nil ∘ x) p₀) _,
      from hVΓ (by simp[Theory.to_pl]; refine ⟨σ, hσ, n, p₀, h, hp₀, _, rfl⟩),
      simpa[sentence_models_def, Structure.Herbrand.val_iff_subst p₀ hp₀] using this },  
    have : S ⊧ ∀'*p₀, by simpa[Structure.Herbrand.models_forall_iff] using this,
    simpa[h] using this },
  refine ⟨S.restrict add_left, by intros σ hσ; exact skolem.restrict_models _ (this hσ)⟩
end

theorem compactness {T : Theory L} : Satisfiable T ↔ (∀ u ⊆ T, u.finite → Satisfiable u) :=
⟨by rintros ⟨S, hS⟩ u hu u_fin; refine ⟨S, logic.semantics.models_of_ss hu hS⟩,
begin
  contrapose, intros h,
  have : ¬pl.Satisfiable (T.to_pl ∪ pl.equal_axioms (L + L.skolem)),
  from mt (Satisfiable_of_to_pl_Satisfiable T) h,
  rcases pl.compactness'.mp this with ⟨u, u_ss, u_fin, hu⟩,
  let g := u \ pl.equal_axioms _,
  have : g ⊆ T.to_pl, by simp[g, set.diff_subset_iff, set.union_comm, u_ss],
  have hg_to_fol : pl.formula.to_fol '' g ⊆
    ⋃ (σ ∈ T) {n} (p₀ : subformula (L + L.skolem) 0 n) (hp₀ : p₀.is_open) (h : to_snf σ = (∀'*p₀ : subformula _ _ _)),
    set.range (λ x, substs x p₀),
  by simpa[Theory.to_pl, set.image_Union, ←set.range_comp, (∘)] using set.image_subset pl.formula.to_fol this,    
  have hg_to_fol_fin : (pl.formula.to_fol '' g).finite , from set.finite.image _ (set.finite.diff u_fin _),
  have : ¬pl.Satisfiable (g ∪ pl.equal_axioms _),
  { intros A, suffices : pl.Satisfiable u, by contradiction, refine logic.semantics.Satisfiable_of_ss (by simp) A },
  have : ¬Satisfiable (pl.formula.to_fol '' g), from mt Structure.Satisfies_to_fol_iff.mp this,
  rcases set.finite_subset_Union hg_to_fol_fin hg_to_fol with ⟨s, s_fin, hs⟩,
  simp[-set.image_subset_iff] at hs ⊢,
  refine ⟨s ∩ T, by simp, set.finite.inter_of_left s_fin T, _⟩,
  assume A,
  suffices : Satisfiable (pl.formula.to_fol '' g), by contradiction,
  rcases skolem.Satisfiability.mpr A with ⟨S, hS⟩,
  refine ⟨S, _⟩, intros p hp,
  have : ∃ (σ ∈ s ∩ T) {n} (p₀ : subformula (L + L.skolem) 0 n),
    p₀.is_open ∧ to_snf σ = (∀'*p₀ : subformula _ _ _) ∧ ∃ x, substs x p₀ = p,
  by simpa[and_assoc] using hs hp,
  rcases this with ⟨σ, hσ, n, p₀, hp₀, h, x, rfl⟩,
  have : S ⊧ ∀'*p₀, { rw←h, refine hS (set.mem_image_of_mem _ hσ) },
  simp[sentence_models_def] at this ⊢, exact this _  
end⟩

end compactness

open subformula logic logic.Theory
     axiomatic_classical_logic' axiomatic_classical_logic
     Structure
variables {L} {m n : ℕ} [inhabited (L.fn 0)]

lemma provable_of_valid_aux (p : subformula L 0 n) (hp : p.is_open) (H : valid (∃'*p)) : ∅ ⊢ ∃'*p :=
begin
  rcases (valid_iff_pl_consequence p hp).mp H with ⟨v, hv⟩,
  have lmm₁ : ∅ ⊢ (v.map (λ t, substs t p)).disjunction ⟶ ∃'*p, from ldisj_imply_of (by simp),
  have lmm₂ : ∅ ⊢ (v.map (λ t, substs t p)).disjunction,
    by simpa[(∘)] using pl.provable.to_fol (pl.completeness.mpr hv),
  exact lmm₁ ⨀ lmm₂
end

lemma provable_of_valid (σ : sentence L) (H : valid σ) : ∅ ⊢ σ :=
begin
  rcases formula.to_snf_univ_closure (∼σ) with ⟨n, p, hp, h⟩,
  
end


end fol
