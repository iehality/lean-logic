import language_extension consistency
open encodable

universes u

namespace fopl
open term formula
variables (L : language.{u}) (T : theory L)

namespace henkin
open language language.extension language.consts_pelimination theory

@[reducible] def extend : language.{u} := L + consts (formula L)

@[reducible] def Lang : ℕ → language
| 0     := L
| (n+1) := extend (Lang n)

def Consts : Type u := Σ n, formula (Lang L n)

variables {L}

def henkin_axiom (p : formula L) : formula (extend L) := (∐ ↑p) ⟶ rew ı[0 ⇝ p] ↑p

@[reducible] def theory_extend : theory (extend L) := ↑T ∪ set.range henkin_axiom

section
open axiomatic_classical_logic axiomatic_classical_logic' provable

variables {S : theory (extend L)} (Γ : list (formula L))

lemma consistent_of_disjoint (S_consis : S.consistent) (disj : ∀ p ∈ S, disjoint Γ p) (p : formula (extend L)) :
  ¬S ⊢ (∏[Γ.length] ⁻((pelimination' Γ).p 0 p)) → theory.consistent (S +{ p }) := λ not_b,
begin
  simp [theory.consistent_iff_bot],
  intros b,
  have : S ⊢ ⁻p, from of_equiv_p (deduction.mp b) (equiv_symm $ neg_iff _),
  have : S ⊢ ∏[Γ.length] ⁻(pelimination' Γ).p 0 p,
  { have := provable_pelimination_of_disjoint Γ S (⁻p) disj this, simp at this, exact this },
  contradiction
end

lemma tauto (p : formula L) : S ⊢ ∐ ((∐ ↑p)^1 ⟶ ↑p) :=
begin
  have lmm₁ : S ⊢ (∐ ↑p) ⟶ ∐ ((∐ ↑p)^1 ⟶ ↑p),
  { simp[pnf_imply_ex_iff_fal_imply₁], refine generalize (deduction.mp _),
    refine use #0 _, simp[formula.nested_rew] },
  have lmm₂ : S ⊢ ⁻(∐ ↑p) ⟶ ∐ ((∐ ↑p)^1 ⟶ ↑p),
  { refine deduction.mp (use #0 (deduction.mp _)), simp,
    show S +{ ⁻∐ ↑p } +{ ∐ ↑p } ⊢ rew ı[0 ⇝ #0] ↑p,
    exact explosion (show S +{ ⁻∐ ↑p } +{ ∐ ↑p } ⊢ ∐ ↑p, by simp) (show S +{ ⁻∐ ↑p } +{ ∐ ↑p } ⊢ ⁻∐ ↑p, by simp) },
  exact cases_of _ _ lmm₁ lmm₂
end

@[simp] lemma pelimination'_henkin_axiom (p : formula L) : (pelimination' ([p])).p 0 (henkin_axiom p) = ((∐ ↑p)^1 ⟶ ↑p) :=
begin
  simp[henkin_axiom, pelimination'_subst, pelimination_coe_eq_pow_coe_aux],
  have : pelim_aux_t ([p]) 0 ↑↑p = (#0 : term (extend L)),
  { have : pelim_aux_t ([p]) 0 ↑p = (#(list.index_of p ([p]) + 0) : term (extend L)), from pelim_aux_t_consts_of_Γ ([p]) p (by simp) 0,
    simp at this, exact this },
  simp[this, formula.nested_rew, show (#0 ⌢ λ x, #(1 + x) : ℕ → term (extend L)) = ı, by { funext x, rcases x; simp[add_comm 1] }],
  simp[formula.pow_eq, add_comm 1]
end

lemma consts_of_henkin_axiom {p : formula L} {c} (mem : c ∈ consts_of_p (henkin_axiom p)) : c = p :=
begin
  simp[henkin_axiom, consts_of_p] at mem,
  rcases mem with ⟨t, (t_mem | t_mem), c_mem⟩,
  { rcases language_translation_coe.fun_formula_inversion_of_mem t_mem with ⟨t, t_mem, rfl⟩, simp at c_mem, contradiction },
  { rcases formula.rew_inversion_or_le_of_mem_rew t_mem with (⟨t, t_mem', k, rfl⟩ | ⟨k, n, le⟩),
    { rcases language_translation_coe.fun_formula_inversion_of_mem t_mem' with ⟨t, t_mem'', rfl⟩,
      simp[subst_pow] at c_mem,
      rcases mem_of_consts_of_t_subst _ _ _ c_mem with (c_mem | c_mem),
      { simp at c_mem, contradiction },
      {exact eq_of_consts_of_t_coe.mp c_mem } },
    { simp[subst_pow] at le, have : n < k ∨ n = k ∨ k < n , exact trichotomous n k, rcases this with (lt | rfl | lt),
      { simp[lt] at le, simp[le] at c_mem, contradiction },
      { simp[consts.coe_def, show (↑(consts.c p) : (extend L).fn 0) = sum.inr (consts.c p), from rfl, le_iff_lt_or_eq] at le,
        rcases le with (⟨⟨_, A⟩, _⟩ | rfl), { simp at A, contradiction }, { simp at c_mem, exact c_mem } },
      { simp[lt] at le, simp[le] at c_mem, contradiction } } }
end

lemma disjoint_of_ne (p q : formula L) (ne : p ≠ q) : disjoint ([p]) (henkin_axiom q) := λ p mem,
by { simp at mem, rcases mem with rfl, intros mem, have : p = q, from consts_of_henkin_axiom mem, contradiction }

end

theorem theory_extend_consistent (consis : T.consistent) : (theory_extend T).consistent :=
begin
  have : (↑T : theory (extend L)).consistent, from language.add_consts.consistent_iff.mpr consis,
  refine of_finite_induction this _,
  intros s s_ss φ φ_mem p_nmem s_fin consis',
  let U := ↑T ∪ s,
  rcases φ_mem with ⟨φ, rfl⟩,
  show theory.consistent (U +{ henkin_axiom φ }),
  have disj : ∀ p ∈ U, disjoint ([φ]) p,
  { intros p mem, simp[U] at mem, rcases mem,
    { rcases mem with ⟨p, mem, rfl⟩, show disjoint ([φ]) (↑p), intros h, simp },
    { have : p ∈ set.range henkin_axiom, from s_ss mem,
      rcases this with ⟨p, rfl⟩,
      have : φ ≠ p, { rintros rfl, contradiction },
      exact disjoint_of_ne _ _ this } },
  have : ¬U ⊢ ∏ ⁻((∐ ↑φ)^1 ⟶ ↑φ),
  { intros b,
    have : U ⊢ ⁻∏ ⁻((∐ ↑φ)^1 ⟶ ↑φ), from tauto φ,
    have : ¬U.consistent, { simp[theory.consistent], refine ⟨_, b, this⟩ },
    contradiction },
  exact consistent_of_disjoint ([φ]) consis' disj (henkin_axiom φ) (by simp; exact this)
end

end henkin

end fopl