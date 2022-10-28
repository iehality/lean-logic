import FOL.completeness

universes u v

namespace fol
open_locale logic_symbol
variables {L L₁ L₂ L₃ : language.{u}} {T₁ U₁ : Theory L₁} {T₂ U₂ : Theory L₂} {T₃ U₃ : Theory L₃} 
open formula language language.language_translation language.language_translation_coe

namespace Theory

section
variables [closed_Theory T₁] [closed_Theory U₁] [language_translation_coe L₁ L₂]
open axiomatic_classical_logic' axiomatic_classical_logic

@[simp] lemma le_coe_iff : (↑T₁ : Theory L₂) ≤ ↑U₁ ↔ T₁ ≤ U₁ :=
⟨λ h p b,
  by { have : (↑T₁ : Theory L₂) ⊢ ↑p, by simp[b],
       have : ↑U₁ ⊢ ↑p, from h this,
       simpa using this },
 λ h p b,
begin
  rcases provable.proof_conjunction b with ⟨P, hP, b⟩,
  have : ∀ p, ∃ p₁ : formula L₁, p ∉ P ∨ p = ↑p₁ ∧ p₁ ∈ T₁,
  { intros p, by_cases hp : p ∈ P,
    { rcases language.language_translation_coe.mem_coe_iff.mp (hP p hp) with ⟨p₁, hp₁, rfl⟩,
      refine ⟨p₁, by simp[hp₁]⟩ },
    { simp[hp] } },
  choose coe_inv hcoe_inv using this,
  have : ↑U₁ ⊢ conjunction P,
    from provable.conjunction_provable
      (λ p hp, by { rcases language.language_translation_coe.mem_coe_iff.mp (hP p hp) with ⟨p₁, hp₁, rfl⟩,
        simpa using h (by_axiom hp₁) }),
  exact b.extend ⨀ this
end⟩

instance extend_coe [extend T₁ U₁] : extend (↑T₁ : Theory L₂) ↑U₁ := ⟨le_coe_iff.mpr extend.le⟩

end

variables [language_translation_coe L₁ L₂] {T₁ U₁} {T₂ U₂}

def lle (T₁ : Theory L₁) (T₂ : Theory L₂) : Prop := ∀ ⦃p : formula L₁⦄, T₁ ⊢ p → T₂ ⊢ p

@[simp] lemma lle_refl (T : Theory L) : lle T T := λ p h, by simp[coe_def_p, ltr]; exact h

@[trans] lemma lle_trans [language_translation_coe L₁ L₂] [language_translation_coe L₂ L₃] [language_translation_coe L₁ L₃]
  {T₁ : Theory L₁} {T₂ : Theory L₂} {T₃ : Theory L₃} [commutes L₁ L₂ L₃] :
  lle T₁ T₂ → lle T₂ T₃ → lle T₁ T₃ :=
λ le₁₂ le₂₃ p₁ b₁, by simpa[commutes.coe_coe_p_of_commute p₁] using le₂₃ (le₁₂ b₁)

lemma lle_of_le (h : T₁ ≤ U₁) : lle T₁ U₁ := λ p b, by simp[coe_def_p, ltr]; exact h b

variables {T₁ U₂} (T₂)

lemma lle_of_lle_of_le (h : lle T₁ T₂) (le : T₂ ≤ U₂) : lle T₁ U₂ := λ p b, le (h b)

variables {T₁ T₂} (U₁)

lemma lle_of_le_of_lle (le : T₁ ≤ U₁) (h : lle U₁ T₂) : lle T₁ T₂ := λ p b, h (le b)

variables (T₁)

lemma lle_coe [closed_Theory T₁] : lle T₁ (↑T₁ : Theory L₂) := λ p, by simp

end Theory

class lextend {L₁ : language.{u}} {L₂ : language.{u}} [language_translation_coe L₁ L₂] (T₁ : Theory L₁) (T₂ : Theory L₂) :=
(le : Theory.lle T₁ T₂)

lemma provable.lextend [language_translation_coe L₁ L₂] {T₁ : Theory L₁} {p} (b : T₁ ⊢ p) (T₂ : Theory L₂)
  [lextend T₁ T₂] : T₂ ⊢ p := lextend.le b

namespace Theory
variables  [language_translation_coe L₁ L₂] (T₁ U₁) (T₂ U₂)

instance lextend_refl : lextend T₁ T₁ := ⟨by simp⟩

instance lextend_of_extend [extend T₁ U₁] : lextend T₁ U₁ := ⟨lle_of_le extend.le⟩

instance lextend_sf [lextend T₁ T₂] : lextend (⤊T₁) (⤊T₂) :=
⟨λ p h, by {
  have : T₁ ⊢ ∏ p, from h.generalize,
  have : T₂ ⊢ ∏ p, from provable.lextend this T₂,
  have : ⤊T₂ ⊢ (∏ p)^1, from provable.sf_sf.mpr this,
  simpa[formula.nested_rew] using this ⊚ #0 }⟩

instance lextend_pow [ex : lextend T₁ T₂] (k : ℕ) : lextend (T₁^k) (T₂^k) :=
by { induction k with k IH ; simp[Theory.sf_itr_succ], { exact ex }, { exactI fol.Theory.lextend_sf _ _ } }

instance lextend_sf_closed [closed_Theory T₁] [lextend T₁ T₂] : lextend T₁ (⤊T₂) :=
by simpa using Theory.lextend_sf T₁ T₂

instance lextend_pow_closed [closed_Theory T₁] [lextend T₁ T₂] (k : ℕ) : lextend T₁ (T₂^k) :=
by simpa using Theory.lextend_pow T₁ T₂ k

instance lextend_coe [closed_Theory T₁] : lextend T₁ (↑T₁ : Theory L₂) := ⟨lle_coe T₁⟩

variables (T₁ U₂ T₂)

def lextend_of_lextend_of_extend [lextend T₁ T₂] [extend T₂ U₂] : lextend T₁ U₂ := ⟨lle_of_lle_of_le T₂ lextend.le extend.le⟩

variables (T₁ T₂ U₁)

def lextend_of_extend_of_lextend [extend T₁ U₁] [lextend U₁ T₂] : lextend T₁ T₂ := ⟨lle_of_le_of_lle U₁ extend.le lextend.le⟩

section
variables {T₁ T₂} [lextend T₁ T₂]

instance lextend_insert₁ (p) : lextend T₁ (T₂+{p}) := lextend_of_lextend_of_extend _ T₂ _

instance lextend_insert₂ (p q) : lextend T₁ (T₂+{p}+{q}) := lextend_of_lextend_of_extend _ T₂ _

instance lextend_insert₃ (p q r) : lextend T₁ (T₂+{p}+{q}+{r}) := lextend_of_lextend_of_extend _ T₂ _

instance lextend_insert₄ (p q r s) : lextend T₁ (T₂+{p}+{q}+{r}+{s}) := lextend_of_lextend_of_extend _ T₂ _

end

section
variables [language_translation_coe L₁ L₂] [language_translation_coe L₂ L₃] [language_translation_coe L₁ L₃]
  [commutes L₁ L₂ L₃] (T₁ T₂ T₃)

def lextend_trans [lextend T₁ T₂] [lextend T₂ T₃] : lextend T₁ T₃ := ⟨lle_trans (show lle T₁ T₂, from lextend.le) lextend.le⟩

end

end Theory

variables {L₁ L₂} (D : L₁.definitions L₂) [language_translation_coe (L₁ + L₂) L₃] 
  [language_translation_coe L₁ L₃] [commutes L₁ (L₁ + L₂) L₃] (T : Theory L₃) [lextend D.thy T]

@[simp] lemma language.definitions.fn' {n} (f : L₂.fn n) (v : finitary (term L₃) n) :
  T ⊢ (D.df_fn f : formula L₃).rew (term.app ((coe : (L₁ + L₂).fn n → L₃.fn n) (sum.inr f)) v ⌢ of_fin v) :=
by { have : T ⊢ ∏[n] (D.df_fn f : formula L₃).rew ı[0 ⇝ term.app ↑(sum.inr f)  (λ i, #i)],
       by simpa using provable.lextend (axiomatic_classical_logic'.by_axiom (language.definitions.mem_fn D f)) T,
     have := provable.nfal_subst'_finitary this v,
     simp[formula.nested_rew] at this,
     refine cast (by { congr, funext x, rcases x; simp }) this }

@[simp] lemma language.definitions.pr' {n} (r : L₂.pr n) (v : finitary (term L₃) n) :
  T ⊢ app ((coe : (L₁ + L₂).pr n → L₃.pr n) (sum.inr r)) v ⟷ (D.df_pr r : formula L₃).rew (of_fin v) :=
by { have : T ⊢ ∏[n] ❴↑(sum.inr r)❵ (λ i, #i) ⟷ ↑(D.df_pr r),
       by simpa using provable.lextend (axiomatic_classical_logic'.by_axiom (language.definitions.mem_pr D r)) T,
     simpa using provable.nfal_subst'_finitary this v }

lemma coe_inv_equiv' [language.predicate L₂] (p : formula (L₁ + L₂)) :
  T ⊢ p ⟷ ↑(formula.coe_inv D p : formula L₁) :=
by simpa using provable.lextend (coe_inv_equiv D p) T

end fol