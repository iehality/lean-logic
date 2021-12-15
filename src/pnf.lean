import deduction lindenbaum

universes u v

namespace fopl

variables (L : language.{u})

local infix ` ≃₁ `:80 := ((≃) : term L → term L → formula L)

local prefix `∏₁ `:64 := (has_univ_quantifier.univ : formula L → formula L)

local prefix `∐₁ `:64 := (has_exists_quantifier.ex : formula L → formula L)

structure pnf : Type u := 
(quantifier : list bool)
(p : formula L)
(openform : p.is_open)

local notation `𝚷` := bool.tt

local notation `𝚺` := bool.ff

variables {L}



namespace pnf

def fal : pnf L → pnf L
| ⟨Q, p, h⟩ := ⟨𝚷 :: Q, p, h⟩

def ex : pnf L → pnf L
| ⟨Q, p, h⟩ := ⟨𝚺 :: Q, p, h⟩

instance : has_univ_quantifier (pnf L) (pnf L) := ⟨pnf.fal⟩

instance : has_exists_quantifier (pnf L) (pnf L) := ⟨pnf.ex⟩

@[simp] lemma fal_eq (Q : list bool) (p : formula L) (h) : (∏ (⟨Q, p, h⟩ : pnf L) : pnf L) = ⟨𝚷 :: Q, p, h⟩ := rfl

@[simp] lemma ex_eq (Q : list bool) (p : formula L) (h) : (∐ (⟨Q, p, h⟩ : pnf L) : pnf L) = ⟨𝚺 :: Q, p, h⟩ := rfl

@[simp] def to_openform : pnf L → formula L
| ⟨Q, p, h⟩ := p

@[simp] def to_formula : pnf L → formula L
| ⟨[], p, h⟩     := p
| ⟨𝚷 :: Q, p, h⟩ := ∏ to_formula ⟨Q, p, h⟩
| ⟨𝚺 :: Q, p, h⟩ := ∐ to_formula ⟨Q, p, h⟩

@[simp] def fal_to_formula : ∀ p : pnf L, (∏ p : pnf L).to_formula = ∏ p.to_formula
| ⟨Q, p, h⟩     := by simp

@[simp] def ex_to_formula : ∀ p : pnf L, (∐ p : pnf L).to_formula = ∐ p.to_formula
| ⟨Q, p, h⟩     := by simp

@[simp] def rank : pnf L → ℕ := λ p, p.1.length

def rew (s : ℕ → term L) : pnf L → pnf L
| ⟨Q, p, h⟩ := ⟨Q, p.rew (s^Q.length), by simp[h]⟩

instance : has_pow (pnf L) ℕ := ⟨λ p i, p.rew (λ x, #(x + i))⟩

lemma rew_eq : ∀ (p : pnf L) (s : ℕ → term L), (p.rew s).to_formula = p.to_formula.rew s
| ⟨[], p, h⟩     s := by simp[rew]
| ⟨𝚷 :: Q, p, h⟩ s := by simp[rew, ←rew_eq ⟨Q, p, by simp[h]⟩ (s^1), rewriting_sf_itr.pow_add,
    show 1 + Q.length = Q.length + 1, from add_comm _ _]
| ⟨𝚺 :: Q, p, h⟩ s := by simp[rew, ←rew_eq ⟨Q, p, by simp[h]⟩ (s^1), rewriting_sf_itr.pow_add,
    show 1 + Q.length = Q.length + 1, from add_comm _ _]

lemma pow_eq (p : pnf L) (i : ℕ) : (p^i).to_formula = p.to_formula^i :=
by simp[formula.pow_eq, rew_eq, has_pow.pow]

@[simp] def neg : pnf L → pnf L
| ⟨[], p, h⟩ := ⟨[], ⁻p, by simp[h]⟩
| ⟨𝚷 :: Q, p, h⟩ := ∐ neg ⟨Q, p, by simp[h]⟩
| ⟨𝚺 :: Q, p, h⟩ := ∏ neg ⟨Q, p, by simp[h]⟩
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf rank⟩]}

@[simp] lemma rew_rank : ∀ (p : pnf L) (s), (p.rew s).rank = p.rank
| ⟨[], p, h⟩     s := by simp[rew]
| ⟨𝚷 :: Q, p, h⟩ s := by simp[rew]
| ⟨𝚺 :: Q, p, h⟩ s := by simp[rew]

@[simp] lemma pow_rank (p : pnf L) (i : ℕ) : (p^i).rank = p.rank :=
by simp[has_pow.pow]

@[simp] def imply : pnf L → pnf L → pnf L
| ⟨[], p₁, h₁⟩      ⟨[], p₂, h₂⟩      := ⟨[], p₁ ⟶ p₂, by simp[h₁, h₂]⟩
| ⟨[], p₁, h₁⟩      ⟨𝚷 :: Q₂, p₂, h₂⟩ := ∏ imply (⟨[], p₁^1, by simp[h₁]⟩) ⟨Q₂, p₂, h₂⟩
| ⟨[], p₁, h₁⟩      ⟨𝚺 :: Q₂, p₂, h₂⟩ := ∐ imply ⟨[], p₁^1, by simp[h₁]⟩ ⟨Q₂, p₂, h₂⟩
| ⟨𝚷 :: Q₁, p₁, h₁⟩ ⟨[], p₂, h₂⟩      := ∐ imply ⟨Q₁, p₁, by simp[h₁]⟩ ⟨[], p₂^1, by simp[h₂]⟩
| ⟨𝚷 :: Q₁, p₁, h₁⟩ ⟨𝚷 :: Q₂, p₂, h₂⟩ :=
    ∐ (∏ imply (pnf.mk Q₁ p₁ h₁^1) ((pnf.mk Q₂ p₂ (by simp[h₂])).rew ι-{1}) : pnf L)
| ⟨𝚷 :: Q₁, p₁, h₁⟩ ⟨𝚺 :: Q₂, p₂, h₂⟩ :=
    ∐ (∐ imply (pnf.mk Q₁ p₁ h₁^1) ((pnf.mk Q₂ p₂ (by simp[h₂])).rew ι-{1}) : pnf L)
| ⟨𝚺 :: Q₁, p₁, h₁⟩ ⟨[], p₂, h₂⟩      := ∏ imply ⟨Q₁, p₁, by simp[h₁]⟩ ⟨[], p₂^1, by simp[h₂]⟩
| ⟨𝚺 :: Q₁, p₁, h₁⟩ ⟨𝚷 :: Q₂, p₂, h₂⟩ :=
    ∏ (∏ imply (pnf.mk Q₁ p₁ h₁^1) ((pnf.mk Q₂ p₂ (by simp[h₂])).rew ι-{1}) : pnf L)
| ⟨𝚺 :: Q₁, p₁, h₁⟩ ⟨𝚺 :: Q₂, p₂, h₂⟩ :=
    ∏ (∐ imply (pnf.mk Q₁ p₁ h₁^1) ((pnf.mk Q₂ p₂ (by simp[h₂])).rew ι-{1}) : pnf L)
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.fst.rank + x.snd.rank)⟩]}

end pnf

namespace formula

@[simp] def to_pnf : formula L → pnf L
| (app p v) := ⟨[], app p v, by simp⟩
| ((t : term L) ≃ u) := ⟨[], (t : term L) ≃ u, by simp⟩
| (p ⟶ q) := (to_pnf p).imply (to_pnf q)
| (⁻p) := (to_pnf p).neg
| (∏ (p : formula L)) := ∏ (to_pnf p)

end formula

lemma iff_pnf_imply : ∀ (p q : pnf L) (T : theory L), T ⊢ (p.imply q).to_formula ⟷ p.to_formula ⟶ q.to_formula
| ⟨[], p₁, h₁⟩      ⟨[], p₂, h₂⟩      T := by simp
| ⟨[], p₁, h₁⟩      ⟨𝚷 :: Q₂, p₂, h₂⟩ T := by { simp, have ih := iff_pnf_imply ⟨[], p₁^1, by simp[h₁]⟩ ⟨Q₂, p₂, h₂⟩,
    calc     ∏ ((pnf.mk ([]) (p₁^1) (by simp[h₁])).imply (pnf.mk Q₂ p₂ h₂)).to_formula
        ≈[T] ∏ ((pnf.mk ([]) (p₁^1) (by simp[h₁])).to_formula ⟶ (pnf.mk Q₂ p₂ h₂).to_formula)
    : provable.equiv_univ_of_equiv (ih _)
    ... ≈[T] p₁ ⟶ ∏ (pnf.mk Q₂ p₂ h₂).to_formula
    : by { symmetry, refine by simp[classical_logic.equiv] } }
| ⟨[], p₁, h₁⟩      ⟨𝚺 :: Q₂, p₂, h₂⟩ T := by { simp, have ih := iff_pnf_imply ⟨[], p₁^1, by simp[h₁]⟩ ⟨Q₂, p₂, h₂⟩,
    calc     ∐ ((pnf.mk ([]) (p₁^1) (by simp[h₁])).imply (pnf.mk Q₂ p₂ h₂)).to_formula
        ≈[T] ∐ ((pnf.mk ([]) (p₁^1) (by simp[h₁])).to_formula ⟶ (pnf.mk Q₂ p₂ h₂).to_formula)
    : provable.equiv_ex_of_equiv (ih _)
    ... ≈[T] p₁ ⟶ ∐ (pnf.mk Q₂ p₂ h₂).to_formula
    : by { symmetry, simp[classical_logic.equiv] } }
| ⟨𝚷 :: Q₁, p₁, h₁⟩ ⟨[], p₂, h₂⟩      T := by { simp, have ih := iff_pnf_imply ⟨Q₁, p₁, h₁⟩ (pnf.mk ([]) p₂ h₂^1),
    calc     ∐ ((pnf.mk Q₁ p₁ h₁).imply (pnf.mk ([]) p₂ h₂^1)).to_formula
        ≈[T] ∐ ((pnf.mk Q₁ p₁ h₁).to_formula ⟶ (pnf.mk ([]) p₂ h₂^1).to_formula)
    : provable.equiv_ex_of_equiv (ih _)
    ... ≈[T] ∏ (pnf.mk Q₁ p₁ (by simp[h₁])).to_formula ⟶ p₂
    : by { symmetry, simp[classical_logic.equiv, pnf.pow_eq] } }
| ⟨𝚷 :: Q₁, p₁, h₁⟩ ⟨𝚷 :: Q₂, p₂, h₂⟩ T := by { simp,
    have ih := iff_pnf_imply (pnf.mk Q₁ p₁ h₁^1) ((pnf.mk Q₂ p₂ h₂).rew ι-{1}),
    calc     ∐ ∏ ((pnf.mk Q₁ p₁ h₁^1).imply ((pnf.mk Q₂ p₂ h₂).rew ι-{1})).to_formula
        ≈[T] ∐ ∏ ((pnf.mk Q₁ p₁ h₁^1).to_formula ⟶ ((pnf.mk Q₂ p₂ h₂).rew ι-{1}).to_formula)
    : provable.equiv_ex_of_equiv (provable.equiv_univ_of_equiv (ih _))
    ... ≈[T] ∐ ((pnf.mk Q₁ p₁ h₁).to_formula ⟶ (∏ (pnf.mk Q₂ p₂ h₂).to_formula)^1)
    : by { show _ ≈[T] _, symmetry, simp[pnf.pow_eq, pnf.rew_eq, classical_logic.equiv, formula.fal_pow_discard],
           refine provable.equiv_ex_of_equiv (by simp) }
    ... ≈[T] ∏ (pnf.mk Q₁ p₁ h₁).to_formula ⟶ ∏ (pnf.mk Q₂ p₂ h₂).to_formula
    : by { symmetry, simp [classical_logic.equiv] } }
| ⟨𝚷 :: Q₁, p₁, h₁⟩ ⟨𝚺 :: Q₂, p₂, h₂⟩ T := by { simp, 
    have ih := iff_pnf_imply (pnf.mk Q₁ p₁ h₁^1) ((pnf.mk Q₂ p₂ h₂).rew ι-{1}),
    calc     ∐ ∐ ((pnf.mk Q₁ p₁ h₁^1).imply ((pnf.mk Q₂ p₂ h₂).rew ι-{1})).to_formula
        ≈[T] ∐ ∐ ((pnf.mk Q₁ p₁ h₁^1).to_formula ⟶ ((pnf.mk Q₂ p₂ h₂).rew ι-{1}).to_formula)
    : provable.equiv_ex_of_equiv (provable.equiv_ex_of_equiv (ih _))
    ... ≈[T] ∐ ((pnf.mk Q₁ p₁ h₁).to_formula ⟶ (∐ (pnf.mk Q₂ p₂ h₂).to_formula)^1)
    : by { show _ ≈[T] _, symmetry, simp[pnf.pow_eq, pnf.rew_eq, classical_logic.equiv, formula.ex_pow_discard],
           refine provable.equiv_ex_of_equiv (by simp) }
    ... ≈[T] ∏ (pnf.mk Q₁ p₁ h₁).to_formula ⟶ ∐ (pnf.mk Q₂ p₂ h₂).to_formula
    : by { symmetry, simp [classical_logic.equiv] } }
| ⟨𝚺 :: Q₁, p₁, h₁⟩ ⟨[], p₂, h₂⟩      T := by { simp, have ih := iff_pnf_imply ⟨Q₁, p₁, h₁⟩ (pnf.mk ([]) p₂ h₂^1),
    calc     ∏ ((pnf.mk Q₁ p₁ h₁).imply (pnf.mk ([]) p₂ h₂^1)).to_formula
        ≈[T] ∏ ((pnf.mk Q₁ p₁ h₁).to_formula ⟶ (pnf.mk ([]) p₂ h₂^1).to_formula)
    : provable.equiv_univ_of_equiv (ih _)
    ... ≈[T] ∐ (pnf.mk Q₁ p₁ (by simp[h₁])).to_formula ⟶ p₂
    : by { symmetry, simp[classical_logic.equiv, pnf.pow_eq] } }
| ⟨𝚺 :: Q₁, p₁, h₁⟩ ⟨𝚷 :: Q₂, p₂, h₂⟩ T := by { simp,
    have ih := iff_pnf_imply (pnf.mk Q₁ p₁ h₁^1) ((pnf.mk Q₂ p₂ h₂).rew ι-{1}),
    calc     ∏ ∏ ((pnf.mk Q₁ p₁ h₁^1).imply ((pnf.mk Q₂ p₂ h₂).rew ι-{1})).to_formula
        ≈[T] ∏ ∏ ((pnf.mk Q₁ p₁ h₁^1).to_formula ⟶ ((pnf.mk Q₂ p₂ h₂).rew ι-{1}).to_formula)
    : provable.equiv_univ_of_equiv (provable.equiv_univ_of_equiv (ih _))
    ... ≈[T] ∏ ((pnf.mk Q₁ p₁ h₁).to_formula ⟶ (∏ (pnf.mk Q₂ p₂ h₂).to_formula)^1)
    : by { show _ ≈[T] _, symmetry, simp[pnf.pow_eq, pnf.rew_eq, classical_logic.equiv, formula.fal_pow_discard],
           refine provable.equiv_univ_of_equiv (by simp) }
    ... ≈[T] ∐ (pnf.mk Q₁ p₁ h₁).to_formula ⟶ ∏ (pnf.mk Q₂ p₂ h₂).to_formula
    : by { symmetry, simp [classical_logic.equiv] } }
| ⟨𝚺 :: Q₁, p₁, h₁⟩ ⟨𝚺 :: Q₂, p₂, h₂⟩ T := by { simp, 
    have ih := iff_pnf_imply (pnf.mk Q₁ p₁ h₁^1) ((pnf.mk Q₂ p₂ h₂).rew ι-{1}),
    calc     ∏ ∐ ((pnf.mk Q₁ p₁ h₁^1).imply ((pnf.mk Q₂ p₂ h₂).rew ι-{1})).to_formula
        ≈[T] ∏ ∐ ((pnf.mk Q₁ p₁ h₁^1).to_formula ⟶ ((pnf.mk Q₂ p₂ h₂).rew ι-{1}).to_formula)
    : provable.equiv_univ_of_equiv (provable.equiv_ex_of_equiv (ih _))
    ... ≈[T] ∏ ((pnf.mk Q₁ p₁ h₁).to_formula ⟶ (∐ (pnf.mk Q₂ p₂ h₂).to_formula)^1)
    : by { show _ ≈[T] _, symmetry, simp[pnf.pow_eq, pnf.rew_eq, classical_logic.equiv, formula.ex_pow_discard],
           refine provable.equiv_univ_of_equiv (by simp) }
    ... ≈[T] ∐ (pnf.mk Q₁ p₁ h₁).to_formula ⟶ ∐ (pnf.mk Q₂ p₂ h₂).to_formula
    : by { symmetry, simp [classical_logic.equiv] } }
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.1.rank + x.2.1.rank)⟩]}

lemma iff_pnf_neg : ∀ (p : pnf L) (T : theory L) , T ⊢ p.neg.to_formula ⟷ ⁻p.to_formula
| ⟨[], p, h⟩     T := by simp
| ⟨𝚷 :: Q, p, h⟩ T := by simp;
    calc ∐ (pnf.mk Q p (by simp[h])).neg.to_formula ≈[T] ∐ ⁻(pnf.mk Q p (by simp[h])).to_formula
    : provable.equiv_ex_of_equiv (iff_pnf_neg ⟨Q, p, by simp[h]⟩ _)
                                                 ... ≈[T] ⁻∏ (pnf.mk Q p (by simp[h])).to_formula
    : classical_logic.equiv_neg_of_equiv (provable.equiv_univ_of_equiv (by simp))
| ⟨𝚺 :: Q, p, h⟩ T := by { simp,
    calc     ∏ (pnf.mk Q p (by simp[h])).neg.to_formula ≈[T] ∏ ⁻(pnf.mk Q p (by simp[h])).to_formula
    : provable.equiv_univ_of_equiv (iff_pnf_neg ⟨Q, p, by simp[h]⟩ _)
                                                    ... ≈[T] ⁻∐ (pnf.mk Q p (by simp[h])).to_formula
    : by { simp[has_exists_quantifier.ex, formula.ex, classical_logic.equiv] } }

lemma iff_pnf : ∀ (p : formula L) {T : theory L},  T ⊢ p ⟷ p.to_pnf.to_formula
| (formula.app p v) T := by simp
| (t ≃₁ u)          T := by simp
| (p ⟶ q)          T := by { simp, 
    have : T ⊢ p ⟶ q ⟷ (p.to_pnf.to_formula ⟶ q.to_pnf.to_formula),
      from classical_logic.equiv_imply_of_equiv (iff_pnf p) (iff_pnf q),
    exact classical_logic.equiv_trans this (classical_logic.equiv_symm (iff_pnf_imply p.to_pnf q.to_pnf T)) }
| (⁻p)              T := by { simp,
    have : T ⊢ ⁻p ⟷ ⁻p.to_pnf.to_formula, from classical_logic.equiv_neg_of_equiv (iff_pnf p),
    exact classical_logic.equiv_trans this (classical_logic.equiv_symm (iff_pnf_neg p.to_pnf T)) }
| (∏₁ p)           T := by { simp, refine provable.equiv_univ_of_equiv (iff_pnf p) }



end fopl