import QL.FOL.deduction

-- Prenex normal form

universes u v

namespace fol
open_locale logic_symbol
open subformula

variables (L : language.{u}) (m n : ℕ)

inductive pnf (m : ℕ) : ℕ → Type u
| openformula {n} : Π p : subformula L m n, p.is_open → pnf n
| fal         {n} : pnf (n + 1) → pnf n
| ex          {n} : pnf (n + 1) → pnf n

variables {L m n}

instance : has_univ_quantifier' (pnf L m) := ⟨@pnf.fal L m⟩

instance : has_exists_quantifier' (pnf L m) := ⟨@pnf.ex L m⟩

namespace pnf

@[simp] def to_formula : Π {n}, pnf L m n → subformula L m n
| n (openformula p hp) := p
| n (fal φ)            := ∀'to_formula φ
| n (ex  φ)            := ∃'to_formula φ

instance : has_coe (pnf L m n) (subformula L m n) := ⟨@to_formula L m n⟩

@[simp] def neg : Π {n}, pnf L m n → pnf L m n
| n (openformula p hp) := openformula (∼p) (by simpa[is_open] using hp)
| n (fal φ)            := ∃'φ.neg
| n (ex φ)             := ∀'φ.neg

@[simp] def imply : Π {n}, pnf L m n → pnf L m n → pnf L m n
| n (openformula p hp) (openformula q hq) := openformula (p ⟶ q) (by simp; exact ⟨hp, hq⟩)
| n (openformula p hp) (fal φ)            := ∃'φ.neg
| n (openformula p hp) (ex φ)             := ∀'φ.neg


#check 0
/--/



#check 0
/-

@[simp] def rank : pnf L → ℕ := λ p, p.1.length

def rew (s : ℕ → term L) : pnf L → pnf L
| ⟨Q, p, h⟩ := ⟨Q, p.rew (s^Q.length), by simp[h]⟩

instance : has_pow (pnf L) ℕ := ⟨λ p i, p.rew (λ x, #(x + i))⟩

@[simp] lemma rew_to_formula_eq_to_formula_rew : ∀ (p : pnf L) (s : ℕ → term L),
  (p.rew s).to_formula = p.to_formula.rew s
| ⟨[], p, h⟩     s := by simp[rew]
| ⟨𝚷 :: Q, p, h⟩ s := by simp[rew, ←rew_to_formula_eq_to_formula_rew ⟨Q, p, by simp[h]⟩ (s^1),
    rewriting_sf_itr.pow_add, show 1 + Q.length = Q.length + 1, from add_comm _ _]
| ⟨𝚺 :: Q, p, h⟩ s := by simp[rew, ←rew_to_formula_eq_to_formula_rew ⟨Q, p, by simp[h]⟩ (s^1),
    rewriting_sf_itr.pow_add, show 1 + Q.length = Q.length + 1, from add_comm _ _]

@[simp] lemma pow_to_formula_eq_to_formula_pow (p : pnf L) (i : ℕ) : (p^i).to_formula = p.to_formula^i :=
by simp[formula.pow_eq, rew_to_formula_eq_to_formula_rew, has_pow.pow]

lemma rew_fal (Q : list bool) (p : formula L) {h} (s : ℕ → term L) :
  (⟨(𝚷 :: Q), p, h⟩ : pnf L).rew s = ∀.(⟨Q, p, h⟩ : pnf L).rew (s^1) :=
by simp[rew, show Q.length + 1 = 1 + Q.length, from add_comm _ _, rewriting_sf_itr.pow_add]

@[simp] lemma rew_fal' : ∀ (p : pnf L) (s : ℕ → term L),
  (∀.p : pnf L).rew s = ∀.(p.rew (s^1))
| ⟨Q, p, h⟩ s := by simp[rew_fal]

lemma rew_ex (Q : list bool) (p : formula L) {h} (s : ℕ → term L) :
  (⟨(𝚺 :: Q), p, h⟩ : pnf L).rew s = ∃.(⟨Q, p, h⟩ : pnf L).rew (s^1) :=
by simp[rew, show Q.length + 1 = 1 + Q.length, from add_comm _ _, rewriting_sf_itr.pow_add]

@[simp] lemma rew_ex' : ∀ (p : pnf L) (s : ℕ → term L),
  (∃.p : pnf L).rew s = ∃.(p.rew (s^1))
| ⟨Q, p, h⟩ s := by simp[rew_ex]

lemma nested_rew (p : pnf L) (s₀ s₁) :
  (p.rew s₀).rew s₁ = p.rew (λ x, (s₀ x).rew s₁) :=
to_formula_inj.mp (by simp[formula.nested_rew])

@[simp] lemma rew_rank : ∀ (p : pnf L) (s), (p.rew s).rank = p.rank
| ⟨[], p, h⟩     s := by simp[rew]
| ⟨𝚷 :: Q, p, h⟩ s := by simp[rew]
| ⟨𝚺 :: Q, p, h⟩ s := by simp[rew]

@[simp] lemma pow_rank (p : pnf L) (i : ℕ) : (p^i).rank = p.rank :=
by simp[has_pow.pow]

@[simp] def neg : pnf L → pnf L
| ⟨[], p, h⟩ := ⟨[], ∼p, by simp[h]⟩
| ⟨𝚷 :: Q, p, h⟩ := ∃.neg ⟨Q, p, by simp[h]⟩
| ⟨𝚺 :: Q, p, h⟩ := ∀.neg ⟨Q, p, by simp[h]⟩
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf rank⟩]}

instance : has_negation (pnf L) := ⟨neg⟩

@[simp] def imply : pnf L → pnf L → pnf L
| ⟨[], p₁, h₁⟩      ⟨[], p₂, h₂⟩      := ⟨[], p₁ ⟶ p₂, by simp[h₁, h₂]⟩
| ⟨[], p₁, h₁⟩      ⟨𝚷 :: Q₂, p₂, h₂⟩ := ∀.imply (⟨[], p₁^1, by simp[h₁]⟩) ⟨Q₂, p₂, h₂⟩
| ⟨[], p₁, h₁⟩      ⟨𝚺 :: Q₂, p₂, h₂⟩ := ∃.imply ⟨[], p₁^1, by simp[h₁]⟩ ⟨Q₂, p₂, h₂⟩
| ⟨𝚷 :: Q₁, p₁, h₁⟩ ⟨[], p₂, h₂⟩      := ∃.imply ⟨Q₁, p₁, by simp[h₁]⟩ ⟨[], p₂^1, by simp[h₂]⟩
| ⟨𝚷 :: Q₁, p₁, h₁⟩ ⟨𝚷 :: Q₂, p₂, h₂⟩ :=
    ∃.(∀.imply (pnf.mk Q₁ p₁ h₁^1) ((pnf.mk Q₂ p₂ (by simp[h₂])).rew ı-{1}) : pnf L)
| ⟨𝚷 :: Q₁, p₁, h₁⟩ ⟨𝚺 :: Q₂, p₂, h₂⟩ :=
    ∃.(∃.imply (pnf.mk Q₁ p₁ h₁^1) ((pnf.mk Q₂ p₂ (by simp[h₂])).rew ı-{1}) : pnf L)
| ⟨𝚺 :: Q₁, p₁, h₁⟩ ⟨[], p₂, h₂⟩      := ∀.imply ⟨Q₁, p₁, by simp[h₁]⟩ ⟨[], p₂^1, by simp[h₂]⟩
| ⟨𝚺 :: Q₁, p₁, h₁⟩ ⟨𝚷 :: Q₂, p₂, h₂⟩ :=
    ∀.(∀.imply (pnf.mk Q₁ p₁ h₁^1) ((pnf.mk Q₂ p₂ (by simp[h₂])).rew ı-{1}) : pnf L)
| ⟨𝚺 :: Q₁, p₁, h₁⟩ ⟨𝚺 :: Q₂, p₂, h₂⟩ :=
    ∀.(∃.imply (pnf.mk Q₁ p₁ h₁^1) ((pnf.mk Q₂ p₂ (by simp[h₂])).rew ı-{1}) : pnf L)
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.fst.rank + x.snd.rank)⟩]}

instance : has_arrow (pnf L) := ⟨imply⟩

end pnf

namespace formula

@[simp] def to_pnf : formula L → pnf L
| ⊤         := ⟨[], ⊤, by simp⟩
| (app p v) := ⟨[], app p v, by simp⟩
| ((t : term L) =' u) := ⟨[], (t : term L) =' u, by simp⟩
| (p ⟶ q) := (to_pnf p).imply (to_pnf q)
| (∼p) := (to_pnf p).neg
| (∀.(p : formula L)) := ∀.(to_pnf p)

end formula

lemma equiv_normalize_imply : ∀ (p q : pnf L) (T : Theory L),
  (p.imply q).to_formula  ≈[T] p.to_formula ⟶ q.to_formula
| ⟨[], p₁, h₁⟩      ⟨[], p₂, h₂⟩      T := by simp
| ⟨[], p₁, h₁⟩      ⟨𝚷 :: Q₂, p₂, h₂⟩ T := by { simp, have ih := equiv_normalize_imply ⟨[], p₁^1, by simp[h₁]⟩ ⟨Q₂, p₂, h₂⟩,
    calc     ∀.((pnf.mk ([]) (p₁^1) (by simp[h₁])).imply (pnf.mk Q₂ p₂ h₂)).to_formula
        ≈[(T)] ∀.((pnf.mk ([]) (p₁^1) (by simp[h₁])).to_formula ⟶ (pnf.mk Q₂ p₂ h₂).to_formula)
    : show _ ≈[T] _, from provable.equiv_univ_of_equiv (ih _)
    ... ≈[T] p₁ ⟶ ∀.(pnf.mk Q₂ p₂ h₂).to_formula
    : by { symmetry, refine by simp[classical_logic.equiv] } }
| ⟨[], p₁, h₁⟩      ⟨𝚺 :: Q₂, p₂, h₂⟩ T := by { simp, have ih := equiv_normalize_imply ⟨[], p₁^1, by simp[h₁]⟩ ⟨Q₂, p₂, h₂⟩,
    calc     ∃.((pnf.mk ([]) (p₁^1) (by simp[h₁])).imply (pnf.mk Q₂ p₂ h₂)).to_formula
        ≈[T] ∃.((pnf.mk ([]) (p₁^1) (by simp[h₁])).to_formula ⟶ (pnf.mk Q₂ p₂ h₂).to_formula)
    : show _ ≈[T] _, from provable.equiv_ex_of_equiv (ih _)
    ... ≈[T] p₁ ⟶ ∃.(pnf.mk Q₂ p₂ h₂).to_formula
    : by { symmetry, simp[classical_logic.equiv] } }
| ⟨𝚷 :: Q₁, p₁, h₁⟩ ⟨[], p₂, h₂⟩      T := by { simp, have ih := equiv_normalize_imply ⟨Q₁, p₁, h₁⟩ (pnf.mk ([]) p₂ h₂^1),
    calc     ∃.((pnf.mk Q₁ p₁ h₁).imply (pnf.mk ([]) p₂ h₂^1)).to_formula
        ≈[T] ∃.((pnf.mk Q₁ p₁ h₁).to_formula ⟶ (pnf.mk ([]) p₂ h₂^1).to_formula)
    : show _ ≈[T] _, from provable.equiv_ex_of_equiv (ih _)
    ... ≈[T] ∀.(pnf.mk Q₁ p₁ (by simp[h₁])).to_formula ⟶ p₂
    : by { symmetry, simp[classical_logic.equiv] } }
| ⟨𝚷 :: Q₁, p₁, h₁⟩ ⟨𝚷 :: Q₂, p₂, h₂⟩ T := by { simp,
    have ih := equiv_normalize_imply (pnf.mk Q₁ p₁ h₁^1) ((pnf.mk Q₂ p₂ h₂).rew ı-{1}),
    calc     ∃.∀.((pnf.mk Q₁ p₁ h₁^1).imply ((pnf.mk Q₂ p₂ h₂).rew ı-{1})).to_formula
        ≈[T] ∃.∀.((pnf.mk Q₁ p₁ h₁^1).to_formula ⟶ ((pnf.mk Q₂ p₂ h₂).rew ı-{1}).to_formula)
    : show _ ≈[T] _, from provable.equiv_ex_of_equiv (provable.equiv_univ_of_equiv (ih _))
    ... ≈[T] ∃.((pnf.mk Q₁ p₁ h₁).to_formula ⟶ (∀.(pnf.mk Q₂ p₂ h₂).to_formula)^1)
    : by { show _ ≈[T] _, symmetry, simp[classical_logic.equiv, formula.fal_pow_discard],
           refine provable.equiv_ex_of_equiv (by simp) }
    ... ≈[T] ∀.(pnf.mk Q₁ p₁ h₁).to_formula ⟶ ∀.(pnf.mk Q₂ p₂ h₂).to_formula
    : by { symmetry, simp [classical_logic.equiv] } }
| ⟨𝚷 :: Q₁, p₁, h₁⟩ ⟨𝚺 :: Q₂, p₂, h₂⟩ T := by { simp, 
    have ih := equiv_normalize_imply (pnf.mk Q₁ p₁ h₁^1) ((pnf.mk Q₂ p₂ h₂).rew ı-{1}),
    calc     ∃.∃.((pnf.mk Q₁ p₁ h₁^1).imply ((pnf.mk Q₂ p₂ h₂).rew ı-{1})).to_formula
        ≈[T] ∃.∃.((pnf.mk Q₁ p₁ h₁^1).to_formula ⟶ ((pnf.mk Q₂ p₂ h₂).rew ı-{1}).to_formula)
    : show _ ≈[T] _, from provable.equiv_ex_of_equiv (provable.equiv_ex_of_equiv (ih _))
    ... ≈[T] ∃.((pnf.mk Q₁ p₁ h₁).to_formula ⟶ (∃.(pnf.mk Q₂ p₂ h₂).to_formula)^1)
    : by { show _ ≈[T] _, symmetry, simp[classical_logic.equiv, formula.ex_pow_discard],
           refine provable.equiv_ex_of_equiv (by simp) }
    ... ≈[T] ∀.(pnf.mk Q₁ p₁ h₁).to_formula ⟶ ∃.(pnf.mk Q₂ p₂ h₂).to_formula
    : by { symmetry, simp [classical_logic.equiv] } }
| ⟨𝚺 :: Q₁, p₁, h₁⟩ ⟨[], p₂, h₂⟩      T := by { simp, have ih := equiv_normalize_imply ⟨Q₁, p₁, h₁⟩ (pnf.mk ([]) p₂ h₂^1),
    calc     ∀.((pnf.mk Q₁ p₁ h₁).imply (pnf.mk ([]) p₂ h₂^1)).to_formula
        ≈[T] ∀.((pnf.mk Q₁ p₁ h₁).to_formula ⟶ (pnf.mk ([]) p₂ h₂^1).to_formula)
    : show _ ≈[T] _, from provable.equiv_univ_of_equiv (ih _)
    ... ≈[T] ∃.(pnf.mk Q₁ p₁ (by simp[h₁])).to_formula ⟶ p₂
    : by { symmetry, simp[classical_logic.equiv] } }
| ⟨𝚺 :: Q₁, p₁, h₁⟩ ⟨𝚷 :: Q₂, p₂, h₂⟩ T := by { simp,
    have ih := equiv_normalize_imply (pnf.mk Q₁ p₁ h₁^1) ((pnf.mk Q₂ p₂ h₂).rew ı-{1}),
    calc     ∀.∀.((pnf.mk Q₁ p₁ h₁^1).imply ((pnf.mk Q₂ p₂ h₂).rew ı-{1})).to_formula
        ≈[T] ∀.∀.((pnf.mk Q₁ p₁ h₁^1).to_formula ⟶ ((pnf.mk Q₂ p₂ h₂).rew ı-{1}).to_formula)
    : show _ ≈[T] _, from provable.equiv_univ_of_equiv (provable.equiv_univ_of_equiv (ih _))
    ... ≈[T] ∀.((pnf.mk Q₁ p₁ h₁).to_formula ⟶ (∀.(pnf.mk Q₂ p₂ h₂).to_formula)^1)
    : by { show _ ≈[T] _, symmetry, simp[classical_logic.equiv, formula.fal_pow_discard],
           refine provable.equiv_univ_of_equiv (by simp) }
    ... ≈[T] ∃.(pnf.mk Q₁ p₁ h₁).to_formula ⟶ ∀.(pnf.mk Q₂ p₂ h₂).to_formula
    : by { symmetry, simp [classical_logic.equiv] } }
| ⟨𝚺 :: Q₁, p₁, h₁⟩ ⟨𝚺 :: Q₂, p₂, h₂⟩ T := by { simp, 
    have ih := equiv_normalize_imply (pnf.mk Q₁ p₁ h₁^1) ((pnf.mk Q₂ p₂ h₂).rew ı-{1}),
    calc     ∀.∃.((pnf.mk Q₁ p₁ h₁^1).imply ((pnf.mk Q₂ p₂ h₂).rew ı-{1})).to_formula
        ≈[T] ∀.∃.((pnf.mk Q₁ p₁ h₁^1).to_formula ⟶ ((pnf.mk Q₂ p₂ h₂).rew ı-{1}).to_formula)
    : show _ ≈[T] _, from provable.equiv_univ_of_equiv (provable.equiv_ex_of_equiv (ih _))
    ... ≈[T] ∀.((pnf.mk Q₁ p₁ h₁).to_formula ⟶ (∃.(pnf.mk Q₂ p₂ h₂).to_formula)^1)
    : by { show _ ≈[T] _, symmetry, simp[classical_logic.equiv, formula.ex_pow_discard],
           refine provable.equiv_univ_of_equiv (by simp) }
    ... ≈[T] ∃.(pnf.mk Q₁ p₁ h₁).to_formula ⟶ ∃.(pnf.mk Q₂ p₂ h₂).to_formula
    : by { symmetry, simp [classical_logic.equiv] } }
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.1.rank + x.2.1.rank)⟩]}

lemma equiv_normalize_neg : ∀ (p : pnf L) (T : Theory L) , T ⊢ p.neg.to_formula ⟷ ∼p.to_formula
| ⟨[], p, h⟩     T := by simp
| ⟨𝚷 :: Q, p, h⟩ T := by simp;
    calc ∃.(pnf.mk Q p (by simp[h])).neg.to_formula ≈[T] ∃.∼(pnf.mk Q p (by simp[h])).to_formula
    : show _ ≈[T] _, from provable.equiv_ex_of_equiv (equiv_normalize_neg ⟨Q, p, by simp[h]⟩ _)
                                                 ... ≈[T] ∼∀.(pnf.mk Q p (by simp[h])).to_formula
    : classical_logic.equiv_neg_of_equiv (provable.equiv_univ_of_equiv (by simp))
| ⟨𝚺 :: Q, p, h⟩ T := by { simp,
    calc     ∀.(pnf.mk Q p (by simp[h])).neg.to_formula ≈[T] ∀.∼(pnf.mk Q p (by simp[h])).to_formula
    : show _ ≈[T] _, from provable.equiv_univ_of_equiv (equiv_normalize_neg ⟨Q, p, by simp[h]⟩ _)
                                                    ... ≈[T] ∼∃.(pnf.mk Q p (by simp[h])).to_formula
    : by { simp[has_exists_quantifier.ex, formula.ex, classical_logic.equiv] } }

@[reducible] def formula.normalize (p : formula L) : formula L := p.to_pnf.to_formula

@[reducible] def formula.open (p : formula L) : formula L := p.to_pnf.2

@[simp] lemma formula.open_is_open (p : formula L) : p.open.is_open := p.to_pnf.is_openform

open axiomatic_classical_logic'

lemma equiv_normalize : ∀ (p : formula L) {T : Theory L},  T ⊢ p ⟷ p.normalize
| ⊤                 T := by simp[formula.normalize]
| (formula.app p v) T := by simp[formula.normalize]
| (t =' u)          T := by simp[formula.normalize]
| (p ⟶ q)          T :=
    by { simp[formula.normalize], 
         have : T ⊢ p ⟶ q ⟷ (p.to_pnf.to_formula ⟶ q.to_pnf.to_formula) :=  (equiv_imply_of_equiv (equiv_normalize p) (equiv_normalize q)),
         refine equiv_trans this (classical_logic.equiv_symm (equiv_normalize_imply p.to_pnf q.to_pnf T)) }
| (∼p)              T := by { simp[formula.normalize],
    have : T ⊢ ∼p ⟷ ∼p.to_pnf.to_formula, from equiv_neg_of_equiv (equiv_normalize p),
    exact equiv_trans this (equiv_symm (equiv_normalize_neg p.to_pnf T)) }
| (∀.p)           T := by { simp[formula.normalize], refine provable.equiv_univ_of_equiv (equiv_normalize p) }

def formula.rank (p : formula L) : ℕ := p.to_pnf.rank

end fol