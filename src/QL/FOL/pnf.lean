import QL.FOL.deduction

-- Prenex normal form

universes u v

namespace fol
open_locale logic_symbol aclogic
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

@[simp] def rank : Π {n}, pnf L m n → ℕ
| n (openformula p hp) := 0
| n (fal φ)            := φ.rank + 1
| n (ex  φ)            := φ.rank + 1

@[simp] lemma rank_forall (φ : pnf L m (n + 1)) : rank (∀'φ) = rank φ + 1 := by simp[has_univ_quantifier'.univ]

@[simp] lemma rank_exists (φ : pnf L m (n + 1)) : rank (∃'φ) = rank φ + 1 := by simp[has_exists_quantifier'.ex]

@[simp] lemma forall_inj (p q : pnf L m (n + 1)) : ∀'p = ∀'q ↔ p = q := ⟨fal.inj, congr_arg _⟩

@[simp] lemma exists_inj (p q : pnf L m (n + 1)) : ∃'p = ∃'q ↔ p = q := ⟨ex.inj, congr_arg _⟩

@[simp] def to_formula : Π {n}, pnf L m n → subformula L m n
| n (openformula p hp) := p
| n (fal φ)            := ∀'to_formula φ
| n (ex  φ)            := ∃'to_formula φ

@[simp] lemma to_formula_forall (φ : pnf L m (n + 1)) : to_formula (∀'φ) = ∀'(to_formula φ) := by simp[has_univ_quantifier'.univ]

@[simp] lemma to_formula_exists (φ : pnf L m (n + 1)) : to_formula (∃'φ) = ∃'(to_formula φ) := by simp[has_exists_quantifier'.ex]

@[simp] def mlift : Π {n}, pnf L m n → pnf L (m + 1) n
| n (openformula p hp) := openformula p.mlift (by simpa using hp)
| n (fal φ)            := fal (mlift φ)
| n (ex  φ)            := ex (mlift φ)

@[simp] lemma mlift_forall (φ : pnf L m (n + 1)) : mlift (∀'φ) = ∀'(mlift φ) := by simp[has_univ_quantifier'.univ]

@[simp] lemma mlift_exists (φ : pnf L m (n + 1)) : mlift (∃'φ) = ∃'(mlift φ) := by simp[has_exists_quantifier'.ex]

@[simp] lemma mlift_to_formula : ∀ {n} (φ : pnf L m n), φ.mlift.to_formula = 𝗟 φ.to_formula
| _ (openformula p hp) := by simp
| _ (fal φ)            := by simp; exact mlift_to_formula φ
| _ (ex φ)             := by simp; exact mlift_to_formula φ

@[simp] def push : Π {n}, pnf L m (n + 1) → pnf L (m + 1) n
| n (openformula p hp) := openformula p.push (by simpa using hp)
| n (fal φ)            := fal (push φ)
| n (ex  φ)            := ex (push φ)
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.rank)⟩]}

@[simp] lemma push_forall (φ : pnf L m (n + 1 + 1)) : push (∀'φ) = ∀'(push φ) := by simp[has_univ_quantifier'.univ]

@[simp] lemma push_exists (φ : pnf L m (n + 1 + 1)) : push (∃'φ) = ∃'(push φ) := by simp[has_exists_quantifier'.ex]

lemma push_to_formula : ∀ {n} (φ : pnf L m (n + 1)), φ.push.to_formula = 𝗠 φ.to_formula
| _ (openformula p hp) := by simp
| _ (fal φ)            := by simp; exact push_to_formula φ
| _ (ex φ)             := by simp; exact push_to_formula φ
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.rank)⟩]}

@[simp] lemma rank_push : ∀ {n} (φ : pnf L m (n + 1)), rank (push φ) = rank φ
| n (openformula p hp) := by simp
| n (fal p) := by show (∀'p).push.rank = p.fal.rank; simpa using rank_push p
| n (ex p) := by show (∃'p).push.rank = p.ex.rank; simpa using rank_push p
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.rank)⟩]}

@[simp] def pull : Π {n}, pnf L (m + 1) n → pnf L m (n + 1)
| n (openformula p hp) := openformula p.pull (by simpa using hp)
| n (fal φ)            := fal (pull φ)
| n (ex  φ)            := ex (pull φ)

@[simp] lemma pull_forall (φ : pnf L (m + 1) (n + 1)) : pull (∀'φ) = ∀'(pull φ) := by simp[has_univ_quantifier'.univ]

@[simp] lemma pull_exists (φ : pnf L (m + 1) (n + 1)) : pull (∃'φ) = ∃'(pull φ) := by simp[has_exists_quantifier'.ex]

lemma pull_to_formula : ∀ {n} (φ : pnf L (m + 1) n), φ.pull.to_formula = 𝗡 φ.to_formula
| _ (openformula p hp) := by simp
| _ (fal φ)            := by simp; exact pull_to_formula φ
| _ (ex φ)             := by simp; exact pull_to_formula φ

def dummy : pnf L m n → pnf L m (n + 1) := pull ∘ mlift

lemma dummy_openformula (p : subformula L m n) (hp) :
  dummy (openformula p hp) = openformula p.dummy (by simpa using hp) := by simp[dummy]; refl

@[simp] lemma dummy_forall (φ : pnf L m (n + 1)) : dummy (∀'φ) = ∀'(dummy φ) := by simp[dummy]

@[simp] lemma dummy_exists (φ : pnf L m (n + 1)) : dummy (∃'φ) = ∃'(dummy φ) := by simp[dummy]

lemma dummy_to_formula (φ : pnf L (m + 1) n) : φ.dummy.to_formula = 𝗗 φ.to_formula :=
by simp[mlift_to_formula, pull_to_formula, dummy, subformula.dummy]

@[simp] lemma rank_dummy : ∀ {n} (φ : pnf L m n), rank (dummy φ) = rank φ
| n (openformula p hp) := by simp[dummy_openformula]
| n (fal p) := by show (∀'p).dummy.rank = p.fal.rank; simpa using rank_dummy p
| n (ex p) := by show (∃'p).dummy.rank = p.ex.rank; simpa using rank_dummy p


instance : has_coe (pnf L m n) (subformula L m n) := ⟨@to_formula L m n⟩

@[simp] def neg : Π {n}, pnf L m n → pnf L m n
| n (openformula p hp) := openformula (∼p) (by simpa[is_open] using hp)
| n (fal φ)            := ∃'φ.neg
| n (ex φ)             := ∀'φ.neg

lemma push_neg : ∀ {n} (p : pnf L m (n + 1)), p.neg.push = p.push.neg
| _ (openformula p hp) := by simp
| _ (fal φ)            := by simp[push_neg φ]
| _ (ex φ)             := by simp[push_neg φ]
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.rank)⟩]}

@[simp] def imply : Π {n}, pnf L m n → pnf L m n → pnf L m n
| n (openformula p hp) (openformula q hq) := openformula (p ⟶ q) (by simp; exact ⟨hp, hq⟩)
| n (openformula p hp) (fal ψ)            := ∀'(imply (dummy $ openformula p hp) ψ)
| n (openformula p hp) (ex ψ)             := ∃'(imply (dummy $ openformula p hp) ψ)
| n (fal φ)            ψ                  := ∃'(imply φ (dummy ψ))
| n (ex φ)             ψ                  := ∀'(imply φ (dummy ψ))
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.1.rank + x.2.2.rank)⟩]}

lemma push_imply : ∀ {n} (p q : pnf L m (n + 1)), (p.imply q).push = p.push.imply q.push
| n (openformula p hp) (openformula q hq) := by simp
| n (openformula p hp) (fal ψ)            := by { simp[dummy_openformula], have := push_imply (dummy $ openformula p hp) ψ, }
| n (openformula p hp) (ex ψ)             := by {  }
| n (fal φ)            ψ                  := by {  }
| n (ex φ)             ψ                  := by {  }
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.1.rank + x.2.2.rank)⟩]}


end pnf

namespace formula
open pnf axiomatic_classical_logic' axiomatic_classical_logic provable
variables {L m n} (T : preTheory L m)

@[simp] def to_pnf : Π {n}, subformula L m n → pnf L m n
| _ verum          := openformula ⊤ (by simp)
| _ (relation r v) := openformula (relation r v) (by simp)
| _ (equal t u)    := openformula (t =' u) (by simp)
| _ (imply p q)    := (to_pnf p).imply (to_pnf q)
| _ (neg p)        := (to_pnf p).neg
| _ (fal p)        := ∀'(to_pnf p)

lemma equiv_normalize_neg : ∀ {m} (T : preTheory L m) (p : pnf L m 0), T ⊢ (p.neg).to_formula ⟷ ∼p.to_formula
| m T (openformula p hp) := by simp
| m T (pnf.fal φ) := by {
  have : 𝗟'T ⊢ 𝗠 φ.neg.to_formula ⟷ ∼𝗠 φ.to_formula, by simpa[push_to_formula, ←push_neg] using equiv_normalize_neg 𝗟'T φ.push,
  have : 𝗟'T ⊢ ∼𝗠 φ.neg.to_formula ⟷ ∼∼𝗠 φ.to_formula, from equiv_neg_of_equiv this,
  refine equiv_neg_of_equiv (equiv_forall_of_equiv $ equiv_of_equiv this (by simp[neg_eq]) (by simp)) }
| m T (pnf.ex φ) := by {
  have : 𝗟'T ⊢ 𝗠 φ.neg.to_formula ⟷ ∼𝗠 φ.to_formula, by simpa[push_to_formula, ←push_neg] using equiv_normalize_neg 𝗟'T φ.push,
  have : T ⊢ ∀'φ.neg.to_formula ⟷ ∀'∼φ.to_formula, from equiv_forall_of_equiv (by simpa using this),
  exact equiv_of_equiv this (equiv_refl _) (by simp[ex_def]) }
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.2.rank)⟩]}

lemma equiv_normalize_imply : ∀ {m} (T : preTheory L m) (p q : pnf L m 0),
  T ⊢ (p.imply q).to_formula ⟷ (p.to_formula ⟶ q.to_formula)
| m T (openformula p hp) (openformula q hq) := by simp
| m T (openformula p hp) (fal ψ)            :=
    let φ := openformula p.dummy (by simpa using hp) in
    by { simp,
      show T ⊢ ∀'(φ.imply ψ).to_formula ⟷ p ⟶ ∀' ψ.to_formula,
      have : 𝗟'T ⊢ 𝗠 (φ.imply ψ).to_formula ⟷ φ.push.to_formula ⟶ ψ.push.to_formula,
      { simp[←push_to_formula],
        have := equiv_normalize_imply 𝗟'T φ.push ψ.push, sorry
            },
      have : T ⊢ ∀'((φ.imply ψ).to_formula) ⟷ ∀'(φ.to_formula ⟶ ψ.to_formula),
      refine equiv_forall_of_equiv (by { simp,  }),


       }
| m T (openformula p hp) (ex ψ)             := by sorry
| m T (fal φ)            ψ                  := by sorry
| m T (ex φ)             ψ                  := by sorry
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.1.rank + x.2.2.rank)⟩]}
#check 0
/--/



#check 0
/-





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