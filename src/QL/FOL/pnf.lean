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



namespace pnf

instance : has_univ_quantifier' (pnf L m) := ⟨@pnf.fal L m⟩

instance : has_exists_quantifier' (pnf L m) := ⟨@pnf.ex L m⟩

def to_str [∀ n, has_to_string (L.fn n)] [∀ n, has_to_string (L.pr n)] : Π {n}, pnf L m n → string
| n (openformula p _) := "[" ++ to_string p ++ "]"
| n (fal φ)           := "∀" ++ to_str φ
| n (ex φ)            := "∃" ++ to_str φ

instance [∀ n, has_to_string (L.fn n)] [∀ n, has_to_string (L.pr n)] : has_to_string (pnf L m n) := ⟨@to_str L m _ _ n⟩

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

instance : has_coe (pnf L m n) (subformula L m n) := ⟨@to_formula L m n⟩

@[simp] lemma to_formula_forall (φ : pnf L m (n + 1)) : to_formula (∀'φ) = ∀'(to_formula φ) := by simp[has_univ_quantifier'.univ]

@[simp] lemma to_formula_exists (φ : pnf L m (n + 1)) : to_formula (∃'φ) = ∃'(to_formula φ) := by simp[has_exists_quantifier'.ex]

section mlift

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

@[simp] lemma rank_mlift : ∀ {n} (φ : pnf L m n), rank (mlift φ) = rank φ
| n (openformula p hp) := by simp
| n (fal p) := by show (∀'p).mlift.rank = p.fal.rank; simpa using rank_mlift p
| n (ex p)  := by show (∃'p).mlift.rank = p.ex.rank; simpa  using rank_mlift p

end mlift

section push

@[simp] def push : Π {n}, pnf L m (n + 1) → pnf L (m + 1) n
| n (openformula p hp) := openformula p.push (by simpa using hp)
| n (fal φ)            := fal (push φ)
| n (ex  φ)            := ex (push φ)
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.rank)⟩]}

@[simp] lemma push_forall (φ : pnf L m (n + 1 + 1)) : push (∀'φ) = ∀'(push φ) := by simp[has_univ_quantifier'.univ]

@[simp] lemma push_exists (φ : pnf L m (n + 1 + 1)) : push (∃'φ) = ∃'(push φ) := by simp[has_exists_quantifier'.ex]

@[simp] lemma push_to_formula : ∀ {n} (φ : pnf L m (n + 1)), φ.push.to_formula = 𝗠 φ.to_formula
| _ (openformula p hp) := by simp
| _ (fal φ)            := by simp; exact push_to_formula φ
| _ (ex φ)             := by simp; exact push_to_formula φ
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.rank)⟩]}

@[simp] lemma rank_push : ∀ {n} (φ : pnf L m (n + 1)), rank (push φ) = rank φ
| n (openformula p hp) := by simp
| n (fal p) := by show (∀'p).push.rank = p.fal.rank; simpa using rank_push p
| n (ex p) := by show (∃'p).push.rank = p.ex.rank; simpa using rank_push p
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.rank)⟩]}

end push

section pull

@[simp] def pull : Π {n}, pnf L (m + 1) n → pnf L m (n + 1)
| n (openformula p hp) := openformula p.pull (by simpa using hp)
| n (fal φ)            := fal (pull φ)
| n (ex  φ)            := ex (pull φ)

@[simp] lemma pull_forall (φ : pnf L (m + 1) (n + 1)) : pull (∀'φ) = ∀'(pull φ) := by simp[has_univ_quantifier'.univ]

@[simp] lemma pull_exists (φ : pnf L (m + 1) (n + 1)) : pull (∃'φ) = ∃'(pull φ) := by simp[has_exists_quantifier'.ex]

@[simp] lemma pull_to_formula : ∀ {n} (φ : pnf L (m + 1) n), φ.pull.to_formula = 𝗡 φ.to_formula
| _ (openformula p hp) := by simp
| _ (fal φ)            := by simp; exact pull_to_formula φ
| _ (ex φ)             := by simp; exact pull_to_formula φ

@[simp] lemma pull_push : ∀ {n} (φ : pnf L (m + 1) n), φ.pull.push = φ
| _ (openformula p hp) := by simp
| _ (fal φ)            := by simpa using pull_push φ
| _ (ex φ)             := by simpa using pull_push φ

end pull

section dummy

def dummy : pnf L m n → pnf L m (n + 1) := pull ∘ mlift

@[simp] lemma push_dummy (φ : pnf L m n) : push (dummy φ) = mlift φ :=
by simp[dummy]

lemma dummy_openformula (p : subformula L m n) (hp) :
  dummy (openformula p hp) = openformula p.dummy (by simpa using hp) := by simp[dummy]; refl

@[simp] lemma dummy_forall (φ : pnf L m (n + 1)) : dummy (∀'φ) = ∀'(dummy φ) := by simp[dummy]

@[simp] lemma dummy_exists (φ : pnf L m (n + 1)) : dummy (∃'φ) = ∃'(dummy φ) := by simp[dummy]

@[simp] lemma dummy_to_formula (φ : pnf L m n) : φ.dummy.to_formula = 𝗗 φ.to_formula :=
by simp[mlift_to_formula, pull_to_formula, dummy, subformula.dummy]

@[simp] lemma rank_dummy : ∀ {n} (φ : pnf L m n), rank (dummy φ) = rank φ
| n (openformula p hp) := by simp[dummy_openformula]
| n (fal p) := by show (∀'p).dummy.rank = p.fal.rank; simpa using rank_dummy p
| n (ex p) := by show (∃'p).dummy.rank = p.ex.rank; simpa using rank_dummy p

end dummy

@[simp] def neg : Π {m n}, pnf L m n → pnf L m n
| m n (openformula p hp) := openformula (∼p) (by simpa[is_open] using hp)
| m n (fal φ)            := ∃'(pull $ neg $ push φ)
| m n (ex φ)             := ∀'(pull $ neg $ push φ)
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.2.rank)⟩]}

@[simp] def imply : Π {m n}, pnf L m n → pnf L m n → pnf L m n
| m n (openformula p hp) (openformula q hq) := openformula (p ⟶ q) (by simp; exact ⟨hp, hq⟩)
| m n (openformula p hp) (fal ψ)            := ∀'pull (imply (mlift $ openformula p hp) (push ψ))
| m n (openformula p hp) (ex ψ)             := ∃'pull (imply (mlift $ openformula p hp) (push ψ))
| m n (fal φ)            ψ                  := ∃'pull (imply (push φ) (mlift ψ))
| m n (ex φ)             ψ                  := ∀'pull (imply (push φ) (mlift ψ))
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.2.1.rank + x.2.2.2.rank)⟩]}

open axiomatic_classical_logic' axiomatic_classical_logic provable

lemma equiv_to_formula_neg : ∀ {m} (T : preTheory L m) (p : pnf L m 0), T ⊢ (p.neg).to_formula ⟷ ∼p.to_formula
| m T (openformula p hp) := by simp
| m T (pnf.fal φ) :=
    begin
      simp, show T ⊢ ∃'𝗡 φ.push.neg.to_formula ⟷ ∼∀'φ.to_formula,
      have : 𝗟'T ⊢ φ.push.neg.to_formula ⟷ ∼𝗠 φ.to_formula, by simpa using equiv_to_formula_neg 𝗟'T φ.push,
      have : T ⊢ ∃'𝗡 φ.push.neg.to_formula ⟷ ∃'∼φ.to_formula, by simpa using equiv_exists_of_equiv' this,
      refine equiv_trans this (equiv_symm $ neg_forall_pnf _)
    end
| m T (pnf.ex φ) :=
    begin
      simp, show T ⊢ ∀'𝗡 φ.push.neg.to_formula ⟷ ∼∃'φ.to_formula,
      have : 𝗟'T ⊢ φ.push.neg.to_formula ⟷ ∼𝗠 φ.to_formula, by simpa using equiv_to_formula_neg 𝗟'T φ.push,
      have : T ⊢ ∀'𝗡 φ.push.neg.to_formula ⟷ ∀'∼φ.to_formula, by simpa using equiv_forall_of_equiv' this,
      refine equiv_trans this (equiv_symm $ neg_exists_pnf _)
    end
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.2.rank)⟩]}

lemma equiv_to_formula_imply : ∀ {m} (T : preTheory L m) (p q : pnf L m 0),
  T ⊢ (p.imply q).to_formula ⟷ (p.to_formula ⟶ q.to_formula)
| m T (openformula p hp) (openformula q hq) := by simp
| m T (openformula p hp) (fal ψ)            :=
    let φ := openformula p hp in
    begin
      simp, show T ⊢ (∀'𝗡 (φ.mlift.imply ψ.push).to_formula) ⟷ (p ⟶ ∀'ψ.to_formula),
      have : 𝗟'T ⊢ (φ.mlift.imply ψ.push).to_formula ⟷ (𝗟 p ⟶ 𝗠 ψ.to_formula),
      by simpa using equiv_to_formula_imply 𝗟'T φ.dummy.push ψ.push,
      have : T ⊢ ∀'𝗡 (φ.mlift.imply ψ.push).to_formula ⟷ ∀'(𝗗 p ⟶ ψ.to_formula),
      by simpa using equiv_forall_of_equiv' this,
      refine equiv_trans this (equiv_symm $ imply_forall_pnf _ _)
    end
| m T (openformula p hp) (ex ψ)             :=
    let φ := openformula p hp in
    begin
      simp, show T ⊢ (∃'𝗡 (φ.mlift.imply ψ.push).to_formula) ⟷ (p ⟶ ∃'ψ.to_formula),
      have : 𝗟'T ⊢ (φ.mlift.imply ψ.push).to_formula ⟷ (𝗟 p ⟶ 𝗠 ψ.to_formula),
      by simpa using equiv_to_formula_imply 𝗟'T φ.dummy.push ψ.push,
      have : T ⊢ ∃'𝗡 (φ.mlift.imply ψ.push).to_formula ⟷ ∃'(𝗗 p ⟶ ψ.to_formula),
      by simpa using equiv_exists_of_equiv' this,
      refine equiv_trans this (equiv_symm $ imply_exists_pnf _ _)
    end
| m T (fal φ)            ψ                  :=
    begin
      simp, show T ⊢ (∃'𝗡 (φ.push.imply ψ.mlift).to_formula) ⟷ (∀'φ.to_formula ⟶ ψ.to_formula),
      have : 𝗟'T ⊢ (φ.push.imply ψ.mlift).to_formula ⟷ (𝗠 φ.to_formula ⟶ 𝗟 ψ.to_formula),
      by simpa using equiv_to_formula_imply 𝗟'T φ.push ψ.mlift,
      have : T ⊢ ∃'𝗡 (φ.push.imply ψ.mlift).to_formula ⟷ ∃'(φ.to_formula ⟶ 𝗗 ψ.to_formula),
      by simpa using equiv_exists_of_equiv' this,
      refine equiv_trans this (equiv_symm $ forall_imply_pnf _ _)
    end
| m T (ex φ)             ψ                  :=
    begin
      simp, show T ⊢ (∀'𝗡 (φ.push.imply ψ.mlift).to_formula) ⟷ (∃'φ.to_formula ⟶ ψ.to_formula),
      have : 𝗟'T ⊢ (φ.push.imply ψ.mlift).to_formula ⟷ (𝗠 φ.to_formula ⟶ 𝗟 ψ.to_formula),
      by simpa using equiv_to_formula_imply 𝗟'T φ.push ψ.mlift,
      have : T ⊢ ∀'𝗡 (φ.push.imply ψ.mlift).to_formula ⟷ ∀'(φ.to_formula ⟶ 𝗗 ψ.to_formula),
      by simpa using equiv_forall_of_equiv' this,
      refine equiv_trans this (equiv_symm $ exists_imply_pnf _ _)
    end
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.2.1.rank + x.2.2.2.rank)⟩]}

instance : has_logic_symbol (pnf L m n) :=
logic_simbol_default (pnf L m n) (openformula ⊤ (by simp)) neg imply

end pnf

namespace subformula
open pnf axiomatic_classical_logic' axiomatic_classical_logic provable
variables {L m n} (T : preTheory L m)

@[simp] def to_pnf : Π {m n}, subformula L m n → pnf L m n
| m n verum          := openformula ⊤ (by simp)
| m n (relation r v) := openformula (relation r v) (by simp)
| m n (equal t u)    := openformula (t =' u) (by simp)
| m n (imply p q)    := (to_pnf p).imply (to_pnf q)
| m n (neg p)        := (to_pnf p).neg
| m n (fal p)        := ∀'pnf.pull (to_pnf (𝗠 p))
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.2.complexity)⟩]}

def normalize (p : subformula L m n) : subformula L m n := p.to_pnf.to_formula

@[simp] lemma to_pnf_top : to_pnf (⊤ : subformula L m n) = openformula ⊤ (by simp) := by unfold has_top.top; simp; refl

@[simp] lemma to_pnf_equal (t u) : to_pnf (t =' u : subformula L m n) = openformula (t =' u) (by simp) :=
by unfold has_eq.eq; simp; refl

@[simp] lemma to_pnf_imply (p q : subformula L m n) : to_pnf (p ⟶ q) = (to_pnf p).imply (to_pnf q) :=
by unfold has_arrow.arrow; simp; refl

@[simp] lemma to_pnf_neg (p : subformula L m n) : to_pnf (∼p) = (to_pnf p).neg :=
by unfold has_negation.neg; simp; refl

@[simp] lemma to_pnf_fal (p : subformula L m (n + 1)) : to_pnf (∀'p) = ∀' pnf.pull (to_pnf $ 𝗠 p) :=
by unfold has_univ_quantifier'.univ; simp; refl

end subformula

section 
open pnf subformula axiomatic_classical_logic' axiomatic_classical_logic provable

lemma equiv_normalize : ∀ {m} (T : preTheory L m) (p), T ⊢ normalize p ⟷ p
| m T verum          := by simp[top_eq, normalize]
| m T (relation r v) := by simp[normalize]
| m T (equal t u)    := by simp[equal_eq, normalize]
| m T (imply p q)    := by {
    simp[imply_eq, normalize],
    have : T ⊢ (p.to_pnf.imply q.to_pnf).to_formula ⟷ (p.normalize ⟶ q.normalize),
    from equiv_to_formula_imply T p.to_pnf q.to_pnf,
    exact equiv_trans this (equiv_imply_of_equiv (equiv_normalize T p) (equiv_normalize T q)) }
| m T (neg p)        := by { 
    simp[neg_eq, normalize],
    have : T ⊢ p.to_pnf.neg.to_formula ⟷ ∼p.normalize, from equiv_to_formula_neg T p.to_pnf,
    exact equiv_trans this (equiv_neg_of_equiv (equiv_normalize T p)) }
| m T (fal p)        := by { 
    simp[fal_eq, normalize],
    have : 𝗟'T ⊢ (𝗠 p).normalize ⟷ 𝗠 p, by simpa using equiv_normalize 𝗟'T p.push,
    exact equiv_forall_of_equiv (by simpa using this) }
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.2.complexity)⟩]}

end 

private def s : subformula language.empty 1 0 := (&0 =' &0) ⟶ ∀'((#0 =' &0) ⊓ ∃'(#1 =' #2) ⊔ ∀' ∃' ((#0 =' #1) ⟷ (#0 =' &0)))

#eval to_string s
#eval to_string s.to_pnf
#eval to_string s.normalize

end fol