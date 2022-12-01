import QL.FOL.deduction

-- Prenex normal form

universes u v

namespace fol
open_locale logic_symbol aclogic
open subformula

variables (L : language.{u}) (n : ℕ)

inductive pnf : ℕ → Type u
| openformula {n} : Π p : subformula L n, p.is_open → pnf n
| fal         {n} : pnf (n + 1) → pnf n
| ex          {n} : pnf (n + 1) → pnf n

variables {L n}

namespace pnf

instance : inhabited (pnf L n) := ⟨openformula ⊤ (by simp)⟩

instance : has_univ_quantifier' (pnf L) := ⟨@pnf.fal L⟩

lemma fal_eq (φ : pnf L (n + 1)) : φ.fal = ∀'φ := rfl

instance : has_exists_quantifier' (pnf L) := ⟨@pnf.ex L⟩

lemma ex_eq (φ : pnf L (n + 1)) : φ.ex = ∃'φ := rfl

def to_str [∀ n, has_to_string (L.fn n)] [∀ n, has_to_string (L.pr n)] : Π {n}, pnf L n → string
| n (openformula p _) := "[" ++ to_string p ++ "]"
| n (fal φ)           := "∀" ++ to_str φ
| n (ex φ)            := "∃" ++ to_str φ

instance [∀ n, has_to_string (L.fn n)] [∀ n, has_to_string (L.pr n)] : has_to_string (pnf L n) := ⟨@to_str L _ _ n⟩

@[simp] def rank : Π {n}, pnf L n → ℕ
| n (openformula p hp) := 0
| n (fal φ)            := φ.rank + 1
| n (ex  φ)            := φ.rank + 1

@[simp] lemma rank_forall (φ : pnf L (n + 1)) : rank (∀'φ) = rank φ + 1 := by simp[has_univ_quantifier'.univ]

@[simp] lemma rank_exists (φ : pnf L (n + 1)) : rank (∃'φ) = rank φ + 1 := by simp[has_exists_quantifier'.ex]

@[simp] lemma forall_inj (p q : pnf L (n + 1)) : ∀'p = ∀'q ↔ p = q := ⟨fal.inj, congr_arg _⟩

@[simp] lemma exists_inj (p q : pnf L (n + 1)) : ∃'p = ∃'q ↔ p = q := ⟨ex.inj, congr_arg _⟩

@[simp] def to_formula : Π {n}, pnf L n → subformula L n
| n (openformula p hp) := p
| n (fal φ)            := ∀'to_formula φ
| n (ex  φ)            := ∃'to_formula φ

--instance : has_coe (pnf L n) (subformula L n) := ⟨@to_formula L m n⟩

@[simp] lemma to_formula_forall (φ : pnf L (n + 1)) : to_formula (∀'φ) = ∀'(to_formula φ) := by simp[has_univ_quantifier'.univ]

@[simp] lemma to_formula_exists (φ : pnf L (n + 1)) : to_formula (∃'φ) = ∃'(to_formula φ) := by simp[has_exists_quantifier'.ex]

@[simp] lemma to_formula_univ_closure (φ : pnf L n) : to_formula (∀'*φ) = ∀'*(to_formula φ) :=
by induction n; simp*

section rew
variables (s : ℕ → subterm L n)

@[simp] def rew : Π {n} (s : ℕ → subterm L n), pnf L n → pnf L n
| n s (openformula p hp) := openformula (subformula.rew s p) (by simpa using hp)
| n s (fal φ)            := ∀'φ.rew (subterm.lift ∘ s)
| n s (ex  φ)            := ∃'φ.rew (subterm.lift ∘ s)

@[simp] lemma rew_forall (φ : pnf L (n + 1)) : rew s (∀'φ) = ∀'(rew (subterm.lift ∘ s) φ) := by simp[has_univ_quantifier'.univ]

@[simp] lemma rew_exists (φ : pnf L (n + 1)) : rew s (∃'φ) = ∃'(rew (subterm.lift ∘ s) φ) := by simp[has_exists_quantifier'.ex]

@[simp] def rew_to_formula : Π {n} (s : ℕ → subterm L n) (φ : pnf L n),
  (rew s φ).to_formula = subformula.rew s φ.to_formula
| n s (openformula p hp) := by simp
| n s (fal φ)            := by simp[rew_to_formula _ φ]
| n s (ex  φ)            := by simp[rew_to_formula _ φ]

@[simp] def rank_rew : Π {n} (s : ℕ → subterm L n) (φ : pnf L n), (rew s φ).rank = φ.rank
| n s (openformula p hp) := by simp
| n s (fal φ)            := by simp[rank_rew _ φ]
| n s (ex  φ)            := by simp[rank_rew _ φ]

end rew

section mlift

@[simp] def mlift : Π {n}, pnf L n → pnf L n
| n (openformula p hp) := openformula p.mlift (by simpa using hp)
| n (fal φ)            := fal (mlift φ)
| n (ex  φ)            := ex (mlift φ)

@[simp] lemma mlift_forall (φ : pnf L (n + 1)) : mlift (∀'φ) = ∀'(mlift φ) := by simp[has_univ_quantifier'.univ]

@[simp] lemma mlift_exists (φ : pnf L (n + 1)) : mlift (∃'φ) = ∃'(mlift φ) := by simp[has_exists_quantifier'.ex]

@[simp] lemma mlift_to_formula : ∀ {n} (φ : pnf L n), φ.mlift.to_formula = 𝗟 φ.to_formula
| _ (openformula p hp) := by simp
| _ (fal φ)            := by simp; exact mlift_to_formula φ
| _ (ex φ)             := by simp; exact mlift_to_formula φ

@[simp] lemma rank_mlift : ∀ {n} (φ : pnf L n), rank (mlift φ) = rank φ
| n (openformula p hp) := by simp
| n (fal p) := by show (∀'p).mlift.rank = p.fal.rank; simpa using rank_mlift p
| n (ex p)  := by show (∃'p).mlift.rank = p.ex.rank; simpa  using rank_mlift p

end mlift

section push

@[simp] def push : Π {n}, pnf L (n + 1) → pnf L n
| n (openformula p hp) := openformula p.push (by simpa using hp)
| n (fal φ)            := fal (push φ)
| n (ex  φ)            := ex (push φ)
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.rank)⟩]}

@[simp] lemma push_forall (φ : pnf L (n + 1 + 1)) : push (∀'φ) = ∀'(push φ) := by simp[has_univ_quantifier'.univ]

@[simp] lemma push_exists (φ : pnf L (n + 1 + 1)) : push (∃'φ) = ∃'(push φ) := by simp[has_exists_quantifier'.ex]

@[simp] lemma push_to_formula : ∀ {n} (φ : pnf L (n + 1)), φ.push.to_formula = 𝗠 φ.to_formula
| _ (openformula p hp) := by simp
| _ (fal φ)            := by simp; exact push_to_formula φ
| _ (ex φ)             := by simp; exact push_to_formula φ
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.rank)⟩]}

@[simp] lemma rank_push : ∀ {n} (φ : pnf L (n + 1)), rank (push φ) = rank φ
| n (openformula p hp) := by simp
| n (fal p) := by show (∀'p).push.rank = p.fal.rank; simpa using rank_push p
| n (ex p) := by show (∃'p).push.rank = p.ex.rank; simpa using rank_push p
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.rank)⟩]}

end push

section pull

@[simp] def pull : Π {n}, pnf L n → pnf L (n + 1)
| n (openformula p hp) := openformula p.pull (by simpa using hp)
| n (fal φ)            := fal (pull φ)
| n (ex  φ)            := ex (pull φ)

@[simp] lemma pull_forall (φ : pnf L (n + 1)) : pull (∀'φ) = ∀'(pull φ) := by simp[has_univ_quantifier'.univ]

@[simp] lemma pull_exists (φ : pnf L (n + 1)) : pull (∃'φ) = ∃'(pull φ) := by simp[has_exists_quantifier'.ex]

@[simp] lemma pull_to_formula : ∀ {n} (φ : pnf L n), φ.pull.to_formula = 𝗡 φ.to_formula
| _ (openformula p hp) := by simp
| _ (fal φ)            := by simp; exact pull_to_formula φ
| _ (ex φ)             := by simp; exact pull_to_formula φ

@[simp] lemma pull_push : ∀ {n} (φ : pnf L n), φ.pull.push = φ
| _ (openformula p hp) := by simp
| _ (fal φ)            := by simpa using pull_push φ
| _ (ex φ)             := by simpa using pull_push φ

@[simp] lemma push_pull : ∀ {n} (φ : pnf L (n + 1)), φ.push.pull = φ
| _ (openformula p hp) := by simp
| _ (fal φ)            := by simpa using push_pull φ
| _ (ex φ)             := by simpa using push_pull φ
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.rank)⟩]}

lemma foralls_comm (φ : pnf L (n + 1)) : ∀'*(∀'φ) = ∀'(∀'*φ.push).pull :=
by { induction n with n IH, { simp }, { simpa using IH (∀'φ) } }

lemma exists_comm (φ : pnf L (n + 1)) : ∃'*(∃'φ) = ∃'(∃'*φ.push).pull :=
by { induction n with n IH, { simp }, { simpa using IH (∃'φ) } }

end pull

section subst

def msubst (u : subterm L n) : pnf L n → pnf L n := rew (u .> subterm.metavar)

def subst (u : subterm L n) : pnf L (n + 1) → pnf L n := msubst u ∘ push

@[simp] lemma msubst_openformula (u) (p : subformula L n) (hp) :
  msubst u (openformula p hp) = openformula (subformula.msubst u p) (by simpa using hp) :=
by simp[msubst, nat.comp_left_concat]; refl

@[simp] lemma msubst_fal (u) (φ : pnf L (n + 1)) : msubst u (∀'φ) = ∀'msubst u.lift φ :=
by simp[msubst, nat.comp_left_concat]

@[simp] lemma msubst_ex (u) (φ : pnf L (n + 1)) : msubst u (∃'φ) = ∃'msubst u.lift φ :=
by simp[msubst, nat.comp_left_concat]

@[simp] def msubat_to_formula (u) (φ : pnf L n) :
  (msubst u φ).to_formula = subformula.msubst u φ.to_formula :=
by simp[msubst]; refl

@[simp] def rank_msubat (u) (φ : pnf L n) : (msubst u φ).rank = φ.rank :=
by simp[msubst]

end subst

section dummy

def dummy : pnf L n → pnf L (n + 1) := pull ∘ mlift

@[simp] lemma push_dummy (φ : pnf L n) : push (dummy φ) = mlift φ :=
by simp[dummy]

lemma dummy_openformula (p : subformula L n) (hp) :
  dummy (openformula p hp) = openformula p.dummy (by simpa using hp) := by simp[dummy]; refl

@[simp] lemma dummy_forall (φ : pnf L (n + 1)) : dummy (∀'φ) = ∀'(dummy φ) := by simp[dummy]

@[simp] lemma dummy_exists (φ : pnf L (n + 1)) : dummy (∃'φ) = ∃'(dummy φ) := by simp[dummy]

@[simp] lemma dummy_to_formula (φ : pnf L n) : φ.dummy.to_formula = 𝗗 φ.to_formula :=
by simp[mlift_to_formula, pull_to_formula, dummy, subformula.dummy]

@[simp] lemma rank_dummy : ∀ {n} (φ : pnf L n), rank (dummy φ) = rank φ
| n (openformula p hp) := by simp[dummy_openformula]
| n (fal p) := by show (∀'p).dummy.rank = p.fal.rank; simpa using rank_dummy p
| n (ex p) := by show (∃'p).dummy.rank = p.ex.rank; simpa using rank_dummy p

end dummy

section forall_pnf

inductive forall_pnf : ∀ {n}, pnf L n → Prop
| openformula : ∀ {n} (p : subformula L n) hp, forall_pnf (openformula p hp)
| fal : ∀ {n} {φ : pnf L (n + 1)}, forall_pnf φ → forall_pnf (∀'φ)

attribute [simp] forall_pnf.openformula

@[simp] lemma forall_pnf_fal_iff (φ : pnf L (n + 1)) : forall_pnf (∀'φ) ↔ forall_pnf φ :=
⟨by { rintros ⟨⟩, assumption }, by { intros h, exact h.fal }⟩

@[simp] lemma not_forall_pnf_ex (φ : pnf L (n + 1)) : ¬forall_pnf (∃'φ) :=
by rintros ⟨⟩

@[simp] lemma forall_pnf_push_iff : ∀ {n} (φ : pnf L (n + 1)), forall_pnf (push φ) ↔ forall_pnf φ
| n (openformula p hp) := by simp
| n (fal φ)            := by simp[fal_eq, forall_pnf_push_iff φ]
| n (ex φ)             := by simp[ex_eq]
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.rank)⟩]}

@[simp] lemma forall_pnf_pull_iff : ∀ {n} (φ : pnf L n), forall_pnf (pull φ) ↔ forall_pnf φ
| n (openformula p hp) := by simp
| n (fal φ)            := by simp[fal_eq, forall_pnf_pull_iff φ]
| n (ex φ)             := by simp[ex_eq]

@[simp] lemma forall_pnf_msubst_iff : ∀ {n} (u) (φ : pnf L n), forall_pnf (msubst u φ) ↔ forall_pnf φ
| n u (openformula p hp) := by simp
| n u (fal φ)            := by simp[fal_eq]; exact forall_pnf_msubst_iff u.lift φ
| n u (ex φ)             := by simp[ex_eq]

@[simp] lemma forall_pnf_univ_closure (φ : pnf L n) : forall_pnf (∀'*φ) ↔ forall_pnf φ :=
by induction n with n IH; simp*

@[simp] def open_form : Π (φ : pnf L 0), subformula L φ.rank
| (openformula p hp) := p
| (fal φ)            :=
    by rw[show φ.fal.rank = φ.push.rank + 1, by simp]; exact (open_form φ.push).pull
| (ex  φ)            :=
    by rw[show φ.ex.rank = φ.push.rank + 1, by simp]; exact (open_form φ.push).pull
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.rank)⟩]}

lemma univ_closure_of_forall_pnf : ∀ (φ : pnf L 0), forall_pnf φ →
  ∃ (n) (p : subformula L n) (hp : is_open p), φ = ∀'*(openformula p hp)
| (openformula p hp) _ :=⟨0, p, hp, by simp⟩
| (fal φ)            h :=
    begin
      have : ∃ n (p : subformula L n) (hp : p.is_open), φ.push = ∀'* (openformula p hp),
      from univ_closure_of_forall_pnf φ.push (by simpa[fal_eq] using h),
      rcases this with ⟨n, p, hp, h⟩,
      refine ⟨n + 1, p.pull, by simpa using hp, by simpa[fal_eq, foralls_comm] using congr_arg pull h⟩
    end
| (ex φ)            h := by simp[ex_eq] at h; contradiction
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.1.rank)⟩]}

@[simp] def kernel : ∀ {n} (φ : pnf L n), Σ n, subformula L n
| n (openformula p hp) := ⟨n, p⟩
| n (fal φ)            := φ.kernel
| n (ex φ)             := φ.kernel

lemma kernel_eq_rank : ∀ {n} (φ : pnf L n), φ.kernel.1 = φ.rank + n
| n (openformula p hp) := by simp
| n (fal φ)            := by simp[kernel_eq_rank φ, add_assoc, add_comm]
| n (ex φ)             := by simp[kernel_eq_rank φ, add_assoc, add_comm]

@[simp] lemma kernel_is_open : ∀ {n} (φ : pnf L n), φ.kernel.2.is_open
| n (openformula p hp) := hp
| n (fal φ)            := kernel_is_open φ
| n (ex φ)             := kernel_is_open φ

lemma univ_closure_to_formula (φ : pnf L 0) (h : forall_pnf φ) :
  ∃ (n) (p : subformula L n) (hp : is_open p), φ.to_formula = ∀'*p :=
by { rcases univ_closure_of_forall_pnf φ h with ⟨n, p, hp, rfl⟩,
     refine ⟨n, p, hp, by simp⟩ }

end forall_pnf

@[simp] def neg : Π {n}, pnf L n → pnf L n
| n (openformula p hp) := openformula (∼p) (by simpa[is_open] using hp)
| n (fal φ)            := ∃'(pull $ neg $ push φ)
| n (ex φ)             := ∀'(pull $ neg $ push φ)
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.rank)⟩]}

@[simp] def imply : Π {n}, pnf L n → pnf L n → pnf L n
| n (openformula p hp) (openformula q hq) := openformula (p ⟶ q) (by simp; exact ⟨hp, hq⟩)
| n (openformula p hp) (fal ψ)            := ∀'pull (imply (mlift $ openformula p hp) (push ψ))
| n (openformula p hp) (ex ψ)             := ∃'pull (imply (mlift $ openformula p hp) (push ψ))
| n (fal φ)            ψ                  := ∃'pull (imply (push φ) (mlift ψ))
| n (ex φ)             ψ                  := ∀'pull (imply (push φ) (mlift ψ))
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.1.rank + x.2.2.rank)⟩]}

open axiomatic_classical_logic' axiomatic_classical_logic provable

lemma equiv_to_formula_neg : ∀ (T : preTheory L) (p : pnf L 0), T ⊢ (p.neg).to_formula ⟷ ∼p.to_formula
| T (openformula p hp) := by simp
| T (pnf.fal φ) :=
    begin
      simp, show T ⊢ ∃'𝗡 φ.push.neg.to_formula ⟷ ∼∀'φ.to_formula,
      have : 𝗟'T ⊢ φ.push.neg.to_formula ⟷ ∼𝗠 φ.to_formula, by simpa using equiv_to_formula_neg 𝗟'T φ.push,
      have : T ⊢ ∃'𝗡 φ.push.neg.to_formula ⟷ ∃'∼φ.to_formula, by simpa using equiv_exists_of_equiv' this,
      refine equiv_trans this (equiv_symm $ neg_forall_pnf _)
    end
| T (pnf.ex φ) :=
    begin
      simp, show T ⊢ ∀'𝗡 φ.push.neg.to_formula ⟷ ∼∃'φ.to_formula,
      have : 𝗟'T ⊢ φ.push.neg.to_formula ⟷ ∼𝗠 φ.to_formula, by simpa using equiv_to_formula_neg 𝗟'T φ.push,
      have : T ⊢ ∀'𝗡 φ.push.neg.to_formula ⟷ ∀'∼φ.to_formula, by simpa using equiv_forall_of_equiv' this,
      refine equiv_trans this (equiv_symm $ neg_exists_pnf _)
    end
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.rank)⟩]}

lemma equiv_to_formula_imply : ∀ (T : preTheory L) (p q : pnf L 0),
  T ⊢ (p.imply q).to_formula ⟷ (p.to_formula ⟶ q.to_formula)
| T (openformula p hp) (openformula q hq) := by simp
| T (openformula p hp) (fal ψ)            :=
    let φ := openformula p hp in
    begin
      simp, show T ⊢ (∀'𝗡 (φ.mlift.imply ψ.push).to_formula) ⟷ (p ⟶ ∀'ψ.to_formula),
      have : 𝗟'T ⊢ (φ.mlift.imply ψ.push).to_formula ⟷ (𝗟 p ⟶ 𝗠 ψ.to_formula),
      by simpa using equiv_to_formula_imply 𝗟'T φ.dummy.push ψ.push,
      have : T ⊢ ∀'𝗡 (φ.mlift.imply ψ.push).to_formula ⟷ ∀'(𝗗 p ⟶ ψ.to_formula),
      by simpa using equiv_forall_of_equiv' this,
      refine equiv_trans this (equiv_symm $ imply_forall_pnf _ _)
    end
| T (openformula p hp) (ex ψ)             :=
    let φ := openformula p hp in
    begin
      simp, show T ⊢ (∃'𝗡 (φ.mlift.imply ψ.push).to_formula) ⟷ (p ⟶ ∃'ψ.to_formula),
      have : 𝗟'T ⊢ (φ.mlift.imply ψ.push).to_formula ⟷ (𝗟 p ⟶ 𝗠 ψ.to_formula),
      by simpa using equiv_to_formula_imply 𝗟'T φ.dummy.push ψ.push,
      have : T ⊢ ∃'𝗡 (φ.mlift.imply ψ.push).to_formula ⟷ ∃'(𝗗 p ⟶ ψ.to_formula),
      by simpa using equiv_exists_of_equiv' this,
      refine equiv_trans this (equiv_symm $ imply_exists_pnf _ _)
    end
| T (fal φ)            ψ                  :=
    begin
      simp, show T ⊢ (∃'𝗡 (φ.push.imply ψ.mlift).to_formula) ⟷ (∀'φ.to_formula ⟶ ψ.to_formula),
      have : 𝗟'T ⊢ (φ.push.imply ψ.mlift).to_formula ⟷ (𝗠 φ.to_formula ⟶ 𝗟 ψ.to_formula),
      by simpa using equiv_to_formula_imply 𝗟'T φ.push ψ.mlift,
      have : T ⊢ ∃'𝗡 (φ.push.imply ψ.mlift).to_formula ⟷ ∃'(φ.to_formula ⟶ 𝗗 ψ.to_formula),
      by simpa using equiv_exists_of_equiv' this,
      refine equiv_trans this (equiv_symm $ forall_imply_pnf _ _)
    end
| T (ex φ)             ψ                  :=
    begin
      simp, show T ⊢ (∀'𝗡 (φ.push.imply ψ.mlift).to_formula) ⟷ (∃'φ.to_formula ⟶ ψ.to_formula),
      have : 𝗟'T ⊢ (φ.push.imply ψ.mlift).to_formula ⟷ (𝗠 φ.to_formula ⟶ 𝗟 ψ.to_formula),
      by simpa using equiv_to_formula_imply 𝗟'T φ.push ψ.mlift,
      have : T ⊢ ∀'𝗡 (φ.push.imply ψ.mlift).to_formula ⟷ ∀'(φ.to_formula ⟶ 𝗗 ψ.to_formula),
      by simpa using equiv_forall_of_equiv' this,
      refine equiv_trans this (equiv_symm $ exists_imply_pnf _ _)
    end
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.1.rank + x.2.2.rank)⟩]}

--instance : has_logic_symbol (pnf L n) := logic_simbol_default (pnf L n) (openformula ⊤ (by simp)) neg imply

end pnf

namespace subformula
open pnf axiomatic_classical_logic' axiomatic_classical_logic provable
variables {L n} (T : preTheory L)

@[simp] def to_pnf : Π {n}, subformula L n → pnf L n
| n verum          := openformula ⊤ (by simp)
| n (relation r v) := openformula (relation r v) (by simp)
| n (imply p q)    := (to_pnf p).imply (to_pnf q)
| n (neg p)        := (to_pnf p).neg
| n (fal p)        := ∀'pnf.pull (to_pnf (𝗠 p))
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.complexity)⟩]}

def normalize (p : subformula L n) : subformula L n := p.to_pnf.to_formula

@[simp] lemma to_pnf_top : to_pnf (⊤ : subformula L n) = openformula ⊤ (by simp) := by unfold has_top.top; simp; refl

@[simp] lemma to_pnf_imply (p q : subformula L n) : to_pnf (p ⟶ q) = (to_pnf p).imply (to_pnf q) :=
by unfold has_arrow.arrow; simp; refl

@[simp] lemma to_pnf_neg (p : subformula L n) : to_pnf (∼p) = (to_pnf p).neg :=
by unfold has_negation.neg; simp; refl

@[simp] lemma to_pnf_fal (p : subformula L (n + 1)) : to_pnf (∀'p) = ∀'(pnf.pull $ to_pnf $ 𝗠 p) :=
by unfold has_univ_quantifier'.univ; simp; refl

end subformula

section 
open pnf subformula axiomatic_classical_logic' axiomatic_classical_logic provable

lemma equiv_normalize : ∀ (T : preTheory L) (p), T ⊢ normalize p ⟷ p
| T verum          := by simp[top_eq, normalize]
| T (relation r v) := by simp[normalize]
| T (imply p q)    := by {
    simp[imply_eq, normalize],
    have : T ⊢ (p.to_pnf.imply q.to_pnf).to_formula ⟷ (p.normalize ⟶ q.normalize),
    from equiv_to_formula_imply T p.to_pnf q.to_pnf,
    exact equiv_trans this (equiv_imply_of_equiv (equiv_normalize T p) (equiv_normalize T q)) }
| T (neg p)        := by { 
    simp[neg_eq, normalize],
    have : T ⊢ p.to_pnf.neg.to_formula ⟷ ∼p.normalize, from equiv_to_formula_neg T p.to_pnf,
    exact equiv_trans this (equiv_neg_of_equiv (equiv_normalize T p)) }
| T (fal p)        := by { 
    simp[subformula.fal_eq, normalize],
    have : 𝗟'T ⊢ (𝗠 p).normalize ⟷ 𝗠 p, by simpa using equiv_normalize 𝗟'T p.push,
    exact equiv_forall_of_equiv (by simpa using this) }
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.complexity)⟩]}

end

end fol