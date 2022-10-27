import arithmetic

namespace fopl

namespace arithmetic

local infix ` ≃₁ `:80 := ((≃) : term LA → term LA → formula LA)
local prefix `∏₁ `:64 := (has_univ_quantifier.univ : formula LA → formula LA)
local prefix `∐₁ `:64 := (has_exists_quantifier.ex : formula LA → formula LA)

def standard : model LA := {
  dom := ℕ,
  inhabited := nat.inhabited,
  fn := λ n l v, 
    match n, l, v with
    | 0, langf.zero, v := 0
    | 1, langf.succ, v := v 0 + 1
    | 2, langf.add,  v := v 0 + v 1
    | 2, langf.mul,  v := v 0 * v 1
    end,
  pr := λ n l v,
    match n, l, v with
    | 2, langp.le, v := v 0 ≤ v 1
    end }

notation `ℕ*` := standard

@[reducible, simp] lemma nat_dom_eq : |ℕ*| = ℕ := rfl

@[simp] lemma standard_zero_eq (v : fin 0 → ℕ) : standard.fn *Z v = (0 : ℕ) := rfl

@[simp] lemma standard_succ_eq (v : fin 1 → ℕ) : standard.fn *S v = (v 0 + 1 : ℕ) := rfl

@[simp] lemma standard_add_eq (v : fin 2 → ℕ) : standard.fn *+ v = (v 0 + v 1 : ℕ) := rfl

@[simp] lemma standard_mul_eq (v : fin 2 → ℕ) : standard.fn *× v = (v 0 * v 1 : ℕ) := rfl

@[simp] lemma standard_le_eq (v : fin 2 → ℕ) : standard.pr *≤ v ↔ (v 0 : ℕ) ≤ v 1 := by refl

lemma N_models_Q : ℕ* ⊧ₜₕ 𝐐 := λ p hyp_p e,
begin
  cases hyp_p; simp[symbol.zero, symbol.succ, symbol.add, symbol.mul, finitary.cons],
  { exact λ _, of_to_bool_ff rfl},
  { exact λ _ _, nat.succ.inj },
  { intros n, cases n,
    { left, refl }, { right, refine ⟨n, rfl⟩ } },
  { intros n, simp[add_assoc] },
  { intros n m, exact nat.mul_succ m n },
  { intros n m, split; intros h,
    refine ⟨(n - m : ℕ), nat.add_sub_of_le h⟩,
    rcases h with ⟨_, h⟩, exact nat.le.intro h }
end

theorem Q_consistent : theory.consistent 𝐐 := model_consistent N_models_Q

lemma mjbjhv (p : formula LA) : ℕ* ⊧ 𝐈p := λ e,
by { simp[peano_induction], intros h0 ih n,
     induction n with n IH, exact h0, exact ih n IH
      }

lemma N_models_bd_PA (C : formula LA → Prop) : ℕ* ⊧ₜₕ 𝐐+𝐈C := λ p hyp_p e,
by { cases hyp_p with _ hyp_p p,
     exact N_models_Q p hyp_p e,
     simp,
     intros h0 ih n,
     induction n with n IH, exact h0, exact ih n IH }

theorem bd_PA_consistent (C) : theory.consistent 𝐐+𝐈C := model_consistent (N_models_bd_PA C)

lemma N_models_PA : ℕ* ⊧ₜₕ 𝐏𝐀 := N_models_bd_PA _

theorem PA_consistent : theory.consistent 𝐏𝐀 := model_consistent N_models_PA

def true_arithmetic : theory LA := {p | ℕ* ⊧ p}
notation `𝐓𝐀` := true_arithmetic

lemma N_models_TA : ℕ* ⊧ₜₕ 𝐓𝐀 := λ p hyp_p e, hyp_p e

theorem TA_consistent : theory.consistent 𝐓𝐀 := model_consistent N_models_TA

namespace nonstandard_model

inductive noncomm : Type
| nat₀ (n : ℕ) : noncomm
| int₁ (i : ℤ) : noncomm
| int₂ (i : ℤ) : noncomm

/- 
                   - ... -2₁, -1₁, 0₁, 1₁, 2₁, ... 
                  /
 0₀, 1₀, 2₀, ... -
                  \
                   - ... -2₂, -1₂, 0₂, 1₂, 2₂, ...
-/

namespace noncomm 

@[simp] theorem nat₀.inj_iff {a b} : nat₀ a = nat₀ b ↔ a = b :=
⟨noncomm.nat₀.inj, congr_arg _⟩

@[simp] theorem int₁.inj_iff {a b} : int₁ a = int₁ b ↔ a = b :=
⟨noncomm.int₁.inj, congr_arg _⟩

@[simp] theorem int₂.inj_iff {a b} : int₂ a = int₂ b ↔ a = b :=
⟨noncomm.int₂.inj, congr_arg _⟩

@[simp] def succ : noncomm → noncomm
| (nat₀ n) := nat₀ (n + 1)
| (int₁ i) := int₁ (i + 1)
| (int₂ i) := int₂ (i + 1)

@[simp] def add : noncomm → noncomm → noncomm
| (nat₀ n) (nat₀ m) := nat₀ (n + m)
| (nat₀ n) (int₁ i) := int₁ (n + i)
| (nat₀ n) (int₂ i) := int₂ (n + i)
| (int₁ i) (nat₀ n) := int₁ (i + n)
| (int₁ i) (int₁ j) := int₁ (i + j)
| (int₁ i) (int₂ j) := int₁ (i + j)
| (int₂ i) (nat₀ n) := int₂ (i + n)
| (int₂ i) (int₁ j) := int₂ (i + j)
| (int₂ i) (int₂ j) := int₂ (i + j)

@[simp] def mul : noncomm → noncomm → noncomm
| n        (nat₀ 0)     := nat₀ 0
| n        (nat₀ (m+1)) := add (mul n (nat₀ m)) n
| (nat₀ n) (int₁ i)     := int₁ (n * i)
| (nat₀ n) (int₂ i)     := int₂ (n * i)
| (int₁ i) (int₁ j)     := int₁ (i * j)
| (int₁ i) (int₂ j)     := int₁ (i * j)
| (int₂ i) (int₁ j)     := int₂ (i * j)
| (int₂ i) (int₂ j)     := int₂ (i * j)

@[simp] def Noncomm_fn : ∀ n, LA.fn n → finitary noncomm n → noncomm
| 0 langf.zero _ := nat₀ 0
| 1 langf.succ v := (v 0).succ
| 2 langf.add  v := (v 0).add (v 1)
| 2 langf.mul  v := (v 0).mul (v 1)

@[simp] def Noncomm_pr : ∀ n, LA.pr n → finitary noncomm n → Prop
| 2 langp.le  v := ∃ d, (v 0).add d = v 1

def Noncomm : model LA := ⟨noncomm, ⟨nat₀ 0⟩, Noncomm_fn, Noncomm_pr⟩

@[reducible, simp] lemma Noncomm_dom_eq : |Noncomm| = noncomm := rfl

@[simp] lemma Noncomm_fn_eq : Noncomm.fn = Noncomm_fn := rfl

@[simp] lemma Noncomm_pr_eq : Noncomm.pr = Noncomm_pr := rfl

theorem Noncomm_models_Q : Noncomm ⊧ₜₕ 𝐐 := λ p hyp_p e,
begin
  cases hyp_p; simp[Noncomm_fn ,symbol.zero, symbol.succ, symbol.add, symbol.mul, finitary.cons],
  { intros d, cases d; simp, exact of_to_bool_ff rfl },
  { intros d₁ d₂, cases d₁; cases d₂; simp[sum.inl.inj_iff, sum.inr.inj_iff] },
  { intros d, cases d; simp,
    { cases d; simp, refine ⟨nat₀ d, rfl⟩ },
    { refine ⟨int₁ (d - 1), _⟩, simp },
    { refine ⟨int₂ (d - 1), _⟩, simp } },
  { intros d, cases d; simp },
  { intros d₁ d₂, cases d₁; cases d₂; simp[add_assoc] },
  { intros d, cases d; simp },
  { intros d₁ d₂, cases d₁; cases d₂; simp[int.distrib_left] },
  { intros d₁ d₂, refl }
end

theorem refutable_comm_add : ¬𝐐 ⊢ ∏₁ ∏₁ (#0 +̇ #1 ≃₁ #1 +̇ #0) := λ h,
by { have : Noncomm ⊧ ∏ ∏ (#0 +̇ #1 ≃ #1 +̇ #0), from soundness h Noncomm_models_Q,
     have : ∀ n m, add m n = add n m,
     { have := this (λ x, default _), simp[symbol.add] at this, exact this },
     have := this (int₁ 0) (int₂ 0),
     simp at this, exact this }

theorem refutable_comm_mul : ¬𝐐 ⊢ ∏₁ ∏₁ (#0 ×̇ #1 ≃₁ #1 ×̇ #0) := λ h,
by { have : Noncomm ⊧ ∏ ∏ (#0 ×̇ #1 ≃ #1 ×̇ #0), from soundness h Noncomm_models_Q,
     have : ∀ n m, mul m n = mul n m,
     { have := this (λ x, default _), simp at this, exact this },
     have := this (int₁ 0) (int₂ 0),
     simp at this, exact this }

theorem refutable_zero_mul : ¬𝐐 ⊢ ∏₁ (Ż ×̇ #0 ≃₁ Ż) := λ h,
by { have : Noncomm ⊧ ∏ (Ż ×̇ #0 ≃ Ż), from soundness h Noncomm_models_Q,
     have : ∀ n, mul (nat₀ 0) n = nat₀ 0,
     { have := this (λ x, default _), simp at this, exact this },
     have := this (int₁ 0),
     simp at this, exact this }

end noncomm

end nonstandard_model

end arithmetic

end fopl