import arithmetic

namespace fopl

namespace arithmetic

@[simp] def nat_fn : ∀ n, LA.fn n → dvector ℕ n → ℕ
| 0 langf.zero nil             := 0
| 1 langf.succ (n :: nil)      := n + 1
| 2 langf.add  (n :: m :: nil) := n + m
| 2 langf.mult (n :: m :: nil) := n * m

@[simp] def nat_pr : ∀ n, LA.pr n → dvector ℕ n → Prop
| 2 langp.le  (n :: m :: nil) := n ≤ m

def Num : model LA := ⟨ℕ, 0, nat_fn, nat_pr⟩
notation `𝒩` := Num

@[reducible, simp] lemma nat_dom_eq : Num.dom = ℕ := rfl

@[simp] lemma nat_fn_eq : Num.fn = nat_fn := rfl

@[simp] lemma nat_pr_eq : Num.pr = nat_pr := rfl

lemma N_models_Q : 𝒩 ⊧ₜₕ 𝐐 := λ p hyp_p e,
begin
  cases hyp_p; simp,
  { exact λ _, of_to_bool_ff rfl},
  { exact λ _ _, nat.succ.inj },
  { exact λ _, nat.exists_eq_succ_of_ne_zero },
  { exact λ n m, by simp[add_assoc] },
  { exact λ n m, nat.mul_succ m n },
  { intros n m, split; intros h,
    refine ⟨(n - m : ℕ), nat.add_sub_of_le h⟩,
    rcases h with ⟨_, h⟩, exact nat.le.intro h }
end

theorem Q_consistent : theory.consistent 𝐐 := model_consistent N_models_Q

def peano_ind (p : formula LA) : formula LA :=
p.rew ₛ[Ż] ⩑ ∀̇ (p →̇ ∀̇ (#1 =̇ Ṡ #0 →̇ p.sf)) →̇ ∀̇ p

lemma mjbjhv (p : formula LA) : 𝒩 ⊧ peano_ind p := λ e,
by { simp[peano_ind, rew_val_iff], }

lemma N_models_bd_PA (C : formula LA → Prop) : 𝒩 ⊧ₜₕ 𝐐+𝐈C := λ p hyp_p e,
by { cases hyp_p with _ hyp_p p,
     exact N_models_Q p hyp_p e,
       simp[rew_val_iff],
  intros h0 hIH n,
  induction n with n IH,
  { have : (λ n, (vecterm.val e (ₛ[Ż] n)).head) = ((0 : ℕ) ^ˢ e),
    { funext n, cases n; simp[slide] },
    simp[this] at h0, exact h0 },
  { have hIH' := hIH n IH,
    have : (λ m, (vecterm.val (n ^ˢ e : ℕ → Num.dom) (ₑ[Ṡ #0] m)).head) = (n+1 : ℕ) ^ˢ e,
    { funext n, cases n; simp[slide, embed] },
    simp[this] at hIH', exact hIH' } }

theorem bd_PA_consistent (C) : theory.consistent 𝐐+𝐈C := model_consistent (N_models_bd_PA C)

lemma N_models_PA : 𝒩 ⊧ₜₕ 𝐏𝐀 := N_models_bd_PA _

theorem PA_consistent : theory.consistent 𝐏𝐀 := model_consistent N_models_PA

def true_arithmetic : theory LA := {p | 𝒩 ⊧ p}
notation `𝐓𝐀` := true_arithmetic

lemma N_models_TA : 𝒩 ⊧ₜₕ 𝐓𝐀 := λ p hyp_p e, hyp_p e

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

@[simp] def Noncomm_fn : ∀ n, LA.fn n → dvector noncomm n → noncomm
| 0 langf.zero nil             := nat₀ 0
| 1 langf.succ (n :: nil)      := n.succ
| 2 langf.add  (n :: m :: nil) := n.add m
| 2 langf.mult (n :: m :: nil) := n.mul m

@[simp] def Noncomm_pr : ∀ n, LA.pr n → dvector noncomm n → Prop
| 2 langp.le  (n :: m :: nil) := ∃ d, n.add d = m

def Noncomm : model LA := ⟨noncomm, nat₀ 0, Noncomm_fn, Noncomm_pr⟩

@[reducible, simp] lemma Noncomm_dom_eq : |Noncomm| = noncomm := rfl

@[simp] lemma Noncomm_fn_eq : Noncomm.fn = Noncomm_fn := rfl

@[simp] lemma Noncomm_pr_eq : Noncomm.pr = Noncomm_pr := rfl

theorem Noncomm_models_Q : Noncomm ⊧ₜₕ 𝐐 := λ p hyp_p e,
begin
  cases hyp_p; simp[Noncomm_fn],
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

theorem refutable_comm_add : ¬𝐐 ⊢ ∀̇ ∀̇ (#0 +̇ #1 =̇ #1 +̇ #0) := λ h,
by { have : Noncomm ⊧ ∀̇ ∀̇ (#0 +̇ #1 =̇ #1 +̇ #0), from soundness h Noncomm_models_Q,
     have : ∀ n m, add m n = add n m,
     { have := this (λ x, default _), simp at this, exact this },
     have := this (int₁ 0) (int₂ 0),
     simp at this, exact this }

theorem refutable_comm_mul : ¬𝐐 ⊢ ∀̇ ∀̇ (#0 ×̇ #1 =̇ #1 ×̇ #0) := λ h,
by { have : Noncomm ⊧ ∀̇ ∀̇ (#0 ×̇ #1 =̇ #1 ×̇ #0), from soundness h Noncomm_models_Q,
     have : ∀ n m, mul m n = mul n m,
     { have := this (λ x, default _), simp at this, exact this },
     have := this (int₁ 0) (int₂ 0),
     simp at this, exact this }

theorem refutable_zero_mul : ¬𝐐 ⊢ ∀̇ (Ż ×̇ #0 =̇ Ż) := λ h,
by { have : Noncomm ⊧ ∀̇ (Ż ×̇ #0 =̇ Ż), from soundness h Noncomm_models_Q,
     have : ∀ n, mul (nat₀ 0) n = nat₀ 0,
     { have := this (λ x, default _), simp at this, exact this },
     have := this (int₁ 0),
     simp at this, exact this }

end noncomm

end nonstandard_model

end arithmetic

end fopl