import deduction semantics cltheory

namespace fopl

inductive langf : ℕ → Type
| zero : langf 0
| succ : langf 1
| add  : langf 2
| mult : langf 2
notation `*Z` := langf.zero
notation `*S` := langf.succ
notation `*+` := langf.add
notation `*×` := langf.mult

inductive langp : ℕ → Type
| le : langp 2
notation `*≤` := langp.le

def LA : language := ⟨langf, langp⟩

@[reducible] def symbol.zero : term LA := vecterm.const *Z
notation `Ż` := symbol.zero

@[reducible] def symbol.succ : term LA → term LA := λ x, vecterm.app *S x
prefix `Ṡ `:max := symbol.succ

@[reducible] def symbol.add : term LA → term LA → term LA := λ x y, vecterm.app *+ (x ::: y)
infixl ` +̇ `:92 := symbol.add 

@[reducible] def symbol.mult : term LA → term LA → term LA := λ x y, vecterm.app *× (x ::: y)
infixl ` ×̇ `:94 := symbol.mult

@[reducible] def symbol.le : term LA → term LA → formula LA := λ x y, formula.app *≤ (x ::: y)
infixl ` ≤̇ `:90 := symbol.le

def symbol.lt (t u : term LA) : formula LA := ¬̇(u ≤̇ t)
infix `<̇`:90 := symbol.lt

def term.pair (u t₁ t₂ : term LA) : formula LA :=
(t₁ <̇ t₂ ⩑ u =̇ t₂ ×̇ t₂ +̇ t₁) ⩒ (t₂ ≤̇ t₁ ⩑ u =̇ t₁ ×̇ t₁ +̇ t₁ +̇ t₂)
notation u` =⟨`t₁`, `t₂`⟩` := term.pair u t₁ t₂

def term.divide (t u : term LA) : formula LA := ∃̇(t ×̇ #0 =̇ u)
infix `|` := term.divide

instance (T : theory LA) (i) : has_zero (Herbrand T i) := ⟨Herbrand.function₀ T i *Z⟩
instance (T : theory LA) (i) : has_add (Herbrand T i) := ⟨Herbrand.function₂ T i *+⟩
instance (T : theory LA) (i) : has_mul (Herbrand T i) := ⟨Herbrand.function₂ T i *×⟩
def lessthan {T : theory LA} {i} : Herbrand T i → Herbrand T i → Lindenbaum T i := Lindenbaum.predicate₂ T i *≤
infix ` ≼ `:50 := lessthan
def Succ {T : theory LA} {i} : Herbrand T i → Herbrand T i := Herbrand.function₁ T i *S
lemma zero_eq {T : theory LA} {i : ℕ} : Herbrand.function₀ T i *Z = 0 := rfl
lemma Succ_eq {T : theory LA} {i : ℕ} : Herbrand.function₁ T i *S = Succ := rfl

variables (s : ℕ → term LA)

def numeral : ℕ → term LA
| 0     := Ż
| (n+1) := Ṡ (numeral n)

local notation n`˙`:1200 := numeral n

lemma numeral_arity0 : ∀ n, (n˙).arity = 0
| 0     := rfl
| (n+1) := by simp[numeral, vecterm.arity, @numeral_arity0 n]

@[elab_as_eliminator] 
lemma LA_ind {C : term LA → Sort*}
  (var  : ∀ n, C(#n))
  (zero : C (Ż))
  (succ : ∀ {t₁}, C t₁ → C (Ṡ t₁))
  (add  : ∀ {t₁ t₂}, C t₁ → C t₂ → C (t₁ +̇ t₂)) 
  (mul  : ∀ {t₁ t₂}, C t₁ → C t₂ → C (t₁ ×̇ t₂)) : ∀ t, C t
| (#n)                                  := var n
| (vecterm.const *Z)                    := zero
| (vecterm.app *S t)                    := succ (LA_ind t)
| (vecterm.app *+ (vecterm.cons t₁ t₂)) := add (LA_ind t₁) (LA_ind t₂)
| (vecterm.app *× (vecterm.cons t₁ t₂)) := mul (LA_ind t₁) (LA_ind t₂)

@[elab_as_eliminator] 
theorem LA_ind_on {C : term LA → Sort*} (t : term LA)
  (var  : ∀ n, C(#n))
  (zero : C (Ż))
  (succ : ∀ {t₁}, C t₁ → C (Ṡ t₁))
  (add  : ∀ {t₁ t₂}, C t₁ → C t₂ → C (t₁ +̇ t₂)) 
  (mul  : ∀ {t₁ t₂}, C t₁ → C t₂ → C (t₁ ×̇ t₂)) : C t :=
LA_ind var zero @succ @add @mul t

def bounded_fal (t : term LA) (p : formula LA) : formula LA := ∀̇(#0 ≤̇ t.sf →̇ p)

notation `[∀̇`` ≤ `t`]`p := bounded_fal t p

def bounded_ext (t : term LA) (p : formula LA) := ∃̇(#0 ≤̇ t.sf ⩑ p)

notation `[∃̇`` ≤ `t`]`p := bounded_ext t p

#check [∃̇ ≤ #2][∀̇ ≤ #3]∃̇[∀̇ ≤ #3](#1 ≤̇ #2)

@[simp] lemma bounded_fal_rew (t : term LA) (p : formula LA) (s) : ([∀̇ ≤ t]p).rew s = [∀̇ ≤ t.rew s](p.rew (s^1)) :=
by simp[bounded_fal, vecterm.sf, vecterm.nested_rew]

@[simp] lemma bounded_ex_rew (t : term LA) (p : formula LA) (s) : ([∃̇ ≤ t]p).rew s = [∃̇ ≤ t.rew s](p.rew (s^1)) :=
by simp[bounded_ext, vecterm.sf, vecterm.nested_rew]

inductive robinson : theory LA
| q1 : robinson ∀̇ (Ż ≠̇ Ṡ #0)
| q2 : robinson ∀̇ ∀̇ (Ṡ #0 =̇ Ṡ #1 →̇ #0 =̇ #1)
| q3 : robinson ∀̇ (#0 ≠̇ Ż →̇ ∃̇ (#1 =̇ Ṡ #0))
| q4 : robinson ∀̇ (#0 +̇ Ż =̇ #0)
| q5 : robinson ∀̇ ∀̇ (#0 +̇ Ṡ #1 =̇ Ṡ(#0 +̇ #1))
| q6 : robinson ∀̇ (#0 ×̇ Ż =̇ Ż)
| q7 : robinson ∀̇ ∀̇ (#0 ×̇ Ṡ #1 =̇ #0 ×̇ #1 +̇ #0)
| q8 : robinson ∀̇ ∀̇ (#0 ≤̇ #1 ↔̇ ∃̇ (#1 +̇ #0 =̇ #2))
notation `𝐐` := robinson

def peano_induction (p : formula LA) : formula LA := p.rew ₛ[Ż] ⩑ ∀̇ (p.rew ₑ[#0] →̇ p.rew ₑ[Ṡ #0]) →̇ ∀̇ p
prefix `𝐈`:max := peano_induction

lemma bvjyfjyfh (p : formula LA) : p.rew ₑ[Ṡ #0] = p.sf.rew (ₛ[Ṡ #0]^1) :=
by { simp[formula.sf, formula.nested_rew], }

instance : closed_theory 𝐐 := ⟨λ p h,
  by cases h; simp[sentence, formula.arity, vecterm.arity, formula.iff, formula.ex, formula.and]⟩

instance : proper 0 𝐐 := ⟨λ p s h, by { cases h; simp; exact h }⟩

inductive bounded_peano (C : set (formula LA)) : theory LA
| q   : ∀ {p}, p ∈ 𝐐 → bounded_peano p
| ind : ∀ {p : formula LA}, p ∈ C → bounded_peano 𝐈p
prefix `𝐐+𝐈`:max := bounded_peano

@[reducible] def peano : theory LA := (𝐐+𝐈(set.univ))
notation `𝐏𝐀` := peano

instance {C : set (formula LA)} [proper 0 C] : proper 0 𝐐+𝐈C := ⟨λ p s h,
  by { simp, cases h with _ h p hyp,
       { have : p.rew s ∈ 𝐐, from proper.proper0 h,
         exact bounded_peano.q this },
       { simp,
         have : (p.rew ₛ[Ż]).rew s = (p.rew (s^1)).rew ₛ[Ż],
         { simp[formula.nested_rew], congr, ext x, cases x; simp }, simp[this],
         have : (p.rew ₑ[Ṡ #0]).rew (s^1) = (p.rew (s^1)).sf.rew (ₑ[Ṡ #0]),
         { simp[formula.nested_rew], congr, ext x, cases x; simp, }, simp[this],
         have : p.rew (s^1) ∈ C, from proper.proper0 hyp,
         have := bounded_peano.ind this, exact this } }⟩

lemma Q_bd_peano (C) : 𝐐 ⊆ 𝐐+𝐈C := λ p h, bounded_peano.q h

lemma bd_peano_subset {C D : set (formula LA)} : C ⊆ D → 𝐐+𝐈C ⊆ 𝐐+𝐈D := λ h p hyp_p,
by { cases hyp_p with _ hyp_p p hyp_p2,
     exact bounded_peano.q hyp_p, refine bounded_peano.ind (h hyp_p2) }

namespace hierarchy

mutual inductive sigma_form, pie_form
with sigma_form : ℕ → formula LA → Prop
| op : ∀ {p : formula LA}, p.Open → sigma_form 0 p
| bd_fal : ∀ {p} {n t}, sigma_form n p → sigma_form n [∀̇ ≤ t]p
| bd_ext : ∀ {p} {n t}, sigma_form n p → sigma_form n [∃̇ ≤ t]p
| qt : ∀ {p} {n}, pie_form n p → sigma_form (n+1) ∃̇p 
with pie_form : ℕ → formula LA → Prop
| op : ∀ {p : formula LA}, p.Open → pie_form 0 p
| bd_fal : ∀ {p} {n t}, pie_form n p → pie_form n [∀̇ ≤ t]p
| bd_ext : ∀ {p} {n t}, pie_form n p → pie_form n [∃̇ ≤ t]p
| qt : ∀ {p} {n}, sigma_form n p → pie_form (n+1) ∀̇p

prefix `𝚺¹`:1200 := sigma_form

def sigma (T : theory LA) (n : ℕ) : set (formula LA) := {p | ∃ q, sigma_form n q ∧ T ⊢ q ↔̇ p}
def pie (T : theory LA) (n : ℕ) : set (formula LA) := {p | ∃ q, pie_form n q ∧ T ⊢ q ↔̇ p}
def delta (T : theory LA) (n : ℕ) : set (formula LA) :=
{p | ∃ q₁ q₂, T ⊢ q₁ ↔̇ p ∧ T ⊢ q₂ ↔̇ p ∧ q₁ ∈ sigma T n ∧ q₂ ∈ pie T n}

end hierarchy

@[simp] def nat_fn : ∀ n, LA.fn n → dvector ℕ n → ℕ
| 0 langf.zero nil             := 0
| 1 langf.succ (n :: nil)      := n + 1
| 2 langf.add  (n :: m :: nil) := n + m
| 2 langf.mult (n :: m :: nil) := n * m

@[simp] def nat_pr : ∀ n, LA.pr n → dvector ℕ n → Prop
| 2 langp.le  (n :: m :: nil) := n ≤ m

def Num : model LA := ⟨ℕ, 0, nat_fn, nat_pr⟩
notation `𝒩` := Num

lemma apply_nat_pr (p : LA.pr 2) (a : ℕ) (v : dvector ℕ 1) :
  a :: v = a :: v.head :: dvector.nil := by simp[dvector.head_tail]

lemma apply_nat_fn (f : LA.fn 2) (a : ℕ) (v : dvector ℕ 1) :
  a :: v = a :: v.head :: dvector.nil := by simp[dvector.head_tail]

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

namespace Q_model

inductive noncomm : Type
| nat₀ (n : ℕ) : noncomm
| int₁ (n : ℤ) : noncomm
| int₂ (n : ℤ) : noncomm

/- 
            .    .-- ... -2, -1, 0, 1, 2, ... 
                /
 0, 1, 2, ... --
                \
                 -- ... -2, -1, 0, 1, 2, ...
-/

namespace noncomm 
open noncomm
@[simp] theorem nat₀.inj_iff {a b} : nat₀ a = nat₀ b ↔ a = b :=
⟨noncomm.nat₀.inj, congr_arg _⟩

@[simp] theorem int₁.inj_iff {a b} : int₁ a = int₁ b ↔ a = b :=
⟨noncomm.int₁.inj, congr_arg _⟩

@[simp] theorem int₂.inj_iff {a b} : int₂ a = int₂ b ↔ a = b :=
⟨noncomm.int₂.inj, congr_arg _⟩

@[simp] def succ : noncomm → noncomm
| (nat₀ n) := nat₀ (n+1)
| (int₁ i) := int₁ (i+1)
| (int₂ i) := int₂ (i+1)

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
| (nat₀ n) (int₁ i) := int₁ (n * i)
| (nat₀ n) (int₂ i) := int₂ (n * i)
| (int₁ i) (int₁ j) := int₁ (i * j)
| (int₁ i) (int₂ j) := int₁ (i * j)
| (int₂ i) (int₁ j) := int₂ (i * j)
| (int₂ i) (int₂ j) := int₂ (i * j)

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

theorem refutable_comm : ¬𝐐 ⊢ ∀̇ ∀̇ (#0 +̇ #1 =̇ #1 +̇ #0) := λ h,
by { have : Noncomm ⊧ ∀̇ ∀̇ (#0 +̇ #1 =̇ #1 +̇ #0), from soundness h Noncomm_models_Q,
     have : ∀ n m, add m n = add n m,
     { have := this (λ x, default _), simp at this, exact this },
     have := this (int₁ 0) (int₂ 0),
     simp at this, exact this }

end noncomm


end Q_model

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

namespace robinson
open Herbrand Lindenbaum
variables {T : theory LA} {i : ℕ} [extend 𝐐 T]

open provable

lemma ss_robinson : 𝐐 ⊆ T^i := λ p h,
by { refine sentence_mem_theory_sf_itr (closed_theory.cl h) i (extend.ss h)}

@[simp] lemma add_zero  (h : Herbrand T i) : 0 + h = h :=
by { induction h using fopl.Herbrand.ind_on,
     have : ∀̇(Ż +̇ #0 =̇ #0) ∈ T^i, from ss_robinson robinson.q4,
     have := Herbrand.provable_iff.mp ((AX this).fal_subst h), simp* at *,
     exact this }

@[simp] lemma mul_zero  (h : Herbrand T i) : 0 * h = 0 :=
by { induction h using fopl.Herbrand.ind_on,
     have : ∀̇(Ż ×̇ #0 =̇ Ż) ∈ T^i, from ss_robinson robinson.q6,
     have := (AX this).fal_subst h,
     have := Herbrand.provable_iff.mp this, simp* at this, exact this }

@[simp] lemma add_succ {i} (h₁ h₂ : Herbrand T i) :
  (Succ h₁) + h₂ = Succ (h₁ + h₂) :=
by { induction h₁ using fopl.Herbrand.ind_on, induction h₂ using fopl.Herbrand.ind_on,
     have : ∀̇ ∀̇ (Ṡ #0 +̇ #1 =̇ Ṡ (#0 +̇ #1)) ∈ T^i := ss_robinson robinson.q5,
     have := ((AX this).fal_subst h₂).fal_subst h₁,
     have := Herbrand.provable_iff.mp this, simp* at this, exact this }

@[simp] lemma mul_succ {i} (h₁ h₂ : Herbrand T i) :
  (Succ h₁) * h₂ = h₁ * h₂ + h₂ :=
by { induction h₁ using fopl.Herbrand.ind_on, induction h₂ using fopl.Herbrand.ind_on,
     have : ∀̇ ∀̇ (Ṡ #0 ×̇ #1 =̇ #0 ×̇ #1 +̇ #1) ∈ T^i := ss_robinson robinson.q7,
     have := ((AX this).fal_subst h₂).fal_subst h₁,
     have := Herbrand.provable_iff.mp this, simp* at this, exact this }

lemma add_eq : ∀ (n m : ℕ), (⟦n˙⟧ᴴ + ⟦m˙⟧ᴴ : Herbrand T i) = ⟦(n + m)˙⟧ᴴ
| 0     m := by simp[numeral, zero_eq]
| (n+1) m := by { simp[numeral, add_eq n m, (show n + 1 + m = (n + m) + 1, from nat.succ_add n m)],
  simp [Succ_eq, add_succ, add_eq n m] }

lemma mul_eq : ∀ (n m : ℕ), (⟦n˙⟧ᴴ * ⟦m˙⟧ᴴ : Herbrand T i) = ⟦(n * m)˙⟧ᴴ
| 0     m := by { simp, exact mul_zero _ }
| (n+1) m := by { simp[numeral, Succ_eq, mul_eq n m, add_eq,
    show (n + 1) * m = n * m + m, from nat.succ_mul n m ] }

lemma le_iff {h₁ h₂ : Herbrand T i} :
  h₁ ≼ h₂ = ∐(h₁.sf + ⟦#0⟧ᴴ ∥ h₂.sf) :=
by { induction h₁ using fopl.Herbrand.ind_on,
     induction h₂ using fopl.Herbrand.ind_on,
     have : ∀̇ ∀̇ (#0 ≤̇ #1 ↔̇ ∃̇(#1 +̇ #0 =̇ #2)) ∈ T^i := ss_robinson robinson.q8, 
     have := Lindenbaum.provable_iff.mp (((AX this).fal_subst h₂).fal_subst h₁),
     simp at this, exact this }

end robinson

namespace bd_peano
open Herbrand Lindenbaum
open provable
variables {T : theory LA} {i : ℕ} [extend 𝐐 T]

lemma Lindenbaum_induction {p : formula LA} {T : theory LA} (h : T^i ⊢ 𝐈p)
  (zero : (⟦p.rew ₛ[Ż]⟧ᴸ : Lindenbaum T i) = ⊤)
  (succ : (⟦p⟧ᴸ : Lindenbaum T (i+1)) ≤ ⟦p.rew ₑ[Ṡ #0]⟧ᴸ) : ∏(⟦p⟧ᴸ : Lindenbaum T (i+1)) = ⊤ :=
begin
  simp[peano_induction, Lindenbaum.provable_imp_iff, zero] at h,
  have : ⟦p⟧ᴸᶜ ⊔ ⟦(formula.rew ₑ[Ṡ #0] p)⟧ᴸ = (⊤ : Lindenbaum T (i+1)), { simp* },
  simp[this] at h, exact h
end

#check 𝐐+𝐈(hierarchy.sigma_form 1)

theorem collection (p : formula LA) : 𝐐+𝐈𝚺¹1 ⊢ ([∀̇ ≤ #0] ∃̇ p) →̇ ∃̇ [∀̇ ≤ #1] [∃̇ ≤ #1] p :=
begin
  refine deduction.mp _,
  have : ∀ n, ∃ m, (((ₛ[#0] ^ 1) ^ 1) ^ 1) m = (#n : term LA) :=
    (rewriting_sf_perm $ rewriting_sf_perm $ rewriting_sf_perm $ slide_perm #0), 
  rcases formula.total_rew_inv p this with ⟨q, e_q⟩,
  suffices : 𝐐+𝐈(hierarchy.sigma_form 1)+{[∀̇ ≤ #0] ∃̇ p} ⊢ ∀̇ ∀̇ (#0 ≤̇ #1 →̇ ∃̇ [∀̇ ≤ #1] [∃̇ ≤ #1] q),
  { have := (this.fal_subst #0).fal_subst #0, simp[e_q] at this,
    sorry },
  simp[Lindenbaum.provable_top_iff0], apply Lindenbaum_induction,
  { sorry },
  { simp[e_q],
    have : predicate₂ (𝐐^0) *≤ ⟦#0⟧ᴴ c⟪*Z⟫⁰ = ⊥,
    { rw robinson.le_iff, }
       }
end


end bd_peano

end fopl
