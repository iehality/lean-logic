import deduction semantics

namespace fopl

inductive langf : ℕ → Type
| zero : langf 0
| succ : langf 1
| add  : langf 2
| mult : langf 2

inductive langp : ℕ → Type
| le : langp 2

def AL : language := ⟨langf, langp⟩

@[reducible] def symbol.zero : term AL := vecterm.const langf.zero

notation `Ż` := symbol.zero

@[reducible] def symbol.succ : term AL → term AL := λ x, vecterm.app langf.succ x

prefix `Ṡ `:max := symbol.succ

@[reducible] def symbol.add : term AL → term AL → term AL := λ x y, vecterm.app langf.add (vecterm.cons x y)

infixl ` +̇ `:92 := symbol.add 

@[reducible] def symbol.mult : term AL → term AL → term AL := λ x y, vecterm.app langf.mult (vecterm.cons x y)

infixl ` ×̇ `:94 := symbol.mult

@[reducible] def symbol.le : term AL → term AL → form AL := λ x y, form.app langp.le (vecterm.cons x y)

infixl ` ≤̇ `:90 := symbol.le

def numeral : ℕ → term AL
| 0     := Ż
| (n+1) := Ṡ (numeral n)

local notation n`˙`:max := numeral n

def bounded_fal (t : term AL) (p : form AL) : form AL := Ȧ(#0 ≤̇ t.sf →̇ p)

notation `[Ȧ`` ≤ `t`]`p := bounded_fal t p

def bounded_ext (t : term AL) (p : form AL) := Ė(#0 ≤̇ t.sf ⩑ p)

notation `[Ė`` ≤ `t`]`p := bounded_ext t p

#check [Ė ≤ #2][Ȧ ≤ #3]Ė[Ȧ ≤ #3](#1 ≤̇ #2)

inductive robinson : theory AL
| q1 : robinson Ȧ(Ż ≠̇ Ṡ #0)
| q2 : robinson ȦȦ(Ṡ #0 =̇ Ṡ #1 →̇ #0 =̇ #1)
| q3 : robinson Ȧ(#0 ≠̇ Ż →̇ Ė(#1 =̇ Ṡ #0))
| q4 : robinson Ȧ(Ż +̇ #0 =̇ #0)
| q5 : robinson ȦȦ(Ṡ #0 +̇ #1 =̇ Ṡ(#0 +̇ #1))
| q6 : robinson Ȧ(Ż ×̇ #0 =̇ Ż)
| q7 : robinson ȦȦ(Ṡ #0 ×̇ #1 =̇ #0 ×̇ #1 +̇ #1)
| q8 : robinson ȦȦ(#0 ≤̇ #1 ↔̇ Ė(#1 +̇ #0 =̇ #2))
notation `𝐐` := robinson
  
inductive peano : theory AL
| q   : ∀ {p}, 𝐐 p → peano p
| ind : ∀ (p : form AL), peano (p.(Ż) →̇ Ȧ(p →̇ (p.ᵉ(Ṡ #0))) →̇ Ȧ p)
notation `𝐏𝐀` := peano

inductive bounded_peano (C : form AL → Prop) : theory AL
| q   : ∀ {p}, 𝐐 p → bounded_peano p
| ind : ∀ {p : form AL}, C p → bounded_peano (p.(Ż) →̇ Ȧ(p →̇ (p.ᵉ(Ṡ #0))) →̇ Ȧ p)
prefix `𝐈`:max := bounded_peano

lemma peano_bd_peano : 𝐏𝐀 = 𝐈(λ x, true) :=
by { ext p, split; intros h; induction h with h h h h,
     { exact bounded_peano.q h }, { exact bounded_peano.ind trivial },
     { exact peano.q h }, { exact peano.ind _ } }

lemma Q_bd_peano (C) : 𝐐 ⊆ 𝐈C := λ p h, bounded_peano.q h

lemma bd_peano_subset {C D : set (form AL)} : C ⊆ D → 𝐈C ⊆ 𝐈D := λ h p hyp_p,
by { cases hyp_p with _ hyp_p p hyp_p2,
     exact bounded_peano.q hyp_p, refine bounded_peano.ind (h hyp_p2) }

namespace hierarchy

mutual inductive sigma, pie
with sigma : ℕ → form AL → Prop
| op : ∀ {p : form AL}, p.op → sigma 0 p
| bd_fal : ∀ {p} {n t}, sigma n p → sigma n [Ȧ ≤ t]p
| bd_ext : ∀ {p} {n t}, sigma n p → sigma n [Ė ≤ t]p
| qt : ∀ {p} {n}, pie n p → sigma (n+1) Ėp 
with pie : ℕ → form AL → Prop
| op : ∀ {p : form AL}, p.op → pie 0 p
| bd_fal : ∀ {p} {n t}, pie n p → pie n [Ȧ ≤ t]p
| bd_ext : ∀ {p} {n t}, pie n p → pie n [Ė ≤ t]p
| qt : ∀ {p} {n}, sigma n p → pie (n+1) Ȧp 

end hierarchy

@[simp] def nat_fn : ∀ n, AL.fn n → dvector ℕ n → ℕ
| 0 langf.zero nil             := 0
| 1 langf.succ (n :: nil)      := n + 1
| 2 langf.add  (n :: m :: nil) := n + m
| 2 langf.mult (n :: m :: nil) := n * m

@[simp] def nat_pr : ∀ n, AL.pr n → dvector ℕ n → Prop
| 2 langp.le  (n :: m :: nil) := n ≤ m

def Num : model AL := ⟨ℕ, 0, nat_fn, nat_pr⟩
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
  { exact λ n m, nat.succ_add m n },
  { exact λ n m, nat.succ_mul m n },
  { intros n m, split; intros h,
    refine ⟨(n - m : ℕ), nat.add_sub_of_le h⟩,
    rcases h with ⟨_, h⟩, exact nat.le.intro h }
end

theorem Q_consistent : theory.consistent 𝐐 := model_consistent N_models_Q

lemma N_models_bd_PA (C : form AL → Prop) : 𝒩 ⊧ₜₕ 𝐈C := λ p hyp_p e,
by { cases hyp_p with _ hyp_p p,
     exact N_models_Q p hyp_p e,
       simp[form.subst₁, form.subst₁_e, rew_val_iff],
  intros h0 hIH n,
  induction n with n IH,
  { have : (λ n, (vecterm.val e (Ż ^ˢ vecterm.var $ n)).head) = ((0 : ℕ) ^ˢ e),
    { funext n, cases n; simp[slide] },
    simp[this] at h0, exact h0 },
  { have hIH' := hIH n IH,
    have : (λ m, (vecterm.val (n ^ˢ e : ℕ → Num.dom) (Ṡ #0 ^ᵉ vecterm.var $ m)).head) = (n+1 : ℕ) ^ˢ e,
    { funext n, cases n; simp[slide, embed] },
    simp[this] at hIH', exact hIH' } }

theorem bd_PA_consistent (C) : theory.consistent 𝐈C := model_consistent (N_models_bd_PA C)

lemma N_models_PA : 𝒩 ⊧ₜₕ 𝐏𝐀 :=
by {rw peano_bd_peano, exact N_models_bd_PA _}

theorem PA_consistent : theory.consistent 𝐏𝐀 := model_consistent N_models_PA

def true_arithmetic : theory AL := {p | 𝒩 ⊧ p}
notation `𝐓𝐀` := true_arithmetic

lemma N_models_TA : 𝒩 ⊧ₜₕ 𝐓𝐀 := λ p hyp_p e, hyp_p e

theorem TA_consistent : theory.consistent 𝐓𝐀 := model_consistent N_models_TA

end fopl
