import deduction semantics model

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

def AL : language := ⟨langf, langp⟩

@[reducible] def symbol.zero : term AL := vecterm.const *Z
notation `Ż` := symbol.zero

@[reducible] def symbol.succ : term AL → term AL := λ x, vecterm.app *S x
prefix `Ṡ `:max := symbol.succ

@[reducible] def symbol.add : term AL → term AL → term AL := λ x y, vecterm.app *+ (vecterm.cons x y)
infixl ` +̇ `:92 := symbol.add 

@[reducible] def symbol.mult : term AL → term AL → term AL := λ x y, vecterm.app *× (vecterm.cons x y)
infixl ` ×̇ `:94 := symbol.mult

@[reducible] def symbol.le : term AL → term AL → formula AL := λ x y, formula.app *≤ (vecterm.cons x y)
infixl ` ≤̇ `:90 := symbol.le

def symbol.lt (t u : term AL) : formula AL := ¬̇(u ≤̇ t)
infix `<̇`:90 := symbol.lt

def term.pair (u t₁ t₂ : term AL) : formula AL :=
(t₁ <̇ t₂ ⩑ u =̇ t₂ ×̇ t₂ +̇ t₁) ⩒ (t₂ ≤̇ t₁ ⩑ u =̇ t₁ ×̇ t₁ +̇ t₁ +̇ t₂)
notation u` =⟨`t₁`, `t₂`⟩` := term.pair u t₁ t₂

def term.divide (t u : term AL) : formula AL := Ė(t ×̇ #0 =̇ u)
infix `|` := term.divide

def numeral : ℕ → term AL
| 0     := Ż
| (n+1) := Ṡ (numeral n)

local notation n`˙`:1200 := numeral n

lemma numeral_arity0 : ∀ n, (n˙).arity = 0
| 0     := rfl
| (n+1) := by simp[numeral, vecterm.arity, @numeral_arity0 n]
@[elab_as_eliminator] 
lemma AL_ind {C : term AL → Sort*}
  (var  : ∀ n, C(#n))
  (zero : C (Ż))
  (succ : ∀ {t₁}, C t₁ → C (Ṡ t₁))
  (add  : ∀ {t₁ t₂}, C t₁ → C t₂ → C (t₁ +̇ t₂)) 
  (mul  : ∀ {t₁ t₂}, C t₁ → C t₂ → C (t₁ ×̇ t₂)) : ∀ t, C t
| (#n)                                  := var n
| (vecterm.const *Z)                    := zero
| (vecterm.app *S t)                    := succ (AL_ind t)
| (vecterm.app *+ (vecterm.cons t₁ t₂)) := add (AL_ind t₁) (AL_ind t₂)
| (vecterm.app *× (vecterm.cons t₁ t₂)) := mul (AL_ind t₁) (AL_ind t₂)

@[elab_as_eliminator] 
theorem AL_ind_on {C : term AL → Sort*} (t : term AL)
  (var  : ∀ n, C(#n))
  (zero : C (Ż))
  (succ : ∀ {t₁}, C t₁ → C (Ṡ t₁))
  (add  : ∀ {t₁ t₂}, C t₁ → C t₂ → C (t₁ +̇ t₂)) 
  (mul  : ∀ {t₁ t₂}, C t₁ → C t₂ → C (t₁ ×̇ t₂)) : C t :=
AL_ind var zero @succ @add @mul t

def bounded_fal (t : term AL) (p : formula AL) : formula AL := Ȧ(#0 ≤̇ t.sf →̇ p)

notation `[Ȧ`` ≤ `t`]`p := bounded_fal t p

def bounded_ext (t : term AL) (p : formula AL) := Ė(#0 ≤̇ t.sf ⩑ p)

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

@[simp] lemma Q_sentence : theory.sentence 𝐐 := λ p h,
by cases h; simp[sentence, formula.arity, vecterm.arity, formula.iff, formula.ex, formula.and]
  
inductive peano : theory AL
| q   : ∀ {p}, 𝐐 p → peano p
| ind : ∀ (p : formula AL), peano (p.(Ż) →̇ Ȧ(p →̇ (p.ᵉ(Ṡ #0))) →̇ Ȧ p)
notation `𝐏𝐀` := peano

inductive bounded_peano (C : formula AL → Prop) : theory AL
| q   : ∀ {p}, 𝐐 p → bounded_peano p
| ind : ∀ {p : formula AL}, C p → bounded_peano (p.(Ż) →̇ Ȧ(p →̇ (p.ᵉ(Ṡ #0))) →̇ Ȧ p)
prefix `𝐈`:max := bounded_peano

lemma peano_bd_peano : 𝐏𝐀 = 𝐈(λ x, true) :=
by { ext p, split; intros h; induction h with h h h h,
     { exact bounded_peano.q h }, { exact bounded_peano.ind trivial },
     { exact peano.q h }, { exact peano.ind _ } }

lemma Q_bd_peano (C) : 𝐐 ⊆ 𝐈C := λ p h, bounded_peano.q h

lemma bd_peano_subset {C D : set (formula AL)} : C ⊆ D → 𝐈C ⊆ 𝐈D := λ h p hyp_p,
by { cases hyp_p with _ hyp_p p hyp_p2,
     exact bounded_peano.q hyp_p, refine bounded_peano.ind (h hyp_p2) }

namespace hierarchy

mutual inductive sigma_form, pie_form
with sigma_form : ℕ → formula AL → Prop
| op : ∀ {p : formula AL}, p.Open → sigma_form 0 p
| bd_fal : ∀ {p} {n t}, sigma_form n p → sigma_form n [Ȧ ≤ t]p
| bd_ext : ∀ {p} {n t}, sigma_form n p → sigma_form n [Ė ≤ t]p
| qt : ∀ {p} {n}, pie_form n p → sigma_form (n+1) Ėp 
with pie_form : ℕ → formula AL → Prop
| op : ∀ {p : formula AL}, p.Open → pie_form 0 p
| bd_fal : ∀ {p} {n t}, pie_form n p → pie_form n [Ȧ ≤ t]p
| bd_ext : ∀ {p} {n t}, pie_form n p → pie_form n [Ė ≤ t]p
| qt : ∀ {p} {n}, sigma_form n p → pie_form (n+1) Ȧp 

def sigma (T : theory AL) (n : ℕ) : set (formula AL) := {p | ∃ q, sigma_form n q ∧ T ⊢̇ q ↔̇ p}
def pie (T : theory AL) (n : ℕ) : set (formula AL) := {p | ∃ q, pie_form n q ∧ T ⊢̇ q ↔̇ p}
def delta (T : theory AL) (n : ℕ) : set (formula AL) :=
{p | ∃ q₁ q₂, T ⊢̇ q₁ ↔̇ p ∧ T ⊢̇ q₂ ↔̇ p ∧ q₁ ∈ sigma T n ∧ q₂ ∈ pie T n}

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

lemma apply_nat_pr (p : AL.pr 2) (a : ℕ) (v : dvector ℕ 1) :
  nat_pr 2 p (a :: v) = nat_pr 2 p (a :: v.head :: dvector.nil) := by simp[dvector.head_tail]

lemma apply_nat_fn (f : AL.fn 2) (a : ℕ) (v : dvector ℕ 1) :
  nat_fn 2 f (a :: v) = nat_fn 2 f (a :: v.head :: dvector.nil) := by simp[dvector.head_tail]

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

lemma N_models_bd_PA (C : formula AL → Prop) : 𝒩 ⊧ₜₕ 𝐈C := λ p hyp_p e,
by { cases hyp_p with _ hyp_p p,
     exact N_models_Q p hyp_p e,
       simp[formula.subst₁, formula.subst₁_e, rew_val_iff],
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

namespace robinson
open Herbrand Lindenbaum

open provable

@[simp] lemma add_zero (h : Herbrand 𝐐) : function₂ 𝐐 *+ (function₀ 𝐐 *Z) h = h :=
by { induction h using fopl.Herbrand.ind_on,
     have := Herbrand.provable_iff.mp ((AX robinson.q4).subst₁ h),
     simp[formula.subst₁, formula.rew, vecterm.rew, Herbrand.of_eq_of] at this ⊢, exact this }

@[simp] lemma add_succ (h₁ h₂ : Herbrand 𝐐) :
  (function₂ 𝐐 *+) ((function₁ 𝐐 *S) h₁) h₂ = (function₁ 𝐐 *S) ((function₂ 𝐐 *+) h₁ h₂) :=
by { induction h₁ using fopl.Herbrand.ind_on, induction h₂ using fopl.Herbrand.ind_on,
     have := Herbrand.provable_iff.mp (((AX robinson.q5).subst₁ h₂).subst₁ h₁),
     simp[formula.subst₁, formula.rew, vecterm.rew, Herbrand.of_eq_of] at this ⊢, exact this }

lemma add_eq : ∀ (n m : ℕ), (function₂ 𝐐 *+) ⟦n˙⟧ᴴ ⟦m˙⟧ᴴ = ⟦(n + m)˙⟧ᴴ
| 0     m := by simp[numeral]
| (n+1) m := by simp[numeral, add_eq n m, (show n + 1 + m = (n + m) + 1, from nat.succ_add n m)]

lemma mul_eq : ∀ {n m : ℕ}, (function₂ 𝐐 *×) ⟦n˙⟧ᴴ ⟦m˙⟧ᴴ = ⟦(n * m)˙⟧ᴴ
| 0     m :=
  by { have := Herbrand.provable_iff.mp ((AX robinson.q6).subst₁ (m˙)),
    simp[formula.subst₁, formula.rew, vecterm.rew, Herbrand.of_eq_of] at this ⊢, refine this }
| (n+1) m := by { simp[numeral],
  have q7 := Herbrand.provable_iff.mp (((AX robinson.q7).subst₁ (m˙)).subst₁ (n˙)),
  have IH := @mul_eq n m,  
  simp[formula.subst₁, formula.rew, vecterm.rew] at q7 IH ⊢,
  rw (show (n + 1) * m = n * m + m, from nat.succ_mul n m), simp[←add_eq],
  rw ← IH, exact q7 }

lemma le_prove {n m : ℕ} (eqn : n ≤ m) : 𝐐 ⊢̇ n˙ ≤̇ m˙ :=
begin
  refine Lindenbaum.provable_top_iff.mpr _,
  have q8 : predicate₂ 𝐐 *≤ ⟦n˙⟧ᴴ ⟦m˙⟧ᴴ = ∐(function₂ ⇑𝐐 *+ ⟦n˙⟧ᴴ ⟦#0⟧ᴴ ∥ ⟦m˙⟧ᴴ),
  { have := Lindenbaum.provable_iff.mp (((AX robinson.q8).subst₁ (m˙)).subst₁ (n˙)),
    simp[formula.rew, vecterm.rew, numeral_arity0] at this ⊢, exact this },
  simp[formula.rew, vecterm.rew, numeral_arity0],
  have exist : ⟦(m - n)˙⟧ᴴ ⊳ (function₂ ⇑𝐐 *+ ⟦n˙⟧ᴴ ⟦#0⟧ᴴ ∥ ⟦m˙⟧ᴴ) = ⊤,
  { have : (function₂ ⇑𝐐 *+) ⟦n˙⟧ᴴ ⟦#0⟧ᴴ ∥ ⟦m˙⟧ᴴ = ⟦n˙ +̇ #0 =̇ m˙⟧ᴸ := rfl,
    rw this, simp[fopl.Lindenbaum.subst₁, fopl.Lindenbaum.subst₁_aux, -provable_equal_eq,
      formula.subst₁, formula.rew, vecterm.rew, numeral_arity0], simp,
      rw[to_Herbrand], simp[add_eq],
      have : ⟦(n + (m - n))˙⟧ᴴ = ⟦m˙⟧ᴴ, simp[(show n + (m - n) = m, from nat.add_sub_of_le eqn)],
      refine this },
  have : ⟦(m - n)˙⟧ᴴ ⊳ (function₂ ⇑𝐐 *+ ⟦n˙⟧ᴴ ⟦#0⟧ᴴ ∥ ⟦m˙⟧ᴴ) ≤ ∐(function₂ ⇑𝐐 *+ ⟦n˙⟧ᴴ ⟦#0⟧ᴴ ∥ ⟦m˙⟧ᴴ),
  from subst₁_le_ex _ _,
  simp[exist] at this, simp[q8], exact this,
end

lemma eq_prove {n m : ℕ} (eqn : n = m) : 𝐐 ⊢̇ n˙ =̇ m˙ :=
by refine Lindenbaum.provable_top_iff.mpr _; simp[to_Herbrand, eqn]

lemma add_inj : ∀ (n : ℕ) (t₁ t₂), 𝐐 ⊢̇ n˙ +̇ t₁ =̇ n˙ +̇ t₂ →̇ t₁ =̇ t₂
| 0     t₁ t₂ := Lindenbaum.provable_imp_iff.mpr (by simp[numeral])
| (n+1) t₁ t₂ := by { apply Lindenbaum.provable_imp_iff.mpr, simp,
  have q2 := Lindenbaum.provable_imp_iff.mp (((AX robinson.q2).subst₁ (n˙ +̇ t₂)).subst₁ (n˙ +̇ t₁)),
  have IH := Lindenbaum.provable_imp_iff.mp (add_inj n t₁ t₂), 
  simp[formula.rew, vecterm.rew, numeral_arity0, numeral] at q2 IH ⊢,
  exact le_trans q2 IH }

lemma neq_prove : ∀ {n m : ℕ}, n ≠ m → 𝐐 ⊢̇ n˙ ≠̇ m˙ :=
begin
  suffices : ∀ n m, 𝐐 ⊢̇ n˙ ≠̇ (n + (m + 1))˙,
  { intros n m eqn, have C : n < m ∨ m < n, exact ne.lt_or_lt eqn,
    cases C,
    { have : 𝐐 ⊢̇ n˙ ≠̇ (n + (m - n - 1 + 1))˙, from this n (m - n - 1),
      simp[(show n + (m - n - 1 + 1) = m, by omega), this] at this, exact this },
    { have : 𝐐 ⊢̇ m˙ ≠̇ (m + (n - m - 1 + 1))˙, from this m (n - m - 1),
      simp[(show m + (n - m - 1 + 1) = n, by omega), this] at this,
      have := provable_neg_iff.mp this,
      refine provable_neg_iff.mpr _,
      simp at this ⊢, simp[←this], refine Lindenbaum.eq_symm _ _ } },
  have lmm₁ : ∀ n, 𝐐 ⊢̇ Ż ≠̇ (n + 1)˙, 
  { intros n, exact ((AX robinson.q1).subst₁ (n˙)) },
  intros n m,
  have : 𝐐 ⊢̇ Ż ≠̇ (m + 1)˙ →̇ n˙ +̇ Ż ≠̇ n˙ +̇ (m + 1)˙, from contrapose.mpr (add_inj n Ż (m + 1)˙), 
  have : 𝐐 ⊢̇ n˙ +̇ 0˙ ≠̇ n˙ +̇ (m + 1)˙, from this.MP (lmm₁ _),
  have := provable_neg_iff.mp this,
  refine provable_neg_iff.mpr _, simp[add_eq] at this ⊢, refine this
end

lemma nle_prove : ∀ {n m : ℕ}, ¬(n ≤ m) → 𝐐 ⊢̇ ¬̇(n˙ ≤̇ m˙) :=
begin
  suffices : ∀ n m, 𝐐 ⊢̇ ¬̇((m + 1 + n)˙ ≤̇ n˙),
  { intros n m eqn, have := this m (n - m - 1),
    simp[show n - m - 1 + 1 + m = n, by omega] at this, exact this },
  have q8 : ∀ n m,
    predicate₂ 𝐐 *≤ ⟦n˙⟧ᴴ ⟦m˙⟧ᴴ = ∐(function₂ ⇑𝐐 *+ ⟦n˙⟧ᴴ ⟦#0⟧ᴴ ∥ ⟦m˙⟧ᴴ),
  { intros n m, have := Lindenbaum.provable_iff.mp (((AX robinson.q8).subst₁ (m˙)).subst₁ (n˙)),
    simp[formula.rew, vecterm.rew, numeral_arity0] at this ⊢, exact this },
  have q2 : ∀ {n m}, 
  function₁ 𝐐 *S (function₂ 𝐐 *+ ⟦(m + 1 + n)˙⟧ᴴ ⟦#0⟧ᴴ) ∥ function₁ 𝐐 *S ⟦n˙⟧ᴴ ≤ function₂ 𝐐 *+ ⟦(m + 1 + n)˙⟧ᴴ ⟦#0⟧ᴴ ∥ ⟦n˙⟧ᴴ,
  { intros n m, have := ((AX robinson.q2).subst₁ n˙).subst₁ ((m + 1 + n)˙ +̇ #0),
    simp[formula.rew, vecterm.rew, numeral_arity0, formula.subst₁, formula.rew, vecterm.rew,
    Lindenbaum.provable_imp_iff] at this, exact this },
  suffices : ∀ (n m : ℕ), 𝐐 ⊢̇ Ȧ¬̇((m + 1 + n)˙ +̇ #0 =̇ n˙),
  { intros n m, have := this n m, simp [provable_top_iff] at this ⊢, simp[q8],
    rw [←compl_inj_iff, prenex_ex_quantifir_neg], simp[this] },
  intros n, induction n with n IH; intros m,
  { apply GE, have := (AX robinson.q1).subst₁ (m˙ +̇ #0),
    simp[numeral, theory_sentence_eq, provable_neg_iff, formula.subst₁, formula.rew, vecterm.rew] at this ⊢, 
    rw Lindenbaum.eq_symm, exact this },
  { apply GE, have IH' := (IH m).subst₁ (#0),
    have : m + 1 + n.succ = (m + 1 + n) + 1, from (m + 1).add_succ n, simp[this, numeral],
    simp[numeral, theory_sentence_eq, provable_neg_iff,
      formula.subst₁, formula.rew, vecterm.rew, numeral_arity0, numeral] at IH' ⊢,
    exact eq_bot_mono q2 IH' }
end

lemma arity0_term_val {t : term AL} : t.arity = 0 → ∀ e : ℕ → |𝒩|, ⟦t⟧ᴴ.𝐐 = ⟦(t.val e)˙⟧ᴴ :=
begin
  induction t using fopl.AL_ind; simp[term.val, vecterm.arity],
  case zero { simp[numeral] },
  case succ : t₁ IH
  { intros h e, rw[←dvector.head_tail (vecterm.val e t₁)],
    simp[-dvector.head_tail, IH h e, numeral] },
  case add : t₁ t₂ IH₁ IH₂
  { intros h₁ h₂ e, rw[←dvector.head_tail (vecterm.val e t₂)],
    simp[-dvector.head_tail, IH₁ h₁ e, IH₂ h₂ e, add_eq] },
  case mul : t₁ t₂ IH₁ IH₂
  { intros h₁ h₂ e, rw[←dvector.head_tail (vecterm.val e t₂)],
    simp[-dvector.head_tail, IH₁ h₁ e, IH₂ h₂ e, mul_eq] }
end

lemma open_complete {p : formula AL} :
  sentence p → p.Open → 𝒩 ⊧ p → 𝐐 ⊢̇ p :=
begin
  suffices : sentence p → p.Open = tt → ∀ e, (𝒩 ⊧[e] p → 𝐐 ⊢̇ p) ∧ (¬𝒩 ⊧[e] p → 𝐐 ⊢̇ ¬̇p),
 { intros a o h, exact (this a o (default _)).1 ((eval_sentence_iff a).mpr h) },
  induction p; simp[sentence, formula.arity, vecterm.val],
  case fopl.formula.const :  { cases p },
  case fopl.formula.app : n p v
  { cases p, cases v with _ t₁ t₂, intros a e,
    simp[models, sentence, formula.arity, vecterm.arity, formula.val] at a ⊢,
    rw[←dvector.head_tail (vecterm.val e t₂)], simp,
    have eqn₁ : ⟦t₁⟧ᴴ = ⟦(t₁.val e).head˙⟧ᴴ, from arity0_term_val a.1 e,
    have eqn₂ : ⟦t₂⟧ᴴ = ⟦(t₂.val e).head˙⟧ᴴ, from arity0_term_val a.2 e,         
    refine ⟨λ h, _, λ h, _⟩,
    { have lmm₁ : predicate₂ 𝐐 *≤ ⟦(t₁.val e).head˙⟧ᴴ ⟦(t₂.val e).head˙⟧ᴴ = ⊤,
      { refine Lindenbaum.provable_top_iff.mp (le_prove h), },
      simp[Lindenbaum.provable_top_iff, eqn₁, eqn₂, lmm₁] },
    { have lmm₁ : 𝐐 ⊢̇ ¬̇((t₁.val e).head˙ ≤̇ (t₂.val e).head˙), refine nle_prove (by simp[h]),
      simp[Lindenbaum.provable_top_iff, eqn₁, eqn₂] at lmm₁ ⊢, exact lmm₁ } },
  case fopl.formula.equal : t₁ t₂
  { intros a₁ a₂ e,
    have eqn₁ : ⟦t₁⟧ᴴ = ⟦(t₁.val e)˙⟧ᴴ, from arity0_term_val a₁ e,
    have eqn₂ : ⟦t₂⟧ᴴ = ⟦(t₂.val e)˙⟧ᴴ, from arity0_term_val a₂ e,
    rw[←dvector.head_tail (vecterm.val e t₁), ←dvector.head_tail (vecterm.val e t₂)],
    simp[dvector.dvector1_tail], refine ⟨λ h, _, λ h, _⟩,
    { simp[Lindenbaum.provable_top_iff, eqn₁, eqn₂], rw h, simp },
    { have : 𝐐 ⊢̇ (t₁.val e)˙ ≠̇ (t₂.val e)˙, { refine neq_prove _, simp, exact h },
      simp[Lindenbaum.provable_top_iff, eqn₁, eqn₂] at this ⊢, exact this } },
  case fopl.formula.imply : p₁ p₂ IH₁ IH₂
  { intros a₁ a₂ o₁ o₂ e,
    have IH₁ := IH₁ a₁ o₁ e,
    have IH₂ := IH₂ a₂ o₂ e,
    by_cases C₁ : p₁.val e; by_cases C₂ : p₂.val e,
    { refine ⟨λ h₁, _, λ h₁ h₂, _⟩,
      { have := IH₂.1 C₂, simp[this] }, { contradiction } },
    { refine ⟨λ h₁, _, λ h₁ h₂, _⟩,
      { have := h₁ C₁, contradiction }, { refine ⟨IH₁.1 C₁, IH₂.2 C₂⟩ } },
    { refine ⟨λ h₁, _, λ h₁ h₂, _⟩,
      { have := IH₂.1 C₂, simp[this] }, { contradiction } },
    { refine ⟨λ h₁, _, λ h₁ h₂, _⟩,
      { have := IH₁.2 C₁, apply contrapose.mp, simp[this] },
      { contradiction } } },
  case fopl.formula.neg : p IH
  { intros a o e,
    have IH := IH a o e, refine ⟨IH.2, IH.1⟩ }
end

lemma sigma1_complete {p : formula AL} :
  sentence p → hierarchy.sigma_form 1 p → 𝒩 ⊧ p → 𝐐 ⊢̇ p := λ a H,
begin
  induction H
  

end

lemma pair_total : 𝐐 ⊢̇ ȦȦĖ(#0 =⟨#1, #2⟩) :=
begin
  refine provable.GE (provable.GE _),
  simp,
end


end robinson

end fopl
