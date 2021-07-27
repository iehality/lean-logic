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

@[reducible] def symbol.add : term LA → term LA → term LA := λ x y, vecterm.app *+ (vecterm.cons x y)
infixl ` +̇ `:92 := symbol.add 

@[reducible] def symbol.mult : term LA → term LA → term LA := λ x y, vecterm.app *× (vecterm.cons x y)
infixl ` ×̇ `:94 := symbol.mult

@[reducible] def symbol.le : term LA → term LA → formula LA := λ x y, formula.app *≤ (vecterm.cons x y)
infixl ` ≤̇ `:90 := symbol.le

def symbol.lt (t u : term LA) : formula LA := ¬̇(u ≤̇ t)
infix `<̇`:90 := symbol.lt

def term.pair (u t₁ t₂ : term LA) : formula LA :=
(t₁ <̇ t₂ ⩑ u =̇ t₂ ×̇ t₂ +̇ t₁) ⩒ (t₂ ≤̇ t₁ ⩑ u =̇ t₁ ×̇ t₁ +̇ t₁ +̇ t₂)
notation u` =⟨`t₁`, `t₂`⟩` := term.pair u t₁ t₂

def term.divide (t u : term LA) : formula LA := ∃̇(t ×̇ #0 =̇ u)
infix `|` := term.divide

instance (T : theory LA) : has_zero (Herbrand T) := ⟨Herbrand.function₀ T *Z⟩
instance (T : theory LA) : has_add (Herbrand T) := ⟨Herbrand.function₂ T *+⟩
instance (T : theory LA) : has_mul (Herbrand T) := ⟨Herbrand.function₂ T *×⟩

variables (s : ℕ → term LA)
#reduce (nfal (#0 +̇ #2 =̇ #9) 9).rew (λ x, #(x+8))
#reduce (nfal (#0 +̇ #2 =̇ #19 +̇ #12) 2).rew s 

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

@[simp] lemma bounded_fal_rew (t : term LA) (p : formula LA) (s) : ([∀̇ ≤ t]p).rew s = [∀̇ ≤ t.rew s](p.rew s⁺¹) :=
by simp[bounded_fal, vecterm.sf, vecterm.nested_rew]

@[simp] lemma bounded_ex_rew (t : term LA) (p : formula LA) (s) : ([∃̇ ≤ t]p).rew s = [∃̇ ≤ t.rew s](p.rew s⁺¹) :=
by simp[bounded_ext, vecterm.sf, vecterm.nested_rew]

inductive robinson : theory LA
| q1 : robinson ∀̇(Ż ≠̇ Ṡ #0)
| q2 : robinson ∀̇∀̇(Ṡ #0 =̇ Ṡ #1 →̇ #0 =̇ #1)
| q3 : robinson ∀̇(#0 ≠̇ Ż →̇ ∃̇(#1 =̇ Ṡ #0))
| q4 : robinson ∀̇(Ż +̇ #0 =̇ #0)
| q5 : robinson ∀̇∀̇(Ṡ #0 +̇ #1 =̇ Ṡ(#0 +̇ #1))
| q6 : robinson ∀̇(Ż ×̇ #0 =̇ Ż)
| q7 : robinson ∀̇∀̇(Ṡ #0 ×̇ #1 =̇ #0 ×̇ #1 +̇ #1)
| q8 : robinson ∀̇∀̇(#0 ≤̇ #1 ↔̇ ∃̇(#1 +̇ #0 =̇ #2))
notation `𝐐` := robinson

def peano_induction (p : formula LA) : formula LA := p.rew ₛ[Ż] ⩑ ∀̇(p →̇ p.rew ₑ[Ṡ #0]) →̇ ∀̇ p
prefix `𝐈`:max := peano_induction

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
         have : (p.rew ₛ[Ż]).rew s = (p.rew s⁺¹).rew ₛ[Ż],
         { simp[formula.nested_rew], congr, ext x, cases x; simp }, simp[this],
         have : (p.rew ₑ[Ṡ #0]).rew s⁺¹ = (p.rew s⁺¹).rew ₑ[Ṡ #0],
         { simp[formula.nested_rew], congr, ext x, cases x; simp }, simp[this],
         have : p.rew s⁺¹ ∈ C, from proper.proper0 hyp,
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

def sigma (T : theory LA) (n : ℕ) : set (formula LA) := {p | ∃ q, sigma_form n q ∧ T ⊢̇ q ↔̇ p}
def pie (T : theory LA) (n : ℕ) : set (formula LA) := {p | ∃ q, pie_form n q ∧ T ⊢̇ q ↔̇ p}
def delta (T : theory LA) (n : ℕ) : set (formula LA) :=
{p | ∃ q₁ q₂, T ⊢̇ q₁ ↔̇ p ∧ T ⊢̇ q₂ ↔̇ p ∧ q₁ ∈ sigma T n ∧ q₂ ∈ pie T n}

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
  nat_pr 2 p (a :: v) = nat_pr 2 p (a :: v.head :: dvector.nil) := by simp[dvector.head_tail]

lemma apply_nat_fn (f : LA.fn 2) (a : ℕ) (v : dvector ℕ 1) :
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

open provable

@[simp] lemma add_zero (h : Herbrand (𝐐^0)) : function₂ (𝐐^0) *+ c[*Z] h = h :=
by { induction h using fopl.Herbrand.ind_on,
     have := Herbrand.provable_iff.mp ((AX robinson.q4).fal_subst h), simp* at *,
     exact this }

@[simp] lemma add_succ (h₁ h₂ : Herbrand (𝐐^0)) :
  (function₂ (𝐐^0) *+) ((function₁ (𝐐^0) *S) h₁) h₂ = (function₁ _ *S) ((function₂ _ *+) h₁ h₂) :=
by { induction h₁ using fopl.Herbrand.ind_on, induction h₂ using fopl.Herbrand.ind_on,
     have := Herbrand.provable_iff.mp (((AX robinson.q5).fal_subst h₂).fal_subst h₁),
     simp* at*, exact this }

lemma add_eq : ∀ (n m : ℕ), (⟦n˙⟧ᴴ f²[*+] ⟦m˙⟧ᴴ : Herbrand (𝐐^0)) = ⟦(n + m)˙⟧ᴴ
| 0     m := by simp[numeral]
| (n+1) m := by simp[numeral, add_eq n m, (show n + 1 + m = (n + m) + 1, from nat.succ_add n m)]

lemma mul_eq : ∀ {n m : ℕ}, (⟦n˙⟧ᴴ f²[*×] ⟦m˙⟧ᴴ : Herbrand (𝐐^0)) = ⟦(n * m)˙⟧ᴴ
| 0     m :=
  by { have := Herbrand.provable_iff.mp ((AX robinson.q6).fal_subst (m˙)),
       simp at this ⊢, exact this }
| (n+1) m := by { simp[numeral],
  have q7 := Herbrand.provable_iff.mp (((AX robinson.q7).fal_subst (m˙)).fal_subst (n˙)),
  have IH := @mul_eq n m, simp at q7 IH ⊢,
  rw (show (n + 1) * m = n * m + m, from nat.succ_mul n m), simp[←add_eq],
  rw ← IH, exact q7 }

lemma le_prove {n m : ℕ} (eqn : n ≤ m) : 𝐐 ⊢̇ n˙ ≤̇ m˙ :=
begin
  refine Lindenbaum.provable_top_iff.mpr _,
  have q8 : predicate₂ (𝐐^0) *≤ ⟦n˙⟧ᴴ ⟦m˙⟧ᴴ = ∐(function₂ _ *+ ⟦n˙⟧ᴴ ⟦#0⟧ᴴ ∥ ⟦m˙⟧ᴴ),
  { have := Lindenbaum.provable_iff.mp (((AX robinson.q8).fal_subst (m˙)).fal_subst (n˙)),
    simp[numeral_arity0] at this ⊢, exact this },
  simp[formula.rew, vecterm.rew, numeral_arity0],
  have exist : ⟦(m - n)˙⟧ᴴ ⊳[0] (function₂ (𝐐^1) *+ ⟦n˙⟧ᴴ ⟦#0⟧ᴴ ∥ ⟦m˙⟧ᴴ) = ⊤,
  { simp[numeral_arity0, add_eq, to_Herbrand],
    have : n + (m - n) = m, exact nat.add_sub_of_le eqn, simp[this] },
  have : ⟦(m - n)˙⟧ᴴ ⊳[0] (function₂ (𝐐^1) *+ ⟦n˙⟧ᴴ ⟦#0⟧ᴴ ∥ ⟦m˙⟧ᴴ) ≤ ∐(function₂ _ *+ ⟦n˙⟧ᴴ ⟦#0⟧ᴴ ∥ ⟦m˙⟧ᴴ),
  from proper.subst_sf_L_le_ex _ _,
  simp[exist] at this, simp[q8], exact this,
end

lemma eq_prove {n m : ℕ} (eqn : n = m) : 𝐐 ⊢̇ n˙ =̇ m˙ :=
by refine Lindenbaum.provable_top_iff.mpr _; simp[to_Herbrand, eqn]

lemma add_inj : ∀ (n : ℕ) (t₁ t₂), 𝐐 ⊢̇ n˙ +̇ t₁ =̇ n˙ +̇ t₂ →̇ t₁ =̇ t₂
| 0     t₁ t₂ := Lindenbaum.provable_imp_iff.mpr (by simp[numeral])
| (n+1) t₁ t₂ := by { apply Lindenbaum.provable_imp_iff.mpr, simp,
  have q2 := Lindenbaum.provable_imp_iff.mp (((AX robinson.q2).fal_subst (n˙ +̇ t₂)).fal_subst (n˙ +̇ t₁)),
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
  { intros n, exact ((AX robinson.q1).fal_subst (n˙)) },
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
    predicate₂ (𝐐^0) *≤ ⟦n˙⟧ᴴ ⟦m˙⟧ᴴ = ∐(function₂ _ *+ ⟦n˙⟧ᴴ ⟦#0⟧ᴴ ∥ ⟦m˙⟧ᴴ),
  { intros n m, have := Lindenbaum.provable_iff.mp (((AX robinson.q8).fal_subst (m˙)).fal_subst (n˙)),
    simp[numeral_arity0] at this ⊢, exact this },
  have q2 : ∀ {n m}, 
    function₁ (𝐐^0) *S (function₂ _ *+ ⟦(m + 1 + n)˙⟧ᴴ ⟦#0⟧ᴴ) ∥ function₁ (𝐐^0) *S ⟦n˙⟧ᴴ ≤
    function₂ (𝐐^0) *+ ⟦(m + 1 + n)˙⟧ᴴ ⟦#0⟧ᴴ ∥ ⟦n˙⟧ᴴ,
  { intros n m, have := ((AX robinson.q2).fal_subst n˙).fal_subst ((m + 1 + n)˙ +̇ #0),
    simp[numeral_arity0, Lindenbaum.provable_imp_iff] at this, exact this },
  suffices : ∀ (n m : ℕ), 𝐐 ⊢̇ ∀̇¬̇((m + 1 + n)˙ +̇ #0 =̇ n˙),
  { intros n m, have := this n m, simp [provable_top_iff] at this ⊢, simp[q8],
    rw [←compl_inj_iff, prenex_ex_neg], simp[this] },
  intros n, induction n with n IH; intros m,
  { apply GE, have := (AX robinson.q1).fal_subst (m˙ +̇ #0),
    simp[numeral, provable_neg_iff] at this ⊢, 
    rw Lindenbaum.eq_symm, exact this },
  { apply GE, have IH' := (IH m).fal_subst (#0),
    have : m + 1 + n.succ = (m + 1 + n) + 1, from (m + 1).add_succ n, simp[this, numeral],
    simp[numeral, provable_neg_iff, numeral_arity0] at IH' ⊢,
    exact eq_bot_mono q2 IH' }
end

lemma arity0_term_val {t : term LA} :
  t.arity = 0 → ∀ e : ℕ → |𝒩|, (⟦t⟧ᴴ : Herbrand (𝐐^0)) = ⟦(t.val e)˙⟧ᴴ :=
begin
  induction t using fopl.LA_ind; simp[term.val, vecterm.arity],
  case zero { simp[numeral] },
  case succ : t₁ IH
  { intros h e, rw[←dvector.head_tail (vecterm.val e t₁)],
    simp[-dvector.head_tail, IH h e, numeral] },
  case add : t₁ t₂ IH₁ IH₂
  { intros h₁ h₂ e, rw[←dvector.head_tail (vecterm.val e t₂)],
    simp[-dvector.head_tail, IH₁ h₁ e, IH₂ h₂ e, add_eq], },
  case mul : t₁ t₂ IH₁ IH₂
  { intros h₁ h₂ e, rw[←dvector.head_tail (vecterm.val e t₂)],
    simp[-dvector.head_tail, IH₁ h₁ e, IH₂ h₂ e, mul_eq] }
end

lemma open_complete {p : formula LA} :
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
    { have lmm₁ : predicate₂ (𝐐^0) *≤ ⟦(t₁.val e).head˙⟧ᴴ ⟦(t₂.val e).head˙⟧ᴴ = ⊤,
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



lemma sigma1_complete {p : formula LA} :
  sentence p → hierarchy.sigma_form 1 p → 𝒩 ⊧ p → 𝐐 ⊢̇ p := λ a H,
begin
  induction H∃̇[∀̇ ≤ #1][∃̇ ≤ #1]p
  

end

lemma pair_total : 𝐐 ⊢̇ ∀̇∀̇∃̇(#0 =⟨#1, #2⟩) :=
begin
  refine provable.GE (provable.GE _),
  simp,
end

end robinson

namespace bd_peano
open Herbrand Lindenbaum
open provable

lemma Lindenbaum_induction {p : formula LA} {T : theory LA} (h : T ⊢̇ 𝐈p)
  (zero : (⟦p.rew ₛ[Ż]⟧ᴸ : Lindenbaum (T^0)) = ⊤)
  (succ : (⟦p⟧ᴸ : Lindenbaum (T^1)) ≤ ⟦p.rew ₑ[Ṡ #0]⟧ᴸ) : (∏⟦p⟧ᴸ : Lindenbaum (T^0)) = ⊤ :=
begin
  simp[peano_induction, Lindenbaum.provable_imp_iff, zero] at h,
  have : ⟦p⟧ᴸᶜ ⊔ ⟦(formula.rew ₑ[Ṡ #0] p)⟧ᴸ = (⊤ : Lindenbaum (T^1)), { simp* },
  simp[this] at h, exact h
end

#check 𝐐+𝐈(hierarchy.sigma_form 1)

theorem collection (p : formula LA) : 𝐐+𝐈(hierarchy.sigma_form 1) ⊢̇ ([∀̇ ≤ #0]∃̇p) →̇ ∃̇[∀̇ ≤ #1][∃̇ ≤ #1]p :=
begin
  refine deduction.mp _,
  suffices : 𝐐+𝐈(hierarchy.sigma_form 1)+{[∀̇ ≤ #0]∃̇p} ⊢̇ ∀̇(#0 ≤̇ #1 →̇ ∃̇[∀̇ ≤ #1][∃̇ ≤ #1]p.rew (shift^2)),
  { have := this.fal_subst #0, simp at this,  }
end


end bd_peano

end fopl
