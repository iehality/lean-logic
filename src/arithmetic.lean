import deduction semantics lindenbaum

namespace fopl

namespace arithmetic
open classical_logic axiomatic_classical_logic' axiomatic_classical_logic

inductive langf : ℕ → Type
| zero : langf 0
| succ : langf 1
| add  : langf 2
| mul : langf 2

inductive langp : ℕ → Type
| le : langp 2
notation `*≤` := langp.le

@[reducible] def LA : language := ⟨langf, langp⟩

instance : has_zero_symbol LA := ⟨langf.zero⟩
instance : has_succ_symbol LA := ⟨langf.succ⟩
instance : has_add_symbol LA := ⟨langf.add⟩
instance : has_mul_symbol LA := ⟨langf.mul⟩
instance : has_le_symbol LA := ⟨langp.le⟩

local infix ` ≃₁ `:50 := ((≃) : term LA → term LA → formula LA)
local prefix `#`:max := @term.var LA
local prefix `∏₁ `:64 := (has_univ_quantifier.univ : formula LA → formula LA)
local prefix `∐₁ `:64 := (has_exists_quantifier.ex : formula LA → formula LA)

variables (s : ℕ → term LA)

@[elab_as_eliminator]
lemma LA_ind {C : term LA → Sort*}
  (var  : ∀ n, C #n)
  (zero : C 0)
  (succ : ∀ {t₁}, C t₁ → C (Succ t₁))
  (add  : ∀ {t₁ t₂}, C t₁ → C t₂ → C (t₁ + t₂)) 
  (mul  : ∀ {t₁ t₂}, C t₁ → C t₂ → C (t₁ * t₂)) : ∀ t, C t := λ t,
begin
  induction t with n n f v IH,
  { exact var _ },
  cases f,
  case langf.zero { simp[finitary.zero_eq v], exact zero },
  case langf.succ { rw (show v = ‹v 0›, by ext; simp), exact succ (IH 0) },
  case langf.add  { rw (show v = ‹v 0, v 1›, by ext; simp), exact add (IH 0) (IH 1) },
  case langf.mul  { rw (show v = ‹v 0, v 1›, by ext; simp), exact mul (IH 0) (IH 1) }
end

@[elab_as_eliminator] 
theorem LA_ind_on {C : term LA → Sort*} (t : term LA)
  (var  : ∀ n, C(#n))
  (zero : C 0)
  (succ : ∀ {t₁}, C t₁ → C (Succ t₁))
  (add  : ∀ {t₁ t₂}, C t₁ → C t₂ → C (t₁ + t₂)) 
  (mul  : ∀ {t₁ t₂}, C t₁ → C t₂ → C (t₁ * t₂)) : C t :=
LA_ind var zero @succ @add @mul t

def bounded_fal (t : term LA) (p : formula LA) : formula LA := ∏₁ ((#0 ⩽ t^1) ⟶ p)

notation `[∏`` ⩽ `t`] `p := bounded_fal t p

def bounded_ex (t : term LA) (p : formula LA) := ∐₁ ((#0 ⩽ t^1) ⊓ p)

notation `[∐`` ⩽ `t`] `p := bounded_ex t p

@[simp] lemma bounded_fal_rew (t : term LA) (p : formula LA) (s) : ([∏ ⩽ t] p).rew s = [∏ ⩽ t.rew s] (p.rew (s^1)) :=
by simp [bounded_fal, term.pow_rew_distrib]

@[simp] lemma bounded_ex_rew (t : term LA) (p : formula LA) (s) : ([∐ ⩽ t] p).rew s = [∐ ⩽ t.rew s] (p.rew (s^1)) :=
by simp [bounded_ex, term.pow_rew_distrib]


inductive robinson : theory LA
| q1 : robinson ∏₁ ⁻(0 ≃₁ Succ #0)
| q2 : robinson ∏₁ ∏₁ ((Succ #0 ≃₁ Succ #1) ⟶ (#0 ≃₁ #1))
| q3 : robinson ∏₁ ((#0 ≃₁ 0) ⊔ ∐₁ (#1 ≃₁ Succ #0))
| q4 : robinson ∏₁ (#0 + 0 ≃₁ #0)
| q5 : robinson ∏₁ ∏₁ (#0 + Succ #1 ≃₁ Succ (#0 + #1))
| q6 : robinson ∏₁ (#0 * 0 ≃₁ 0)
| q7 : robinson ∏₁ ∏₁ (#0 * Succ #1 ≃ #0 * #1 + #0)
| q8 : robinson ∏₁ ∏₁ ((#0 ⩽ #1) ⟷ ∐ (#1 + #0 ≃₁ #2))

notation `𝐐` := robinson

def peano_induction (p : formula LA) : formula LA :=
p.rew ι[0 ⇝ 0] ⊓ ∏ ((p^1).rew ι[1 ⇝ #0] ⟶ (p^1).rew ι[1 ⇝ Succ #0]) ⟶ ∏ p
prefix `𝐈`:max := peano_induction

instance : closed_theory 𝐐 := ⟨λ p h,
  by cases h; simp[sentence, lrarrow_def, formula.ex, formula.and]⟩

instance : proper 0 𝐐 := ⟨λ p s h, by { cases h; simp; exact h }⟩

inductive bounded_peano (C : set (formula LA)) : theory LA
| q   : ∀ {p}, p ∈ 𝐐 → bounded_peano p
| ind : ∀ {p : formula LA}, p ∈ C → bounded_peano 𝐈p
prefix `𝐐+𝐈`:max := bounded_peano

@[reducible] def peano : theory LA := (𝐐+𝐈(set.univ))
notation `𝐏𝐀` := peano

instance {C : set (formula LA)} [proper 0 C] : proper 0 𝐐+𝐈C := ⟨λ p s h,
begin
  simp, cases h with _ h p hyp,
  { have : p.rew s ∈ 𝐐, from proper.proper0 h,
    exact bounded_peano.q this },
  { simp,
    have : (p.rew ι[0 ⇝ 0]).rew s = (p.rew (s^1)).rew ι[0 ⇝ 0],
    { simp[formula.nested_rew], congr, ext x, cases x; simp }, simp[this],
    have : ((p^1).rew ι[1 ⇝ #0]).rew (s^1) = ((p.rew (s^1))^1).rew (ι[1 ⇝ #0]),
    { simp[formula.pow_rew_distrib, formula.pow_eq, formula.nested_rew, rewriting_sf_itr.pow_eq'],
      congr, funext x, cases x; simp[←nat.add_one, term.pow_eq] }, simp[this],
    have : ((p^1).rew ι[1 ⇝ Succ #0]).rew (s^1) = ((p.rew (s^1))^1).rew (ι[1 ⇝ Succ #0]),
    { simp[formula.pow_rew_distrib, formula.pow_eq, formula.nested_rew, rewriting_sf_itr.pow_eq'],
      congr, funext x, cases x; simp[←nat.add_one, term.pow_eq] }, simp[this],
    have : p.rew (s^1) ∈ C, from proper.proper0 hyp,
    have := bounded_peano.ind this, exact this } end⟩

lemma Q_bd_peano (C) : 𝐐 ⊆ 𝐐+𝐈C := λ p, bounded_peano.q

instance (C : theory LA) : extend 𝐐 𝐐+𝐈C := ⟨λ p h, weakening (Q_bd_peano _) h⟩

lemma bd_peano_subset {C D : set (formula LA)} : C ⊆ D → 𝐐+𝐈C ⊆ 𝐐+𝐈D := λ h p hyp_p,
by { cases hyp_p with _ hyp_p p hyp_p2,
     exact bounded_peano.q hyp_p, refine bounded_peano.ind (h hyp_p2) }

namespace hierarchy

mutual inductive sigma_form, pie_form
with sigma_form : ℕ → formula LA → Prop
| op : ∀ {p : formula LA}, p.Open → sigma_form 0 p
| bd_fal : ∀ {p} {n t}, sigma_form n p → sigma_form n [∏ ⩽ t]p
| bd_ext : ∀ {p} {n t}, sigma_form n p → sigma_form n [∐ ⩽ t]p
| qt : ∀ {p} {n}, pie_form n p → sigma_form (n+1) ∐p 
with pie_form : ℕ → formula LA → Prop
| op : ∀ {p : formula LA}, p.Open → pie_form 0 p
| bd_fal : ∀ {p} {n t}, pie_form n p → pie_form n [∏ ⩽ t]p
| bd_ext : ∀ {p} {n t}, pie_form n p → pie_form n [∐ ⩽ t]p
| qt : ∀ {p} {n}, sigma_form n p → pie_form (n+1) ∏p

prefix `𝚺⁰`:1200 := sigma_form

def sigma (T : theory LA) (n : ℕ) : set (formula LA) := {p | ∃ q, sigma_form n q ∧ T ⊢ q ⟷ p}
def pie (T : theory LA) (n : ℕ) : set (formula LA) := {p | ∃ q, pie_form n q ∧ T ⊢ q ⟷ p}
def delta (T : theory LA) (n : ℕ) : set (formula LA) :=
{p | ∃ q₁ q₂, T ⊢ q₁ ⟷ p ∧ T ⊢ q₂ ⟷ p ∧ q₁ ∈ sigma T n ∧ q₂ ∈ pie T n}

end hierarchy

namespace Q_model

end Q_model

namespace robinson
open Herbrand Lindenbaum
variables {T : theory LA} {i : ℕ} [extend 𝐐 T]

open provable

lemma ss_robinson {p} (h : p ∈ 𝐐) : T^i ⊢ p :=
by { have : T ⊢ p, from extend.le (by_axiom h),
     have : T^i ⊢ p^i, from provable.sf_itr_sf_itr.mpr this, 
     simp[show p^i = p, from formula.sentence_rew (closed_theory.cl h) _] at this,
     exact this }

@[simp] lemma succ_neq_zero  (h : Herbrand T i) : 0 ≃ Succ h = (⊥ : Lindenbaum T i) :=
by { induction h using fopl.Herbrand.ind_on,
     have : T^i ⊢ ∏ ⁻(0 ≃ Succ #0), from ss_robinson robinson.q1,
     have := (this ⊚ h), simp at this,
     have : (0 : Herbrand T i) ≃ Succ ⟦h⟧ᴴ = (⊥ : Lindenbaum T i),
       from cast (by simp[Lindenbaum.provable_equal_eq]) (Lindenbaum.provable_neg_iff.mp this),
     exact this }

@[simp] lemma succ_inj  (h₁ h₂ : Herbrand T i) : (Succ h₁ ≃ Succ h₂ : Lindenbaum T i) ≤ (h₁ ≃ h₂) :=
by { induction h₁ using fopl.Herbrand.ind_on, induction h₂ using fopl.Herbrand.ind_on,
     have : T^i ⊢ ∏₁ ∏₁ ((Succ #0 ≃ Succ #1) ⟶ (#0 ≃ #1)), from ss_robinson robinson.q2,
     have := this ⊚ h₂ ⊚ h₁, simp at this,
     have : (⟦Succ h₁ ≃ Succ h₂⟧ᴸ : Lindenbaum T i) ≤ ⟦h₁ ≃ h₂⟧ᴸ,
       from Lindenbaum.provable_imp_iff.mp this, simp[Lindenbaum.provable_equal_eq] at this,
     exact this }

@[simp] lemma add_zero  (h : Herbrand T i) : h + 0 = h :=
by { induction h using fopl.Herbrand.ind_on,
     have : T^i ⊢ ∏₁ (#0 + 0 ≃ #0), from ss_robinson robinson.q4,
     have := Herbrand.provable_iff.mp (this ⊚ h), simp[-Herbrand.of_eq_of] at this,
     exact this }

@[simp] lemma mul_zero  (h : Herbrand T i) : h * 0 = 0 :=
by { induction h using fopl.Herbrand.ind_on,
     have : T^i ⊢ ∏ (#0 * 0 ≃ 0), from ss_robinson robinson.q6,
     have : T ^ i ⊢ formula.rew ι[0 ⇝ h] ((#0 * 0) ≃ 0), from this ⊚ h,
     have := Herbrand.provable_iff.mp this, simp[-Herbrand.of_eq_of] at this, exact this }

@[simp] lemma add_succ {i} (h₁ h₂ : Herbrand T i) :
  h₁ + Succ h₂ = Succ (h₁ + h₂) :=
by { induction h₁ using fopl.Herbrand.ind_on, induction h₂ using fopl.Herbrand.ind_on,
     have : T^i ⊢ ∏ ∏ (#0 + Succ #1 ≃ Succ (#0 + #1)) := ss_robinson robinson.q5,
     have := Herbrand.provable_iff.mp (this ⊚ h₂ ⊚ h₁), simp[-Herbrand.of_eq_of] at this, exact this }

@[simp] lemma mul_succ {i} (h₁ h₂ : Herbrand T i) :
  h₁ * Succ h₂ = h₁ * h₂ + h₁ :=
by { induction h₁ using fopl.Herbrand.ind_on, induction h₂ using fopl.Herbrand.ind_on,
     have : T^i ⊢ ∏ ∏ (#0 * Succ #1 ≃ #0 * #1 + #0) := ss_robinson robinson.q7,
     have := Herbrand.provable_iff.mp (this ⊚ h₂ ⊚ h₁), simp[-Herbrand.of_eq_of] at this, exact this }

lemma le_iff {h₁ h₂ : Herbrand T i} :
  (h₁ ⩽ h₂ : Lindenbaum T i) = ∐ ((h₁.pow + ♯0) ≃ h₂.pow : Lindenbaum T (i + 1)) :=
by { induction h₁ using fopl.Herbrand.ind_on,
     induction h₂ using fopl.Herbrand.ind_on,
     have : T^i ⊢ ∏ ∏ ((#0 ⩽ #1) ⟷ ∐ (#1 + #0 ≃ #2)) := ss_robinson robinson.q8, 
     have := Lindenbaum.provable_iff.mp (this ⊚ h₂ ⊚ h₁),
     simp[←term.pow_rew_distrib, Lindenbaum.provable_equal_eq] at this, exact this }

@[simp] lemma le_refl [proper 0 T] {h : Herbrand T i} :
  (h ⩽ h : Lindenbaum T i) = ⊤ :=
by { simp[le_iff],
     have := Lindenbaum.proper.ex_subst_le ((h.pow + ♯0) ≃ h.pow : Lindenbaum T (i + 1)) 0,
     simp at*, sorry }

@[simp] lemma pow_0_eq : (0 : Herbrand T i).pow = 0 := by simp[has_zero.zero]

end robinson

namespace bd_peano
open Herbrand Lindenbaum
open provable
variables {T : theory LA} {i : ℕ} [extend 𝐐 T] [proper 0 T]
  {C : theory LA} [proper 0 C]

def Ind {C : theory LA} : Lindenbaum 𝐐+𝐈C 1 → Prop := λ l, ∃ p, p ∈ C ∧ l = ⟦p⟧ᴸ

lemma Ind_mem (p : formula LA) : Ind (⟦p⟧ᴸ : Lindenbaum 𝐐+𝐈C 1) → (⟦𝐈p⟧ᴸ : Lindenbaum 𝐐+𝐈C 0) = ⊤ :=
begin
  simp[Ind], 
  intros p0 h eqn, 
  have : 𝐐+𝐈C ⊢ 𝐈 p0,
  {have := provable.AX (bounded_peano.ind h), exact this },
  simp[@Lindenbaum.provable_top_iff0] at *,
  have eqn : classical_logic.to_quo p = classical_logic.to_quo p0, from equiv_eq_top_iff.mp eqn,
  have : (⟦𝐈p⟧ᴸ : Lindenbaum 𝐐+𝐈C 0) = ⟦𝐈p0⟧ᴸ,
  { simp[peano_induction, Lindenbaum.pow_eq, Lindenbaum.subst_eq, eqn], },
  simp*
end

lemma Lindenbaum_induction 
  (l : Lindenbaum 𝐐+𝐈C 1) (m : Lindenbaum 𝐐+𝐈C 0)
  (h : Ind l)
  (zero : m ≤ 0 ⊳ l)
  (succ : m.pow ≤ (♯0 ⊳ l.pow)ᶜ ⊔ (Succ ♯0) ⊳ l.pow) : m ≤ ∏ l :=
begin
  induction l using fopl.Lindenbaum.ind_on with p,
  have P := (provable_top_iff0.mpr (Ind_mem _ h)),
  have trn : (0 : Herbrand 𝐐+𝐈C 0) ⊳ ⟦p⟧ᴸ ⊓ ∏ ((♯0 ⊳ pow ⟦p⟧ᴸ)ᶜ ⊔ Succ ♯0 ⊳ pow ⟦p⟧ᴸ) ≤ ∏ ⟦p⟧ᴸ,
  { simp[peano_induction, Lindenbaum.subst_eq, Lindenbaum.pow_eq, compl_sup_iff_le,
    provable_imp_iff0] at P, refine P },
  have succ' : m ≤ ∏ ((♯0 ⊳ pow ⟦p⟧ᴸ)ᶜ ⊔ Succ ♯0 ⊳ pow ⟦p⟧ᴸ),
    from Lindenbaum.proper.pow_le_le_fal succ,
  have : m ≤ 0 ⊳ ⟦p⟧ᴸ ⊓ ∏ ((♯0 ⊳ pow ⟦p⟧ᴸ)ᶜ ⊔ Succ ♯0 ⊳ pow ⟦p⟧ᴸ), 
    from le_inf zero succ',
  exact le_trans this trn
end

lemma Lindenbaum_induction_top {p : formula LA} (l : Lindenbaum 𝐐+𝐈C 1)
  (h : Ind l)
  (zero : 0 ⊳ l = ⊤)
  (succ : ♯0 ⊳ l.pow ≤ Succ ♯0 ⊳ l.pow) : (∏ l : Lindenbaum 𝐐+𝐈C 0) = ⊤ :=
begin
  induction l using fopl.Lindenbaum.ind_on with p,
  have P := (provable_top_iff0.mpr (Ind_mem _ h)),
  have : (0 : Herbrand 𝐐+𝐈C 0) ⊳ ⟦p⟧ᴸ ⊓ ∏ ((♯0 ⊳ pow ⟦p⟧ᴸ)ᶜ ⊔ Succ ♯0 ⊳ pow ⟦p⟧ᴸ) ≤ ∏ ⟦p⟧ᴸ,
  { simp[peano_induction, Lindenbaum.subst_eq, Lindenbaum.pow_eq, compl_sup_iff_le,
    provable_imp_iff0] at P, refine P },
  simp[zero, succ] at this,
  have eqn : (♯0 ⊳ pow ⟦p⟧ᴸ)ᶜ ⊔ Succ ♯0 ⊳ pow ⟦p⟧ᴸ = ⊤,
    from ((♯0 ⊳ pow ⟦p⟧ᴸ).compl_sup_iff_le (Succ ♯0 ⊳ pow ⟦p⟧ᴸ)).mpr succ,
  simp[eqn] at this, exact this
end

def Lindenbaum.bd_fal {T : theory LA} (l : Lindenbaum T (i + 1)) (h : Herbrand T i) : Lindenbaum T i := ∏ ((♯0 ≼ h.pow)ᶜ ⊔ l)
def Lindenbaum.bd_ex {T : theory LA} (l : Lindenbaum T (i + 1)) (h : Herbrand T i) : Lindenbaum T i := ∐ ((♯0 ≼ h.pow) ⊓ l)

notation `∏_{≼ `:95 h `} ` l :90 := Lindenbaum.bd_fal l h 
notation `∐_{≼ `:95 h `} ` l :90 := Lindenbaum.bd_ex l h 

theorem collection (p : formula LA) [proper 0 (𝚺⁰1)] :
  𝐐+𝐈𝚺⁰1 ⊢ ([∏ ⩽ #0] ∐ p) ⟶ ∐ [∏ ⩽ #1] [∐ ⩽ #1] ((p^3).rew ι[4 ⇝ #0]).rew ι[3 ⇝ #1] :=
begin
  simp[provable_imp_iff0, bounded_fal, bounded_ext, Lindenbaum.pow_eq p, Herbrand.subst_eq, Lindenbaum.subst_eq],
  suffices : ∀ l : Lindenbaum 𝐐+𝐈𝚺⁰1 2,
    ∏_{≼ ♯1} ∐ l ≤ ∐ ∏_{≼ ♯2} ∐_{≼ ♯2} (♯1 ⊳ ♯0 ⊳ l.pow.pow.pow),
  { sorry },
  intros l,
  have : ∏_{≼ ♯1} ∐ l ≤ ∏ ∏ ((♯0 ≼ ♯1)ᶜ ⊔ ∐ ∏_{≼ ♯1} ∐_{≼ ♯1} l.pow.pow.pow),
  { refine Lindenbaum_induction _ _ _ _ _, { sorry },
    { simp, } }

end

theorem collection (p : formula LA) [proper 0 (𝚺⁰1)] : 𝐐+𝐈𝚺⁰1 ⊢ ([∏ ⩽ #0] ∐ p) ⟶ ∐ [∏ ⩽ #1] [∐ ⩽ #1] p :=
begin
  refine deduction.mp _,
  have : ∀ n, ∃ m, (((ι[0 ⇝ #0] ^ 1) ^ 1) ^ 1) m = (#n : term LA) :=
    (rewriting_sf_perm $ rewriting_sf_perm $ rewriting_sf_perm $ slide_perm _ #0), 
  rcases formula.total_rew_inv p this with ⟨q, e_q⟩,
  suffices : 𝐐+𝐈𝚺⁰1+{[∏ ⩽ #0] ∐ p} ⊢ ∏ ∏ (#0 ≤̇ #1 ⟶ ∐ [∏ ⩽ #1] [∐ ⩽ #1] q),
  { have := (this.fal_subst #0).fal_subst #0,
    simp[e_q, formula.nested_rew, rewriting_sf_itr.pow_add, subst_pow] at this,
    have eqn : (λ (x : ℕ), term.rew ι[3 ⇝ #3] (ι[4 ⇝ #4] x) : ℕ → term LA) = 
      (λ x, if x < 4 then #x else if 4 < x then #(x - 2) else #3 ),
    { funext x, have C : x < 4 ∨ x = 4 ∨ 4 < x := trichotomous x 4,
      cases C, simp[C], { by_cases C₂ : x < 3, simp[C₂], simp[show x = 3, by omega] },
      cases C; simp[C], 
      { simp[show ¬x < 4, from asymm C, show 3 < x - 1, from nat.lt_sub_left_of_add_lt C, ι],
        refl } },
    rw eqn at this, sorry },
  apply provable.deduction.mpr, simp[Lindenbaum.provable_top_iff0],
  apply Lindenbaum_induction,
  { sorry },
  { simp[e_q],
    have : predicate₂ (𝐐^0) *≤ ⟦#0⟧ᴴ c⟪*Z⟫⁰ = ⊥,
    { rw robinson.le_iff, }
       }
end

end bd_peano
end arithmetic

end fopl
