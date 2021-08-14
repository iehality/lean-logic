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
         have : (p.rew ₑ[Ṡ #0]).rew (s^1) = (p.rew (s^1)).rew (ₑ[Ṡ #0]),
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

namespace Q_model

end Q_model

namespace robinson
open Herbrand Lindenbaum
variables {T : theory LA} {i : ℕ} [extend 𝐐 T]

open provable

lemma ss_robinson : 𝐐 ⊆ T^i := λ p h,
by { refine sentence_mem_theory_sf_itr (closed_theory.cl h) i (extend.ss h)}

@[simp] lemma add_zero  (h : Herbrand T i) : h + 0 = h :=
by { induction h using fopl.Herbrand.ind_on,
     have : ∀̇ (#0 +̇ Ż =̇ #0) ∈ T^i, from ss_robinson robinson.q4,
     have := Herbrand.provable_iff.mp ((AX this).fal_subst h), simp* at *,
     exact this }

@[simp] lemma mul_zero  (h : Herbrand T i) : h * 0 = 0 :=
by { induction h using fopl.Herbrand.ind_on,
     have : ∀̇ (#0 ×̇ Ż =̇ Ż) ∈ T^i, from ss_robinson robinson.q6,
     have := (AX this).fal_subst h,
     have := Herbrand.provable_iff.mp this, simp* at this, exact this }

@[simp] lemma add_succ {i} (h₁ h₂ : Herbrand T i) :
  h₁ + Succ h₂ = Succ (h₁ + h₂) :=
by { induction h₁ using fopl.Herbrand.ind_on, induction h₂ using fopl.Herbrand.ind_on,
     have : ∀̇ ∀̇ (#0 +̇ Ṡ #1 =̇ Ṡ (#0 +̇ #1)) ∈ T^i := ss_robinson robinson.q5,
     have := ((AX this).fal_subst h₂).fal_subst h₁,
     have := Herbrand.provable_iff.mp this, simp* at this, exact this }

@[simp] lemma mul_succ {i} (h₁ h₂ : Herbrand T i) :
  h₁ * Succ h₂ = h₁ * h₂ + h₁ :=
by { induction h₁ using fopl.Herbrand.ind_on, induction h₂ using fopl.Herbrand.ind_on,
     have : ∀̇ ∀̇ (#0 ×̇ Ṡ #1 =̇ #0 ×̇ #1 +̇ #0) ∈ T^i := ss_robinson robinson.q7,
     have := ((AX this).fal_subst h₂).fal_subst h₁,
     have := Herbrand.provable_iff.mp this, simp* at this, exact this }

lemma le_iff {h₁ h₂ : Herbrand T i} :
  h₁ ≼ h₂ = ∐(h₁.sf + ⟦#0⟧ᴴ ∥ h₂.sf) :=
by { induction h₁ using fopl.Herbrand.ind_on,
     induction h₂ using fopl.Herbrand.ind_on,
     have : ∀̇ ∀̇ (#0 ≤̇ #1 ↔̇ ∃̇ (#1 +̇ #0 =̇ #2)) ∈ T^i := ss_robinson robinson.q8, 
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
