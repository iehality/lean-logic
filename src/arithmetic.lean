import class_of_formulae completeness

namespace fopl
open formula
namespace arithmetic
open axiomatic_classical_logic' axiomatic_classical_logic

inductive langf : ℕ → Type
| zero : langf 0
| succ : langf 1
| add  : langf 2
| mul : langf 2

inductive langp : ℕ → Type
| le : langp 2

@[reducible] def LA : language := ⟨langf, langp⟩

inductive additional_pr : ℕ → Type
| lt : additional_pr 2
| dvd : additional_pr 2
| prime : additional_pr 1

@[reducible] def additional : language := ⟨λ _, pempty, additional_pr⟩

inductive LIopen_fn : ℕ → Type
| pair : LIopen_fn 2

@[reducible] def LIopen : language := ⟨LIopen_fn, λ _, pempty⟩

inductive LISigma₁_fn : ℕ → Type
| exp : LISigma₁_fn 1

@[reducible] def LISigma₁ : language := ⟨LISigma₁_fn, λ _, pempty⟩

@[reducible] def LA' : language := LA + additional

instance : has_zero_symbol LA := ⟨langf.zero⟩
instance : has_succ_symbol LA := ⟨langf.succ⟩
instance : has_add_symbol LA := ⟨langf.add⟩
instance : has_mul_symbol LA := ⟨langf.mul⟩
instance : has_le_symbol LA := ⟨langp.le⟩

@[reducible] def LISigma₁.exp (t : term LISigma₁) : term LISigma₁ := term.app LISigma₁_fn.exp ‹t›

prefix `exp `:max := LISigma₁.exp

@[reducible] def LIopen.pair (t u : term LIopen) : term LIopen := term.app LIopen_fn.pair ‹t, u›

namespace additional
variables {L : language.{0}} [LA'.language_translation_coe L]

@[reducible] def lt (t u : term L) : formula L :=
app ((coe : LA'.pr 2 → L.pr 2) (sum.inr additional_pr.lt)) ‹t, u›
--app ↑(show additional.pr 2, from additional_pr.lt : additional.pr 2) ‹t, u›

@[reducible] def dvd (t u : term L) : formula L :=
app ((coe : LA'.pr 2 → L.pr 2) (sum.inr additional_pr.dvd)) ‹t, u›

@[reducible] def prime (t : term LA') : formula LA' := app (sum.inr additional_pr.prime) ‹t›

notation t ` is_prime`:80 := prime t

end additional

local infix ` ≺ `:50 := additional.lt

local infix ` ⍭ `:50 := additional.dvd

inductive robinson : theory LA
| q1 : robinson ∀₁ x, 0 ≄ Succ x
| q2 : robinson ∀₁ x, ∀₁ y, ((Succ x ≃ Succ y) ⟶ (x ≃ y))
| q3 : robinson ∀₁ x, ((x ≃ 0) ⊔ ∃₁ y, x ≃ Succ y)
| q4 : robinson ∀₁ x, x + 0 ≃ x
| q5 : robinson ∀₁ x y, x + Succ y ≃ Succ (x + y)
| q6 : robinson ∀₁ x, x * 0 ≃ 0
| q7 : robinson ∀₁ x y, x * Succ y ≃ x * y + x
| q8 : robinson ∀₁ x y, ((x ≼ y) ⟷ ∃₁ z, z + x ≃ y)

notation `𝐐` := robinson

namespace additional

instance addditional_predicate : additional.predicate := ⟨λ n, pempty.is_empty⟩

@[simp] def df_pr : Π {n} (r : additional.pr n), formula LA
| 2 additional_pr.lt := ((#0 : term LA) ≼ #1) ⊓ ((#0 : term LA) ≄ #1)
| 2 additional_pr.dvd := ∐ (#0 * #1 ≃ #2)
| 1 additional_pr.prime := ∐ (#0 + 1 ≃ #1) ⊓ ∏ (∐ (#0 * #2 ≃ #1) ⟶ (#0 ≃ 1) ⊔ (#0 ≃ #1))

@[reducible] def defs : LA.definitions additional :=
{ df_fn := λ n f, by exfalso; exact is_empty.false f,
  hdf_fn := λ n f, by exfalso; exact is_empty.false f,
  df_pr := @df_pr,
  hdf_pr := λ n r, by rcases r; simp[df_pr, numeral_one_def] }

@[simp] lemma thy.lt : defs.thy ⊢ ∀₁ x y, ((x ≺ y) ⟷ (x ≼ y) ⊓ (x ≄ y)) :=
by { refine provable.generalize (provable.generalize _),
      have := defs.pr additional_pr.lt ‹#1, #0›,
     simpa[fal_fn] using defs.pr additional_pr.lt ‹#1, #0› }

@[simp] lemma thy.dvd : defs.thy ⊢ ∀₁ x y, (x ⍭ y) ⟷ ∐ (#0 * x ≃ y) :=
by { refine provable.generalize (provable.generalize _),
     simpa[fal_fn] using defs.pr additional_pr.dvd ‹#1, #0› }

end additional

@[reducible] def add_additional (T : theory LA) : theory LA' := (↑T : theory LA') ∪ additional.defs.thy

local postfix `⁺`:1200 := add_additional

namespace additional

instance extend_coe_add_additional (T : theory LA) : extend (↑T) T⁺ := ⟨by simp⟩

instance extend_additional_add_additional (T : theory LA) : extend defs.thy T⁺ := ⟨by simp⟩

instance add_additional_extend_add_additional (T U : theory LA) [closed_theory T] [closed_theory U] [extend T U] :
  extend T⁺ U⁺ := theory.union_extend_union

instance closed_aadd_dditional (T : theory LA) [closed_theory T] : closed_theory T⁺ := fopl.union_closed ↑T defs.thy

variables {L : language.{0}}
  [LA'.language_translation_coe L] {T : theory L} [lextend defs.thy T] {i : ℕ}

def Herbrand.lt (h₁ h₂ : Herbrand T i) : Lindenbaum T i :=
Lindenbaum.predicate_of ((coe : LA'.pr 2 → L.pr 2) (sum.inr additional_pr.lt)) ‹h₁, h₂›

infix ` ≺' `:50 := Herbrand.lt

@[simp] lemma Lindenbaum.lt_def (v) :
  Lindenbaum.predicate_of ((coe : LA'.pr 2 → L.pr 2) (sum.inr additional_pr.lt)) v = (v 0 ≺' v 1 : Lindenbaum T i) := rfl

lemma Lindenbaum.lt_eq (h₁ h₂ : Herbrand T i) : (h₁ ≺' h₂) = (h₁ ≼ h₂) ⊓ (h₁ ≃ h₂)ᶜ :=
begin
  induction h₁ using fopl.Herbrand.ind_on with t,
  induction h₂ using fopl.Herbrand.ind_on with u,
  have : T^i ⊢ ∀₁ x y, ((x ≺ y) ⟷ (x ≼ y) ⊓ (x ≄ y)), by simpa[fal_fn] using provable.lextend thy.lt (T^i),
  have : T^i ⊢ (t ≺ u) ⟷ (t ≼ u) ⊓ (t ≄ u), by simpa[fal_fn] using this ⊚ t ⊚ u,
  simpa using Lindenbaum.eq_of_provable_equiv.mp this
end

def Herbrand.dvd (h₁ h₂ : Herbrand T i) : Lindenbaum T i :=
Lindenbaum.predicate_of ((coe : LA'.pr 2 → L.pr 2) (sum.inr additional_pr.dvd)) ‹h₁, h₂›

infix ` ⍭' `:50 := Herbrand.dvd

@[simp] lemma Lindenbaum.dvd_def (v) :
  Lindenbaum.predicate_of ((coe : LA'.pr 2 → L.pr 2) (sum.inr additional_pr.dvd)) v = (v 0 ⍭' v 1 : Lindenbaum T i) := rfl

lemma Lindenbaum.dvd_eq (h₁ h₂ : Herbrand T i) : (h₁ ⍭' h₂) = ∐' (♯0 * h₁.pow ≃ h₂.pow : Lindenbaum T (i + 1)) :=
begin
  induction h₁ using fopl.Herbrand.ind_on with t,
  induction h₂ using fopl.Herbrand.ind_on with u,
  have : T^i ⊢ ∀₁ x y, (x ⍭ y) ⟷ ∐ (#0 * x ≃ y), by simpa[fal_fn] using provable.lextend thy.dvd (T^i),
  have : T^i ⊢ (t ⍭ u) ⟷ ∐ (#0 * t^1 ≃ u^1), by simpa[fal_fn, subst_pow, term.pow_add] using this ⊚ t ⊚ u,
  simpa using Lindenbaum.eq_of_provable_equiv.mp this
end

end additional

def succ_induction (p : formula LA) : formula LA := ∏* (p.rew (0 ⌢ ı) ⟶ ∏ (p ⟶ p.rew ((Succ #0) ⌢ (λ x, #(x+1)))) ⟶ ∏ p)

def succ_induction' (p : formula LA') : formula LA' :=
∏* (p.rew (0 ⌢ ı) ⟶ ∏ (p ⟶ p.rew ((Succ #0) ⌢ (λ x, #(x+1)))) ⟶ ∏ p)

@[simp] lemma succ_induction_sentence (p : formula LA) : is_sentence (succ_induction p) := by simp[succ_induction]

@[simp] lemma succ_induction'_sentence (p : formula LA') : is_sentence (succ_induction' p) := by simp[succ_induction']

def order_induction (p : formula LA) : formula LA :=
(∀₁ x, ((∀₁ y ≺ᵇ x, p.rew ı-{1}) ⟶ p)) ⟶ ∀₁ x, p

def collection (p : formula LA) : formula LA :=
∀₁ u, (∀₁ x ≼ᵇ u, ∃₁ y, p.rew ı-{2}) ⟶ (∃₁ v, ∀₁ x ≼ᵇ u, ∃₁ y ≼ᵇ v, p.rew ı-{2}-{2})

instance : closed_theory 𝐐 := ⟨λ p h,
  by cases h; simp[is_sentence, lrarrow_def, formula.ex, formula.and, fal_fn, ex_fn]⟩

def succ_induction_axiom (C : theory LA) : theory LA := 𝐐 ∪ (succ_induction '' C)

prefix `𝐈`:max := succ_induction_axiom

def order_induction_axiom (C : theory LA) : theory LA := 𝐐 ∪ (order_induction '' C)

prefix `𝐈′`:max := order_induction_axiom

def collection_axiom (C : theory LA) : theory LA := 𝐐 ∪ (collection '' C)

prefix `𝐁`:max := collection_axiom

@[reducible] def peano : theory LA := 𝐈set.univ

notation `𝐏𝐀` := peano

instance {C : theory LA} : closed_theory 𝐈C := 
⟨λ p h, by { rcases h with (h | ⟨p, hp, rfl⟩), { refine closed_theory.cl h }, { simp[succ_induction] } }⟩

@[simp] lemma Q_ss_I {C} : 𝐐 ⊆ 𝐈C := by simp[succ_induction_axiom]

instance extend_Q_I (C : theory LA) : extend 𝐐 𝐈C := ⟨λ p h, weakening Q_ss_I h⟩

instance extend_ax₁ (C : theory LA) (p : formula LA) : extend 𝐐 (𝐈C +{ p }) :=
theory.extend_of_inclusion (λ p mem, by simp[Q_ss_I mem])

instance extend_ax₂ (C : theory LA) (p q : formula LA) : extend 𝐐 (𝐈C +{ p }+{ q }) :=
theory.extend_of_inclusion (λ p mem, by simp[Q_ss_I mem])

instance extend_ax₃ (C : theory LA) (p q r : formula LA) : extend 𝐐 (𝐈C +{ p }+{ q }+{ r }) :=
theory.extend_of_inclusion (λ p mem, by simp[Q_ss_I mem])

instance extend_ax₄ (C : theory LA) (p q r s : formula LA) : extend 𝐐 (𝐈C +{ p }+{ q }+{ r }+{ s }) :=
theory.extend_of_inclusion (λ p mem, by simp[Q_ss_I mem])

lemma I_succ_induction (p : formula LA) {C} (h : p ∈ C) : 𝐈C ⊢ p.rew (0 ⌢ ı) ⟶ ∏ (p ⟶ p.rew ((Succ #0) ⌢ (λ x, #(x+1)))) ⟶ ∏ p :=
by { have : 𝐈C ⊢ succ_induction p, from by_axiom (by { simp[succ_induction_axiom, h], refine or.inr ⟨p, by simp[h]⟩ }),
     simpa using provable.fal_complete_rew _ ı ⨀ this }

namespace robinson
open Herbrand Lindenbaum provable
variables {L : language.{0}} [LA.language_translation_coe L] (T : theory L) [lextend 𝐐 T] (i : ℕ)

instance extend_coe_Q_Q' : extend (↑𝐐 : theory LA') 𝐐⁺ := theory.extend_union_left _ _

lemma of_mem_robinson {p} (h : 𝐐 p) : 𝐐⁺ ⊢ p :=
provable.extend (show (↑𝐐 : theory LA') ⊢ ↑p, by { simp, exact by_axiom h })

@[simp] lemma zero_ne_succ : 𝐐 ⊢ ∀₁ x, 0 ≄ Succ x :=
by simpa[fal_fn] using by_axiom robinson.q1

@[simp] lemma Lindembaum.zero_ne_succ (h : Herbrand T i) : 0 ≃ Succ h = (⊥ : Lindenbaum T i) :=
by { induction h using fopl.Herbrand.ind_on,
     have : T^i ⊢ ∏ (0 ≄ Succ #0), by simpa[fal_fn] using provable.lextend zero_ne_succ (T^i),
     simpa[Lindenbaum.eq_neg_of_provable_neg_0] using this ⊚ h }

@[simp] lemma Lindenbaum.succ_ne_zero (h : Herbrand T i) : Succ h ≃ 0 = (⊥ : Lindenbaum T i) :=
by simp [Lindenbaum.equal_symm (Succ h) 0]

@[simp] lemma succ_inj :
  𝐐 ⊢ ∀₁ x y, (Succ x ≃ Succ y) ⟶ (x ≃ y) :=
by simpa[fal_fn] using by_axiom robinson.q2

@[simp] lemma Lindenbaum.succ_inj  (h₁ h₂ : Herbrand T i) : (Succ h₁ ≃ Succ h₂ : Lindenbaum T i) = (h₁ ≃ h₂) :=
by { induction h₁ using fopl.Herbrand.ind_on with t,
     induction h₂ using fopl.Herbrand.ind_on with u,
     have : T^i ⊢ ∏ ∏ ((Succ #1 ≃ Succ #0) ⟶ (#1 ≃ #0)), by simpa[fal_fn] using provable.lextend succ_inj (T^i) ,
     have : T^i ⊢ (Succ t ≃ Succ u) ⟷ (t ≃ u), by simpa[iff_equiv, fal_fn] using this ⊚ t ⊚ u,
     simpa using Lindenbaum.eq_of_provable_equiv.mp this }

lemma Herbrand.succ_injective : function.injective (has_succ.succ : Herbrand T i → Herbrand T i) :=
λ h₁ h₂,
begin
  induction h₁ using fopl.Herbrand.ind_on with t,
  induction h₂ using fopl.Herbrand.ind_on with u,
  intros h,
  have lmm₁ : T^i ⊢ Succ t ≃ Succ u, from Herbrand.eq_of_provable_equiv.mpr (by simp[h]),
  have : T^i ⊢ ∏ ∏ ((Succ #1 ≃ Succ #0) ⟶ (#1 ≃ #0)), by simpa[fal_fn] using provable.lextend succ_inj (T^i),
  have lmm₂ : T^i ⊢ (Succ t ≃ Succ u) ⟶ (t ≃ u), by simpa[fal_fn] using this ⊚ t ⊚ u, 
  have : T^i ⊢ t ≃ u, from lmm₂ ⨀ lmm₁,
  exact Herbrand.eq_of_provable_equiv.mp this
end

@[simp] lemma Herbrand.succ_injective_iff (h₁ h₂ : Herbrand T i) : Succ h₁ = Succ h₂ ↔ h₁ = h₂ :=
⟨@@Herbrand.succ_injective _ T _ i, λ h, by simp[h]⟩

@[simp] lemma zero_or_succ : 𝐐 ⊢ ∀₁ x, (x ≃ 0) ⊔ (∃₁ y, x ≃ Succ y) :=
by simpa[fal_fn, ex_fn] using by_axiom robinson.q3

@[simp] lemma zero_or_succ' (t : term LA) : 𝐐 ⊢ (t ≃ 0) ⊔ ∃₁ y, t^1 ≃ Succ y :=
by simpa[fal_fn, ex_fn] using zero_or_succ ⊚ t

@[simp] lemma add_zero : 𝐐 ⊢ ∀₁ x, (x + 0 ≃ x) :=
by simpa[fal_fn] using (by_axiom robinson.q4)

@[simp] lemma Herbrand.add_zero (h : Herbrand T i) : h + 0 = h :=
by { induction h using fopl.Herbrand.ind_on with t,
     have : T^i ⊢ ∀₁ x, (x + 0 ≃ x), by simpa[fal_fn] using provable.lextend add_zero (T^i),
     simpa using Herbrand.eq_of_provable_equiv.mp (this ⊚ t) }

lemma add_succ : 𝐐 ⊢ ∀₁ x y, x + Succ y ≃ Succ (x + y) :=
by simpa[fal_fn] using (by_axiom robinson.q5)

@[simp] lemma Herbrand.add_succ {i} (h₁ h₂ : Herbrand T i) : h₁ + Succ h₂ = Succ (h₁ + h₂) :=
by { induction h₁ using fopl.Herbrand.ind_on with t,
     induction h₂ using fopl.Herbrand.ind_on with u,
     have : T^i ⊢ ∀₁ x y, x + Succ y ≃ Succ (x + y), by simpa[fal_fn] using provable.lextend add_succ (T^i),
     simpa using Herbrand.eq_of_provable_equiv.mp (this ⊚ t ⊚ u) }

@[simp] lemma mul_zero : 𝐐 ⊢ ∀₁ x, x * 0 ≃ 0 :=
by simpa[fal_fn] using by_axiom robinson.q6

@[simp] lemma Herbrand.mul_zero  (h : Herbrand T i) : h * 0 = 0 :=
by { induction h using fopl.Herbrand.ind_on with t,
     have : T^i ⊢ ∀₁ x, x * 0 ≃ 0, by simpa[fal_fn] using provable.lextend mul_zero (T^i),
     simpa using Herbrand.eq_of_provable_equiv.mp (this ⊚ t) }

lemma mul_succ : 𝐐 ⊢ ∀₁ x y, x * Succ y ≃ x * y + x :=
by simpa[fal_fn] using (by_axiom robinson.q7)

@[simp] lemma Herbrand.mul_succ {i} (h₁ h₂ : Herbrand T i) : h₁ * Succ h₂ = h₁ * h₂ + h₁ :=
by { induction h₁ using fopl.Herbrand.ind_on with t,
     induction h₂ using fopl.Herbrand.ind_on with u,
     have : T^i ⊢ ∀₁ x y, x * Succ y ≃ x * y + x, by simpa[fal_fn] using provable.lextend mul_succ (T^i),
     have : T^i ⊢ t * Succ u ≃ t * u + t, by simpa[fal_fn] using this ⊚ t ⊚ u,
     simpa using Herbrand.eq_of_provable_equiv.mp this }

@[simp] lemma le_iff : 𝐐 ⊢ ∀₁ x y, (x ≼ y) ⟷ ∃₁ z, (z + x ≃ y) :=
by simpa[fal_fn, ex_fn, ←term.pow_rew_distrib] using (by_axiom robinson.q8)

@[simp] lemma le_iff' (t u : term LA) : 𝐐 ⊢ (t ≼ u) ⟷ ∃₁ z, (z + t^1 ≃ u^1) :=
by simpa[fal_fn, ex_fn, ←term.pow_rew_distrib] using le_iff ⊚ t ⊚ u

lemma Lindenbaum.le_iff {h₁ h₂ : Herbrand T i} :
  (h₁ ≼ h₂ : Lindenbaum T i) = ∐' (♯0 + h₁.pow ≃ h₂.pow : Lindenbaum T (i + 1)) :=
by { induction h₁ using fopl.Herbrand.ind_on with t,
     induction h₂ using fopl.Herbrand.ind_on with u,
     have : T^i ⊢ ∀₁ x y, (x ≼ y) ⟷ ∃₁ z, (z + x ≃ y), by simpa[fal_fn, ex_fn] using provable.lextend le_iff (T^i),
     have : T^i ⊢ (t ≼ u) ⟷ ∐ (#0 + t^1 ≃ u^1), by simpa[fal_fn, ex_fn, ←term.pow_rew_distrib] using this ⊚ t ⊚ u,
     simpa using Lindenbaum.eq_of_provable_equiv.mp this }

namespace Lindenbaum

lemma le_of_eq (e : Herbrand T i) {h₁ h₂ : Herbrand T i} (h : e + h₁ = h₂) : h₁ ≤ h₂ :=
begin
  induction e using fopl.Herbrand.ind_on with u,
  induction h₁ using fopl.Herbrand.ind_on with t₁,
  induction h₂ using fopl.Herbrand.ind_on with t₂,
  have lmm₁ : T^i ⊢ ∐ (#0 + t₁^1 ≃ t₂^1),
  { refine use u _, simp, refine Herbrand.eq_of_provable_equiv.mpr (by simp[h]) },
  have : T ^ i ⊢ ∀₁ x y, (x ≼ y) ⟷ ∃₁ z, z + x ≃ y, by simpa[fal_fn, ex_fn] using provable.lextend (robinson.le_iff) (T^i),
  have lmm₂ : T^i ⊢ (t₁ ≼ t₂) ⟷ ∐ (#0 + t₁^1 ≃ t₂^1), by simpa[fal_fn, ex_fn, ←term.pow_rew_distrib] using this ⊚ t₁ ⊚ t₂,
  exact Herbrand.le_iff_provable_le.mp (of_equiv lmm₁ (equiv_symm lmm₂))
end

@[simp] lemma le_add_self (h₁ h₂ : Herbrand T i) : h₁ ≤ h₂ + h₁ := le_of_eq T i h₂ rfl

@[simp] lemma succ_inj_le {h₁ h₂ : Herbrand T i} :
  (Succ h₁ ≼ Succ h₂ : Lindenbaum T i) = (h₁ ≼ h₂) := by simp[le_iff, succ_pow]

lemma add_numeral_eq_numeral_add (m n : ℕ) : (n˙ : Herbrand T i) + m˙ = (n + m)˙ :=
by induction m with m IH; simp[numeral, *, ←nat.add_one, ←add_assoc]

lemma mul_numeral_eq_numeral_mul (m n : ℕ) : (n˙ : Herbrand T i) * m˙ = (n * m)˙ :=
by induction m with m IH; simp[numeral, *, ←nat.add_one, add_numeral_eq_numeral_add, mul_add]

lemma succ_add_numeral_eq_add_succ_numeral (h : Herbrand T i) (n : ℕ) : Succ h + n˙ = h + (n + 1)˙ :=
by induction n with n IH; simp[numeral, *]

end Lindenbaum

@[simp] lemma add_eq_zero : 𝐐 ⊢ ∀₁ x y, (x + y ≃ 0) ⟶ (x ≃ 0) ⊓ (y ≃ 0) :=
begin
  refine generalize (generalize _), simp[fal_fn], 
  have lmm₁ : 𝐐 ⊢ (#0 ≃ 0) ⟶ (#1 + #0 ≃ 0) ⟶ (#1 ≃ 0) ⊓ (#0 ≃ 0),
    from (deduction.mp (by simp [le_of_provable_imply_0, rew_by_axiom₁])),
  have lmm₂ : 𝐐 ⊢ (∃₁ y, #1 ≃ Succ y) ⟶ (#1 + #0 ≃ 0) ⟶ (#1 ≃ 0) ⊓ (#0 ≃ 0),
    from imply_ex_of_fal_imply (generalize (deduction.mp (by simp [le_of_provable_imply_0, rew_by_axiom₁]))), 
  exact case_of_ax (show 𝐐 ⊢ (#0 ≃ 0) ⊔ ∃₁ y, (#1 ≃ Succ y), from zero_or_succ' #0) lmm₁ lmm₂
end

@[simp] lemma Lindenbaum.add_eq_0_of_eq_0 (x y : Herbrand T i) :
  (x + y ≃ 0 : Lindenbaum T i) = (x ≃ 0) ⊓ (y ≃ 0) :=
begin
  induction x using fopl.Herbrand.ind_on,
  induction y using fopl.Herbrand.ind_on,
  have : T^i ⊢ ∀₁ x y, (x + y ≃ 0) ⟶ (x ≃ 0) ⊓ (y ≃ 0), by simpa[fal_fn] using provable.lextend add_eq_zero (T^i),
  have : T^i ⊢ (x + y ≃ 0) ⟷ (x ≃ 0) ⊓ (y ≃ 0), 
  { simp[iff_equiv],
    refine ⟨by simpa[fal_fn] using this ⊚ x ⊚ y, deduction.mp _⟩, simp,
    simp[Herbrand.eq_of_provable_equiv_0, rew_by_axiom₁, rew_by_axiom₂] },
  simpa using Lindenbaum.eq_of_provable_equiv.mp this
end

lemma mul_eq_zero : 𝐐 ⊢ ∀₁ x y, (x * y ≃ 0) ⟶ (x ≃ 0) ⊔ (y ≃ 0) :=
begin
  refine generalize (generalize _), simp[fal_fn], 
  have lmm₁ : 𝐐 ⊢ (#0 ≃ 0) ⟶ (#1 * #0 ≃ 0) ⟶ (#1 ≃ 0) ⊔ (#0 ≃ 0),
  { refine (deduction.mp _),
    simp[le_of_provable_imply_0, rew_by_axiom₁] },
  have lmm₂ : 𝐐 ⊢ (∃₁ y, #1 ≃ Succ y) ⟶ (#1 * #0 ≃ 0) ⟶ (#1 ≃ 0) ⊔ (#0 ≃ 0),
  { refine imply_ex_of_fal_imply (generalize (deduction.mp _)), simp,
    simp[le_of_provable_imply_0, rew_by_axiom₁] },
  exact case_of_ax (show 𝐐 ⊢ (#0 ≃ 0) ⊔ ∃₁ y, (#1 ≃ Succ y), from zero_or_succ' #0) lmm₁ lmm₂
end

lemma zero_le : 𝐐 ⊢ ∀₁ x, 0 ≼ x :=
begin
  refine generalize _, simp,
  have : 𝐐 ⊢ (0 ≼ #0) ⟷ (∃₁ z, z + 0 ≃ #1), by simpa using (le_iff' 0 #0), 
  refine of_equiv _ (equiv_symm this),
  exact use #0 (by { simp, refine Herbrand.eq_of_provable_equiv_0.mpr (by simp) } )
end

@[simp] lemma Lindenbaum.zero_le (h : Herbrand T i) : 0 ≤ h :=
by { induction h using fopl.Herbrand.ind_on with t,
     have : T^i ⊢ ∀₁ x, 0 ≼ x, by simpa[fal_fn] using provable.lextend zero_le (T^i),
     have : T^i ⊢ 0 ≼ t, by simpa using this ⊚ t,
     simpa using Herbrand.le_iff_provable_le.mp this }

@[simp] lemma le_zero_equiv_eq_zero : 𝐐 ⊢ ∀₁ x, (x ≼ 0) ⟷ (x ≃ 0) :=
begin
  refine generalize _, simp[fal_fn],
  suffices : 𝐐 ⊢ ∐ (#0 + #1 ≃ 0) ⟷ (#0 ≃ 0),
  { simp[Lindenbaum.eq_of_provable_equiv_0, Lindenbaum.le_iff] at this ⊢, exact this },
  simp[iff_equiv], split,
  { refine ((pnf_imply_ex_iff_fal_imply₁ _ _).mpr $ generalize _),
    simp[Lindenbaum.le_of_provable_imply_0] },
  { refine deduction.mp (use 0 _), simp[ı, Herbrand.eq_of_provable_equiv_0, rew_by_axiom₁] }
end

@[simp] lemma Lindenbaum.le_zero_eq_eq_zero (h : Herbrand T i) : (h ≼ 0 : Lindenbaum T i) = (h ≃ 0) :=
begin
  induction h using fopl.Herbrand.ind_on with t,
  have : T^i ⊢ ∀₁ x, (x ≼ 0) ⟷ (x ≃ 0), by simpa[fal_fn] using provable.lextend le_zero_equiv_eq_zero (T^i),
  have : T^i ⊢ (t ≼ 0) ⟷ (t ≃ 0), by simpa[fal_fn] using this ⊚ t,
  simpa[Lindenbaum.eq_of_provable_equiv_0] using this
end


@[simp] lemma add_numeral_eq_numeral_add (n m : ℕ) : 𝐐 ⊢ (n˙ : term LA) + m˙ ≃ (n + m)˙ :=
by simp[Herbrand.eq_of_provable_equiv_0, Lindenbaum.add_numeral_eq_numeral_add]

@[simp] lemma mul_numeral_eq_numeral_mul (n m : ℕ) : 𝐐 ⊢ (n˙ : term LA) * m˙ ≃ (n * m)˙ :=
by simp[Herbrand.eq_of_provable_equiv_0, Lindenbaum.mul_numeral_eq_numeral_mul]

lemma le_numeral_of_le {n m : ℕ} (h : n ≤ m) : 𝐐 ⊢ (n˙ : term LA) ≼ m˙ :=
begin
  let l := m - n,
  have : m = l + n, from (nat.sub_eq_iff_eq_add h).mp rfl,
  simp[this],
  refine of_equiv (use (l˙) _) (equiv_symm $ le_iff' _ _), simp,
end

lemma le_numeral_iff (n : ℕ) : 𝐐 ⊢ ∏ ((#0 ≼ n˙) ⟷ ⋁ i : fin (n+1), #0 ≃ (i : ℕ)˙) :=
begin
  induction n with n IH,
  { refine generalize _, simp[Lindenbaum.eq_top_of_provable_0], exact Lindenbaum.le_zero_eq_eq_zero _ _ _ },
  { refine generalize _, simp[-sup_disjunction] at IH ⊢,
    simp[iff_equiv, -sup_disjunction], split,
    { have zero : 𝐐 ⊢ (#0 ≃ 0) ⟶ (#0 ≼ (n + 1)˙) ⟶ ⋁ (i : fin (n.succ + 1)), #0 ≃ ↑i˙,
      { refine (deduction.mp $ deduction.mp $ imply_or_right _ _ ⨀ (rew_of_eq 0 0 (by simp) _)), 
        simp, refine disjunction_of ⟨0, by simp⟩ (by simp[numeral]) },
      have succ : 𝐐 ⊢ (∃₁ y, #1 ≃ Succ y) ⟶ (#0 ≼ (n + 1)˙) ⟶ ⋁ (i : fin (n.succ + 1)), #0 ≃ ↑i˙,
      { refine (imply_ex_of_fal_imply $ generalize $ deduction.mp $ rew_of_eq (Succ #0) 1 (by simp) (deduction.mp _)),
        simp[ -sup_disjunction], 
        have : 𝐐 +{ #1 ≃ Succ #0 } +{ Succ #0 ≼ (n + 1)˙ } ⊢ #0 ≼ n˙,
          from of_equiv_p (show _ ⊢ Succ #0 ≼ (n + 1)˙, by simp) (by simp[numeral, Lindenbaum.eq_of_provable_equiv_0]), 
        have lmm₁ : 𝐐 +{ #1 ≃ Succ #0 } +{ Succ #0 ≼ (n + 1)˙ } ⊢ ⋁ (i : fin (n + 1)), #0 ≃ ↑i˙,
          from of_equiv_p this (weakening
            (show 𝐐 ⊆ 𝐐 +{ #1 ≃ Succ #0 } +{ Succ #0 ≼ (n + 1)˙ }, by { intros p mem, refine set.subset_insert _ _ (set.subset_insert _ _ mem) })
            (show 𝐐 ⊢ (#0 ≼ n˙) ⟷ ⋁ (i : fin (n + 1)), #0 ≃ ↑i˙, by simpa using IH ⊚ #0)),
        have lmm₂ : 𝐐 +{ #1 ≃ Succ #0 } +{ Succ #0 ≼ (n + 1)˙ } ⊢ (⋁ (i : fin (n + 1)), #0 ≃ ↑i˙) ⟶ (⋁ (i : fin (n.succ + 1)), Succ #0 ≃ ↑i˙),
        { suffices : 𝐐 +{ #1 ≃ Succ #0 } +{ Succ #0 ≼ (n + 1)˙ } ⊢ ⋀ (i : fin (n + 1)), (#0 ≃ ↑i˙) ⟶ ⋁ (i : fin (n.succ + 1)), Succ #0 ≃ ↑i˙,
            from of_equiv this (conj_imply_iff_disj_imply _ _),
          refine conjunction_iff.mpr (λ i, deduction.mp $ rew_of_eq (↑i˙) 0 (by simp) _), simp[-sup_disjunction],
          refine disjunction_of ⟨i + 1, by simp⟩ (by simp[numeral]) },
        exact lmm₂ ⨀ lmm₁ },
      exact case_of_ax (show 𝐐 ⊢ (#0 ≃ 0) ⊔ ∃₁ y, (#1 ≃ Succ y), from zero_or_succ' #0) zero succ },
    { refine of_equiv (conjunction_iff.mpr _) (conj_imply_iff_disj_imply _ _),
      rintros ⟨i, hi⟩, refine (deduction.mp $  rew_of_eq (i˙) 0 (by simp) _),
      simp[←nat.add_one, le_numeral_of_le (show i ≤ n + 1, from nat.lt_succ_iff.mp hi)] } }
end

end robinson
/--//--/
namespace Iopen
open Herbrand Lindenbaum robinson.Lindenbaum
open provable
notation `𝐈ₒₚₑₙ` := 𝐈is_open

variables {T : theory LA} {i : ℕ} [extend 𝐈ₒₚₑₙ T]

lemma zero_add : 𝐈ₒₚₑₙ ⊢ ∀₁ x, (0 + x ≃ x) :=
begin
  have lmm₁ : 𝐈ₒₚₑₙ ⊢ (0 + 0 ≃ 0) ⟶ ∏ ((0 + #0 ≃ #0) ⟶ (0 + Succ #0 ≃ Succ #0)) ⟶ ∏ (0 + #0 ≃ #0), 
    by simpa using @I_succ_induction (0 + #0 ≃ #0) is_open (by simp[set.mem_def]),
  have lmm₂ : 𝐈ₒₚₑₙ ⊢ ∏ ((0 + #0 ≃ #0) ⟶ (0 + Succ #0 ≃ Succ #0)),
  { refine generalize (deduction.mp _), 
    have : 𝐈ₒₚₑₙ +{ 0 + #0 ≃ #0 } ⊢ 0 + #0 ≃ #0, by simp,
    simp[Herbrand.eq_of_provable_equiv_0] at this ⊢, 
    simp[this] },
  exact lmm₁ ⨀ (by simp[Herbrand.eq_of_provable_equiv_0]) ⨀ lmm₂,
end

@[simp] lemma Lindenbaum.zero_add (h : Herbrand T i) : 0 + h = h :=
begin
  induction h using fopl.Herbrand.ind_on with t,
  have : T^i ⊢ 0 + t ≃ t, from provable.extend_pow (show 𝐈ₒₚₑₙ ⊢ 0 + t ≃ t, by simpa using zero_add ⊚ t) i,
  simpa using Herbrand.eq_of_provable_equiv.mp this
end

lemma succ_add : 𝐈ₒₚₑₙ ⊢ ∀₁ x y, Succ x + y ≃ Succ (x + y) :=
begin
  have ind : 𝐈ₒₚₑₙ ⊢ (Succ #0 + 0 ≃ Succ (#0 + 0)) ⟶
                     ∏ ((Succ #1 + #0 ≃ Succ (#1 + #0)) ⟶ (Succ #1 + Succ #0 ≃ Succ (#1 + Succ #0))) ⟶
                     ∏ (Succ #1 + #0 ≃ Succ (#1 + #0)), 
  by simpa using @I_succ_induction (Succ #1 + #0 ≃ Succ (#1 + #0)) is_open (by simp[set.mem_def]),
  have zero : 𝐈ₒₚₑₙ ⊢ Succ #0 + 0 ≃ Succ (#0 + 0),  by simp[Herbrand.eq_of_provable_equiv_0],
  have succ : 𝐈ₒₚₑₙ ⊢ ∏ ((Succ #1 + #0 ≃ Succ (#1 + #0)) ⟶ (Succ #1 + Succ #0 ≃ Succ (#1 + Succ #0))),
  { refine (generalize $ deduction.mp _), simp,
    have : 𝐈ₒₚₑₙ +{ Succ #1 + #0 ≃ Succ (#1 + #0) } ⊢ Succ #1 + #0 ≃ Succ (#1 + #0), by simp,
    simp[Herbrand.eq_of_provable_equiv_0] at this ⊢,  simp[this] },
  refine (generalize _), simp[fal_fn], exact ind ⨀ zero ⨀ succ
end

@[simp] lemma Lindenbaum.succ_add (h₁ h₂ : Herbrand T i) : Succ h₁ + h₂ = Succ (h₁ + h₂) :=
begin
  induction h₁ using fopl.Herbrand.ind_on with t, induction h₂ using fopl.Herbrand.ind_on with u,
  have : T^i ⊢ Succ t + u ≃ Succ (t + u),
    from provable.extend_pow (show 𝐈ₒₚₑₙ ⊢ Succ t + u ≃ Succ (t + u), by simpa[fal_fn] using succ_add ⊚ t ⊚ u) i,
   simpa using Herbrand.eq_of_provable_equiv.mp this
end

lemma add_commutative : 𝐈ₒₚₑₙ ⊢ ∀₁ x y, x + y ≃ y + x :=
begin
  have ind : 𝐈ₒₚₑₙ ⊢ (#0 + 0 ≃ 0 + #0) ⟶ ∏ ((#1 + #0 ≃ #0 + #1) ⟶ (#1 + Succ #0 ≃ Succ #0 + #1)) ⟶ ∏ (#1 + #0 ≃ #0 + #1),
    by simpa using @I_succ_induction (#1 + #0 ≃ #0 + #1) is_open (by simp[set.mem_def]),
  have zero : 𝐈ₒₚₑₙ ⊢ #0 + 0 ≃ 0 + #0, by simp[Herbrand.eq_of_provable_equiv_0],
  have succ : 𝐈ₒₚₑₙ ⊢ ∏ ((#1 + #0 ≃ #0 + #1) ⟶ (#1 + Succ #0 ≃ Succ #0 + #1)),
  { refine (generalize $ deduction.mp _), simp,
    have : 𝐈ₒₚₑₙ +{ #1 + #0 ≃ #0 + #1 } ⊢ #1 + #0 ≃ #0 + #1, by simp,
    simp[Herbrand.eq_of_provable_equiv_0] at this ⊢,  simp[this] },
  refine (generalize _), simp[fal_fn], exact ind ⨀ zero ⨀ succ
end

lemma Lindenbaum.add_commutative (h₁ h₂ : Herbrand T i) : h₁ + h₂ = h₂ + h₁ :=
begin
  induction h₁ using fopl.Herbrand.ind_on with t, induction h₂ using fopl.Herbrand.ind_on with u,
  have : T^i ⊢ t + u ≃ u + t,
    from provable.extend_pow (show 𝐈ₒₚₑₙ ⊢ t + u ≃ u + t, by simpa[fal_fn] using add_commutative ⊚ t ⊚ u) i,
  simpa using Herbrand.eq_of_provable_equiv.mp this
end

lemma add_associative : 𝐈ₒₚₑₙ ⊢ ∀₁ x y z, x + y + z ≃ x + (y + z) :=
begin
  have ind : 𝐈ₒₚₑₙ ⊢ (#1 + #0 + 0 ≃ #1 + (#0 + 0)) ⟶
                     ∏ ((#2 + #1 + #0 ≃ #2 + (#1 + #0)) ⟶ (#2 + #1 + Succ #0 ≃ #2 + (#1 + Succ #0))) ⟶
                     ∏ (#2 + #1 + #0 ≃ #2 + (#1 + #0)),
  by simpa using @I_succ_induction (#2 + #1 + #0 ≃ #2 + (#1 + #0)) is_open (by simp[set.mem_def]),
  have zero : 𝐈ₒₚₑₙ ⊢ #1 + #0 + 0 ≃ #1 + (#0 + 0), by simp[Herbrand.eq_of_provable_equiv_0],
  have succ : 𝐈ₒₚₑₙ ⊢ ∏ ((#2 + #1 + #0 ≃ #2 + (#1 + #0)) ⟶ (#2 + #1 + Succ #0 ≃ #2 + (#1 + Succ #0))),
  { refine (generalize $ deduction.mp _), simp,
    have : 𝐈ₒₚₑₙ +{ #2 + #1 + #0 ≃ #2 + (#1 + #0) } ⊢ #2 + #1 + #0 ≃ #2 + (#1 + #0), by simp,
    simp[Herbrand.eq_of_provable_equiv_0] at this ⊢, simp[this] },
  refine (generalize $ generalize _), simp[fal_fn], exact ind ⨀ zero ⨀ succ
end

lemma Lindenbaum.add_associative (h₁ h₂ h₃ : Herbrand T i) : h₁ + h₂ + h₃ = h₁ + (h₂ + h₃) :=
begin
  induction h₁ using fopl.Herbrand.ind_on with t₁,
  induction h₂ using fopl.Herbrand.ind_on with t₂,
  induction h₃ using fopl.Herbrand.ind_on with t₃,
  have : T^i ⊢ t₁ + t₂ + t₃ ≃ t₁ + (t₂ + t₃),
    from provable.extend_pow (show 𝐈ₒₚₑₙ ⊢ t₁ + t₂ + t₃ ≃ t₁ + (t₂ + t₃), by simpa[fal_fn] using add_associative ⊚ t₁ ⊚ t₂ ⊚ t₃) i,
  simpa using Herbrand.eq_of_provable_equiv.mp this
end

instance Lindenbaum.add_comm_semigroup : add_comm_semigroup (Herbrand T i) :=
{ add := (+),
  add_assoc := Lindenbaum.add_associative,
  add_comm := Lindenbaum.add_commutative }

lemma zero_mul : 𝐈ₒₚₑₙ ⊢ ∀₁ x, (0 * x ≃ 0) :=
begin
  have ind : 𝐈ₒₚₑₙ ⊢ (0 * 0 ≃ 0) ⟶ ∏ ((0 * #0 ≃ 0) ⟶ (0 * Succ #0 ≃ 0)) ⟶ ∏ (0 * #0 ≃ 0),
    by simpa using @I_succ_induction (0 * #0 ≃ 0) is_open (by simp[set.mem_def]), 
  have zero : 𝐈ₒₚₑₙ ⊢ 0 * 0 ≃ 0, by simp[Herbrand.eq_of_provable_equiv_0],
  have succ : 𝐈ₒₚₑₙ ⊢ ∏ ((0 * #0 ≃ 0) ⟶ (0 * Succ #0 ≃ 0)),
  { refine (generalize $ deduction.mp _),
    have : 𝐈ₒₚₑₙ +{ 0 * #0 ≃ 0 } ⊢ 0 * #0 ≃ 0, by simp,
    simp[Herbrand.eq_of_provable_equiv_0] at this ⊢, simp[this] },
  simp[fal_fn], exact ind ⨀ zero ⨀ succ
end

@[simp] lemma Lindenbaum.zero_mul (h : Herbrand T i) : 0 * h = 0 :=
begin
  induction h using fopl.Herbrand.ind_on with t,
  have : T^i ⊢ 0 * t ≃ 0, from provable.extend_pow (show 𝐈ₒₚₑₙ ⊢ 0 * t ≃ 0, by simpa using zero_mul ⊚ t) i,
  simpa using Herbrand.eq_of_provable_equiv.mp this
end

lemma succ_mul : 𝐈ₒₚₑₙ ⊢ ∀₁ x y, Succ x * y ≃ x * y + y :=
begin
  have ind : 𝐈ₒₚₑₙ ⊢ (Succ #0 * 0 ≃ #0 * 0 + 0) ⟶
                     ∏ ((Succ #1 * #0 ≃ #1 * #0 + #0) ⟶ (Succ #1 * Succ #0 ≃ #1 * Succ #0 + Succ #0)) ⟶
                     ∏ (Succ #1 * #0 ≃ #1 * #0 + #0),
  by simpa using @I_succ_induction (Succ #1 * #0 ≃ #1 * #0 + #0) is_open (by simp[set.mem_def]),
  have zero : 𝐈ₒₚₑₙ ⊢ Succ #0 * 0 ≃ #0 * 0 + 0, by simp[Herbrand.eq_of_provable_equiv_0],
  have succ : 𝐈ₒₚₑₙ ⊢ ∏ ((Succ #1 * #0 ≃ #1 * #0 + #0) ⟶ (Succ #1 * Succ #0 ≃ #1 * Succ #0 + Succ #0)),
  { refine (generalize $ deduction.mp _),
    have : 𝐈ₒₚₑₙ +{ Succ #1 * #0 ≃ #1 * #0 + #0 } ⊢ Succ #1 * #0 ≃ #1 * #0 + #0, by simp,
    simp[Herbrand.eq_of_provable_equiv_0] at this ⊢,
    calc (Succ ♯1 * ♯0 + ♯1 : Herbrand (𝐈ₒₚₑₙ +{ Succ #1 * #0 ≃ #1 * #0 + #0 }) 0)
        = ♯1 * ♯0 + ♯0 + ♯1   : by rw[this]
    ... = ♯1 * ♯0 + (♯1 + ♯0) : by simp[add_assoc, add_comm]
    ... = ♯1 * ♯0 + ♯1 + ♯0   : by simp[add_assoc] },
  refine (generalize _), simp[fal_fn], exact ind ⨀ zero ⨀ succ
end

@[simp] lemma Lindenbaum.succ_mul (h₁ h₂ : Herbrand T i) : Succ h₁ * h₂ = h₁ * h₂ + h₂ :=
begin
  induction h₁ using fopl.Herbrand.ind_on with t, induction h₂ using fopl.Herbrand.ind_on with u,
  have : T^i ⊢ Succ t * u ≃ t * u + u,
    from provable.extend_pow (show 𝐈ₒₚₑₙ ⊢ Succ t * u ≃ t * u + u, by simpa[fal_fn] using succ_mul ⊚ t ⊚ u) i,
   simpa using Herbrand.eq_of_provable_equiv.mp this
end

lemma mul_commutative : 𝐈ₒₚₑₙ ⊢ ∀₁ x y, x * y ≃ y * x :=
begin
  have ind : 𝐈ₒₚₑₙ ⊢ (#0 * 0 ≃ 0 * #0) ⟶ ∏ ((#1 * #0 ≃ #0 * #1) ⟶ (#1 * Succ #0 ≃ Succ #0 * #1)) ⟶ ∏ (#1 * #0 ≃ #0 * #1),
    by simpa using @I_succ_induction (#1 * #0 ≃ #0 * #1) is_open (by simp[set.mem_def]),
  have zero : 𝐈ₒₚₑₙ ⊢ #0 * 0 ≃ 0 * #0, by simp[Herbrand.eq_of_provable_equiv_0],
  have succ : 𝐈ₒₚₑₙ ⊢ ∏ ((#1 * #0 ≃ #0 * #1) ⟶ (#1 * Succ #0 ≃ Succ #0 * #1)),
  { refine (generalize $ deduction.mp _), simp,
    have : 𝐈ₒₚₑₙ +{ #1 * #0 ≃ #0 * #1 } ⊢ #1 * #0 ≃ #0 * #1, by simp,
    simp[Herbrand.eq_of_provable_equiv_0] at this ⊢, simp[this] },
  refine (generalize _), simp[fal_fn], exact ind ⨀ zero ⨀ succ
end

lemma Lindenbaum.mul_commutative (h₁ h₂ : Herbrand T i) : h₁ * h₂ = h₂ * h₁ :=
begin
  induction h₁ using fopl.Herbrand.ind_on with t, induction h₂ using fopl.Herbrand.ind_on with u,
  have : T^i ⊢ t * u ≃ u * t,
    from provable.extend_pow (show 𝐈ₒₚₑₙ ⊢ t * u ≃ u * t, by simpa[fal_fn] using mul_commutative ⊚ t ⊚ u) i,
  simpa using Herbrand.eq_of_provable_equiv.mp this
end

lemma mul_add : 𝐈ₒₚₑₙ ⊢ ∀₁ x y z, x * (y + z) ≃ x * y + x * z :=
begin
  have ind : 𝐈ₒₚₑₙ ⊢ (#1 * (#0 + 0) ≃ #1 * #0 + #1 * 0) ⟶
                     ∏ ((#2 * (#1 + #0) ≃ #2 * #1 + #2 * #0) ⟶ (#2 * (#1 + Succ #0) ≃ #2 * #1 + #2 * Succ #0)) ⟶
                     ∏ (#2 * (#1 + #0) ≃ #2 * #1 + #2 * #0),
  by simpa using @I_succ_induction (#2 * (#1 + #0) ≃ #2 * #1 + #2 * #0) is_open (by simp[set.mem_def]),
  have zero : 𝐈ₒₚₑₙ ⊢ #1 * (#0 + 0) ≃ #1 * #0 + #1 * 0, by simp[Herbrand.eq_of_provable_equiv_0],
  have succ : 𝐈ₒₚₑₙ ⊢ ∏ ((#2 * (#1 + #0) ≃ #2 * #1 + #2 * #0) ⟶ (#2 * (#1 + Succ #0) ≃ #2 * #1 + #2 * Succ #0)),
  { refine (generalize $ deduction.mp _), simp, 
    have : 𝐈ₒₚₑₙ +{ #2 * (#1 + #0) ≃ #2 * #1 + #2 * #0 } ⊢ #2 * (#1 + #0) ≃ #2 * #1 + #2 * #0, by simp,
    simp[Herbrand.eq_of_provable_equiv_0] at this ⊢,
    simp[this, add_assoc] },
  refine (generalize $ generalize _), simp[fal_fn], exact ind ⨀ zero ⨀ succ
end

lemma Lindenbaum.mul_add (h₁ h₂ h₃ : Herbrand T i) : h₁ * (h₂ + h₃) = h₁ * h₂ + h₁ * h₃ :=
begin
  induction h₁ using fopl.Herbrand.ind_on with t₁,
  induction h₂ using fopl.Herbrand.ind_on with t₂,
  induction h₃ using fopl.Herbrand.ind_on with t₃,
  have : T^i ⊢ t₁ * (t₂ + t₃) ≃ t₁ * t₂ + t₁ * t₃,
    from provable.extend_pow (show 𝐈ₒₚₑₙ ⊢ t₁ * (t₂ + t₃) ≃ t₁ * t₂ + t₁ * t₃, by simpa[fal_fn] using mul_add ⊚ t₁ ⊚ t₂ ⊚ t₃) i,
  simpa using Herbrand.eq_of_provable_equiv.mp this
end

lemma mul_associative : 𝐈ₒₚₑₙ ⊢ ∀₁ x y z, x * y * z ≃ x * (y * z) :=
begin
  have ind : 𝐈ₒₚₑₙ ⊢ (#1 * #0 * 0 ≃ #1 * (#0 * 0)) ⟶
                     ∏ ((#2 * #1 * #0 ≃ #2 * (#1 * #0)) ⟶ (#2 * #1 * Succ #0 ≃ #2 * (#1 * Succ #0))) ⟶
                     ∏ (#2 * #1 * #0 ≃ #2 * (#1 * #0)),
  by simpa using @I_succ_induction (#2 * #1 * #0 ≃ #2 * (#1 * #0)) is_open (by simp[set.mem_def]),
  have zero : 𝐈ₒₚₑₙ ⊢ #1 * #0 * 0 ≃ #1 * (#0 * 0), by simp[Herbrand.eq_of_provable_equiv_0],
  have succ : 𝐈ₒₚₑₙ ⊢ ∏ ((#2 * #1 * #0 ≃ #2 * (#1 * #0)) ⟶ (#2 * #1 * Succ #0 ≃ #2 * (#1 * Succ #0))),
  { refine (generalize $ deduction.mp _),
    have : 𝐈ₒₚₑₙ +{ #2 * #1 * #0 ≃ #2 * (#1 * #0) } ⊢ #2 * #1 * #0 ≃ #2 * (#1 * #0), by simp,
    simp[Herbrand.eq_of_provable_equiv_0] at this ⊢, simp[this, Lindenbaum.mul_add] },
  refine (generalize $ generalize _), simp[fal_fn], exact ind ⨀ zero ⨀ succ
end

lemma Lindenbaum.mul_associative (h₁ h₂ h₃ : Herbrand T i) : h₁ * h₂ * h₃ = h₁ * (h₂ * h₃) :=
begin
  induction h₁ using fopl.Herbrand.ind_on with t₁,
  induction h₂ using fopl.Herbrand.ind_on with t₂,
  induction h₃ using fopl.Herbrand.ind_on with t₃,
  have : T^i ⊢ t₁ * t₂ * t₃ ≃ t₁ * (t₂ * t₃),
    from provable.extend_pow (show 𝐈ₒₚₑₙ ⊢ t₁ * t₂ * t₃ ≃ t₁ * (t₂ * t₃), by simpa[fal_fn] using mul_associative ⊚ t₁ ⊚ t₂ ⊚ t₃) i,
  simpa using Herbrand.eq_of_provable_equiv.mp this
end

lemma mul_one : 𝐈ₒₚₑₙ ⊢ ∀₁ x, x * 1 ≃ x :=
generalize (by simp[fal_fn, numeral_one_def, Herbrand.eq_of_provable_equiv_0])

@[simp] lemma Lindenbaum.mul_one (h : Herbrand T i) : h * 1 = h :=
by { simp[numeral_one_def],
  induction h using fopl.Herbrand.ind_on with t,
  have : T^i ⊢ t * Succ 0 ≃ t, from provable.extend_pow (show 𝐈ₒₚₑₙ ⊢ t * 1 ≃ t, by simpa[fal_fn, numeral_one_def] using mul_one ⊚ t) i,
  simpa using Herbrand.eq_of_provable_equiv.mp this }

instance Lindenbaum.comm_semigroup : comm_semigroup (Herbrand T i) :=
{ mul := (*),
  mul_assoc := Lindenbaum.mul_associative,
  mul_comm := Lindenbaum.mul_commutative }

instance Lindenbaum.distrib : distrib (Herbrand T i) :=
{ mul := (*), add := (+),
  left_distrib := Lindenbaum.mul_add,
  right_distrib := λ a b c, by simp[mul_comm (a + b), mul_comm a, mul_comm b, Lindenbaum.mul_add] }

lemma add_right_cancel : 𝐈ₒₚₑₙ ⊢ ∀₁ x y z, (x + z ≃ y + z) ⟶ (x ≃ y) :=
begin
  have ind : 𝐈ₒₚₑₙ ⊢ ((#1 + 0 ≃ #0 + 0) ⟶ (#1 ≃ #0)) ⟶
                     ∏ (((#2 + #0 ≃ #1 + #0) ⟶ (#2 ≃ #1)) ⟶ (#2 + Succ #0 ≃ #1 + Succ #0) ⟶ (#2 ≃ #1)) ⟶
                     ∏ ((#2 + #0 ≃ #1 + #0) ⟶ (#2 ≃ #1)),
  by simpa using @I_succ_induction ((#2 + #0 ≃ #1 + #0) ⟶ (#2 ≃ #1)) is_open (by simp[set.mem_def]),
  have zero : 𝐈ₒₚₑₙ ⊢ (#1 + 0 ≃ #0 + 0) ⟶ (#1 ≃ #0), by simp[Lindenbaum.le_of_provable_imply_0],
  have succ : 𝐈ₒₚₑₙ ⊢ ∏ (((#2 + #0 ≃ #1 + #0) ⟶ (#2 ≃ #1)) ⟶ (#2 + Succ #0 ≃ #1 + Succ #0) ⟶ (#2 ≃ #1)),
  { refine (generalize $ deduction.mp $ deduction.mp _), simp,
    have : 𝐈ₒₚₑₙ +{ (#2 + #0 ≃ #1 + #0) ⟶ (#2 ≃ #1) } +{ #2 + Succ #0 ≃ #1 + Succ #0 } ⊢ #2 + #0 ≃ #1 + #0,
      from deduction.mpr (by simp[Lindenbaum.le_of_provable_imply_0]),
    exact (show _ ⊢ (#2 + #0 ≃ #1 + #0) ⟶ (#2 ≃ #1), by simp) ⨀ this },
  refine (generalize $ generalize _), simp[fal_fn], exact ind ⨀ zero ⨀ succ
end

lemma Herbrand.add_right_cancel (h₁ h₂ h₃ : Herbrand T i) : h₁ + h₃ = h₂ + h₃ ↔ h₁ = h₂ :=
⟨λ h, begin
  induction h₁ using fopl.Herbrand.ind_on with t₁,
  induction h₂ using fopl.Herbrand.ind_on with t₂,
  induction h₃ using fopl.Herbrand.ind_on with t₃,
  have lmm₁ : T^i ⊢ t₁ + t₃ ≃ t₂ + t₃, from Herbrand.eq_of_provable_equiv.mpr (by simp[h]),
  have lmm₂ : T^i ⊢ (t₁ + t₃ ≃ t₂ + t₃) ⟶ (t₁ ≃ t₂),
    by simpa[fal_fn] using provable.extend_pow (add_right_cancel ⊚ t₁ ⊚ t₂ ⊚ t₃) i,
  exact Herbrand.eq_of_provable_equiv.mp (lmm₂ ⨀ lmm₁)
end, λ h, by simp[h]⟩

lemma Herbrand.add_left_cancel (h₁ h₂ h₃ : Herbrand T i) : h₃ + h₁ = h₃ + h₂ ↔ h₁ = h₂ :=
by simp[add_comm h₃, Herbrand.add_right_cancel]

@[simp] lemma Lindenbaum.add_right_cancel (h₁ h₂ h₃ : Herbrand T i) : (h₁ + h₃ ≃ h₂ + h₃ : Lindenbaum T i) = (h₁ ≃ h₂) :=
begin
  induction h₁ using fopl.Herbrand.ind_on with t₁,
  induction h₂ using fopl.Herbrand.ind_on with t₂,
  induction h₃ using fopl.Herbrand.ind_on with t₃,
  have : T^i ⊢ (t₁ + t₃ ≃ t₂ + t₃) ⟶ (t₁ ≃ t₂),
    by simpa[fal_fn] using provable.extend_pow (add_right_cancel ⊚ t₁ ⊚ t₂ ⊚ t₃) i,
  have : T^i ⊢ (t₁ + t₃ ≃ t₂ + t₃) ⟷ (t₁ ≃ t₂),
  { simp[iff_equiv, this],  refine (deduction.mp _),
    simp[Herbrand.eq_of_provable_equiv_0, rew_by_axiom₁] },
  simpa using Lindenbaum.eq_of_provable_equiv.mp this
end

lemma add_le_add : 𝐈ₒₚₑₙ ⊢ ∀₁ x y z, (x + z ≼ y + z) ⟷ (x ≼ y) :=
begin
  refine (generalize $ generalize $ generalize _), simp[fal_fn],
  suffices : 𝐈ₒₚₑₙ ⊢ ∐ (#0 + (#3 + #1) ≃ #2 + #1) ⟷ ∐ (#0 + #3 ≃ #2),
  { simpa[Lindenbaum.eq_top_of_provable_0, le_iff, add_pow] using this },
  simp[iff_equiv], split,
  { refine (imply_ex_of_fal_imply $ generalize $ deduction.mp $ use #0 _), simp[formula.pow_eq], 
    have : 𝐈ₒₚₑₙ +{ #0 + (#3 + #1) ≃ #2 + #1 } ⊢ #0 + (#3 + #1) ≃ #2 + #1, by simp,
    simp[Herbrand.eq_of_provable_equiv_0, ←add_assoc, Herbrand.add_right_cancel] at this ⊢, exact this },
  { refine (imply_ex_of_fal_imply $ generalize $ deduction.mp $ use #0 _), simp[formula.pow_eq],
    have : 𝐈ₒₚₑₙ +{ #0 + #3 ≃ #2 } ⊢ #0 + #3 ≃ #2, by simp,
    simp[Herbrand.eq_of_provable_equiv_0, ←add_assoc, Herbrand.add_right_cancel] at this ⊢, exact this }
end 

@[simp] lemma Lindenbaum.le_add_right_cancel (h₁ h₂ h₃ : Herbrand T i) : (h₁ + h₃ ≼ h₂ + h₃ : Lindenbaum T i) = (h₁ ≼ h₂) :=
begin
  induction h₁ using fopl.Herbrand.ind_on with t₁,
  induction h₂ using fopl.Herbrand.ind_on with t₂,
  induction h₃ using fopl.Herbrand.ind_on with t₃,
  have : T^i ⊢ (t₁ + t₃ ≼ t₂ + t₃) ⟷ (t₁ ≼ t₂),
    by simpa[fal_fn] using provable.extend_pow (add_le_add ⊚ t₁ ⊚ t₂ ⊚ t₃) i,
  simpa using Lindenbaum.eq_of_provable_equiv.mp this
end

lemma lt_equiv : 𝐈ₒₚₑₙ⁺ ⊢ ∀₁ x y, (x ≺ y) ⟷ ∃₁ z, (Succ z + x ≃ y) :=
begin
  refine (generalize $ generalize _), simp[fal_fn, ex_fn, iff_equiv], split,
  { suffices : 𝐈ₒₚₑₙ ⊢ (∐ (#0 + #2 ≃ #1)) ⟶ ⁻(#1 ≃ #0) ⟶ ∐ (Succ #0 + #2 ≃ #1),
    { 
      --have : 𝐈ₒₚₑₙ⁺ ⊢ ∐ (#0 + #2 ≃ #1) ⟶ ⁻(#1 ≃ #0) ⟶ ∐ (Succ #0 + #2 ≃ #1),
      simp[Lindenbaum.le_of_provable_imply_0],
     },
    refine (imply_ex_of_fal_imply $ generalize $ deduction.mp $ rew_of_eq (#0 + #2) 1 (eq_symm $ by simp) _),
    simp[formula.pow_eq],
    have zero : 𝐈ₒₚₑₙ +{ #0 + #2 ≃ #1 } ⊢ (#0 ≃ 0) ⟶ (#2 ≄ #0 + #2) ⟶ ∐ (Succ #0 + #3 ≃ #1 + #3),
    { refine (deduction.mp _), simp[Lindenbaum.le_of_provable_imply_0, rew_by_axiom₁] },
    have succ : 𝐈ₒₚₑₙ +{ #0 + #2 ≃ #1 } ⊢ (∃₁ y, #1 ≃ Succ y) ⟶ (#2 ≄ #0 + #2) ⟶ ∐ (Succ #0 + #3 ≃ #1 + #3),
    { refine (imply_ex_of_fal_imply $ generalize $ deduction.mp $ deduction.mp $ use #0 _), simp[←sf_dsb], 
      simp[Herbrand.eq_of_provable_equiv_0, rew_by_axiom₂] },
    exact case_of_ax (show 𝐈ₒₚₑₙ+{#0 + #2 ≃ #1} ⊢ (#0 ≃ 0) ⊔ ∃₁ y, (#1 ≃ Succ y), from (robinson.zero_or_succ #0).extend) zero succ },
  { refine (imply_ex_of_fal_imply $ generalize $ deduction.mp $ rew_of_eq (Succ #0 + #2) 1 (eq_symm $ by simp) _), simp,
    simp[Herbrand.le_iff_provable_le_0, Lindenbaum.eq_neg_of_provable_neg_0, -Lindenbaum.succ_add],
    have : ♯2 ≃ Succ (♯0 + ♯2) = ⊥, by simpa using Lindenbaum.add_right_cancel (0 : Herbrand (𝐈ₒₚₑₙ +{ Succ #0 + #2 ≃ #1 }) 0) (Succ ♯0) ♯2,
    simpa using this }
end

lemma Lindenbaum.lt_eq (h₁ h₂ : Herbrand T i) :
  (h₁ ≼ h₂ : Lindenbaum T i) ⊓ (h₁ ≃ h₂)ᶜ = ∐' (Succ ♯0 + h₁.pow ≃ h₂.pow : Lindenbaum T (i + 1)) :=
begin
  induction h₁ using fopl.Herbrand.ind_on with t,
  induction h₂ using fopl.Herbrand.ind_on with u,
  have : T^i ⊢ (t ≺ u) ⟷ ∐ (Succ #0 + t^1 ≃ u^1),
   by simpa[lessthan_def, fal_fn, ex_fn, subst_pow, term.pow_add] using provable.extend_pow (lt_equiv ⊚ t ⊚ u) i,
  simpa[lessthan_def] using Lindenbaum.eq_of_provable_equiv.mp this
end

lemma le_refl : 𝐈ₒₚₑₙ ⊢ ∀₁ x, x ≼ x :=
begin
  refine generalize _, simp,
  refine of_equiv (use 0 _) (equiv_symm (robinson.le_iff #0 #0).extend),
  simp[Herbrand.eq_of_provable_equiv_0]
end 

@[simp, refl] lemma Lindenbaum.le_refl (h : Herbrand T i) : h ≤ h :=
by { have : extend 𝐐 T, from extend.trans 𝐐 𝐈ₒₚₑₙ T,
     have : h ≤ 0 + h, by exactI robinson.Lindenbaum.le_add_self T i h 0, 
     simpa using this }

@[simp] lemma Lindenbaum.le_succ_refl (h : Herbrand T i) : h ≤ Succ h :=
by { have : extend 𝐐 T, from extend.trans 𝐐 𝐈ₒₚₑₙ T,
     have : h ≤ 1 + h, by exactI robinson.Lindenbaum.le_add_self T i h 1, 
     simpa[numeral_one_def] using this }

lemma le_transitive : 𝐈ₒₚₑₙ ⊢ ∀₁ x y z, (x ≼ y) ⟶ (y ≼ z) ⟶ (x ≼ z) :=
begin
  refine (generalize $ generalize $ generalize _), simp[fal_fn],
  suffices : 𝐈ₒₚₑₙ ⊢ ∐ (#0 + #3 ≃ #2) ⟶ ∐ (#0 + #2 ≃ #1) ⟶ ∐ (#0 + #3 ≃ #1),
  { simp[Lindenbaum.eq_top_of_provable_0, le_iff] at this ⊢, exact this },
  refine (imply_ex_of_fal_imply $ generalize $ deduction.mp $ imply_ex_of_fal_imply $ generalize $ deduction.mp $ use (#0 + #1) _),
  simp[←sf_dsb, formula.pow_eq],
  show 𝐈ₒₚₑₙ +{ #1 + #4 ≃ #3 } +{ #0 + #3 ≃ #2 } ⊢ #0 + #1 + #4 ≃ #2,
  by simp[Herbrand.eq_of_provable_equiv_0, rew_by_axiom₁_inv, rew_by_axiom₂_inv, add_assoc]
end

@[trans] lemma Lindenbaum.le_transitive {h₁ h₂ h₃ : Herbrand T i} : h₁ ≤ h₂ → h₂ ≤ h₃ → h₁ ≤ h₃ := λ le₁₂ le₂₃,
begin
  induction h₁ using fopl.Herbrand.ind_on with t₁,
  induction h₂ using fopl.Herbrand.ind_on with t₂,
  induction h₃ using fopl.Herbrand.ind_on with t₃,
  have le₁₂ : T^i ⊢ t₁ ≼ t₂, from Herbrand.le_iff_provable_le.mpr le₁₂,
  have le₂₃ : T^i ⊢ t₂ ≼ t₃, from Herbrand.le_iff_provable_le.mpr le₂₃,
  have : T^i ⊢ (t₁ ≼ t₂) ⟶ (t₂ ≼ t₃) ⟶ (t₁ ≼ t₃),
    by simpa[fal_fn] using provable.extend_pow le_transitive i ⊚ t₁ ⊚ t₂ ⊚ t₃, 
  exact Herbrand.le_iff_provable_le.mp (this ⨀ le₁₂ ⨀ le₂₃)
end

lemma add_lt_of_lt_of_lt : 𝐈ₒₚₑₙ ⊢ ∀₁ x y z v, (x ≺ y) ⟶ (z ≺ v) ⟶ (x + z ≺ y + v) :=
begin
  refine (generalize $ generalize $ generalize $ generalize _), simp[fal_fn],
  show 𝐈ₒₚₑₙ ⊢ (#3 ≺ #2) ⟶ (#1 ≺ #0) ⟶ (#3 + #1 ≺ #2 + #0),
  suffices : 𝐈ₒₚₑₙ ⊢ ∐ (Succ #0 + #4 ≃ #3) ⟶ ∐ (Succ #0 + #2 ≃ #1) ⟶ ∐ (Succ #0 + #4 + #2 ≃ #3 + #1),
  { simp[lessthan_def, Lindenbaum.eq_top_of_provable_0, Lindenbaum.lt_eq, add_pow, add_assoc] at this ⊢, simpa using this },
  refine (imply_ex_of_fal_imply $ generalize $ deduction.mp $ imply_ex_of_fal_imply $ generalize $ deduction.mp $ use (Succ #1 + #0) _),
  simp[←sf_dsb, formula.pow_eq],
  show 𝐈ₒₚₑₙ +{ Succ #1 + #5 ≃ #4 } +{ Succ #0 + #3 ≃ #2 } ⊢ Succ (Succ #1 + #0) + #5 + #3 ≃ #4 + #2,
  simp[Herbrand.eq_of_provable_equiv_0, rew_by_axiom₁_inv, rew_by_axiom₂_inv],
  calc    (♯1 + ♯0 + ♯5 + ♯3 : Herbrand (𝐈ₒₚₑₙ+{ Succ #1 + #5 ≃ #4 }+{ Succ #0 + #3 ≃ #2 }) 0) 
        = (♯1 + (♯0 + ♯5) + ♯3) : by simp[add_assoc]
    ... = (♯1 + (♯5 + ♯0) + ♯3) : by simp[add_comm]
    ... = ♯1 + ♯5 + (♯0 + ♯3)   : by simp[add_assoc]
end

lemma eq_or_succ_le_of_le : 𝐈ₒₚₑₙ ⊢ ∀₁ x y, (x ≼ y) ⟶ (x ≃ y) ⊔ (Succ x ≼ y) :=
begin
  refine (generalize $ generalize _), simp[fal_fn],
  suffices : 𝐈ₒₚₑₙ ⊢ ∐ (#0 + #2 ≃ #1) ⟶ (#1 ≃ #0) ⊔ ∐ (#0 + Succ #2 ≃ #1),
  {  simp[Lindenbaum.eq_top_of_provable_0, le_iff] at this ⊢, exact this },
  refine (imply_ex_of_fal_imply $ generalize _), simp[formula.pow_eq],
  show 𝐈ₒₚₑₙ ⊢ (#0 + #2 ≃ #1) ⟶ (#2 ≃ #1) ⊔ ∐ (#0 + Succ #3 ≃ #2),
  have zero : 𝐈ₒₚₑₙ ⊢ (#0 ≃ 0) ⟶ (#0 + #2 ≃ #1) ⟶ (#2 ≃ #1) ⊔ ∐ (#0 + Succ #3 ≃ #2),
  { refine (deduction.mp $ deduction.mp _),
    simp[Lindenbaum.eq_top_of_provable_0, rew_by_axiom₁_inv, rew_by_axiom₂] },
  have succ : 𝐈ₒₚₑₙ ⊢ (∃₁ y, #1 ≃ Succ y) ⟶ (#0 + #2 ≃ #1) ⟶ (#2 ≃ #1) ⊔ ∐ (#0 + Succ #3 ≃ #2),
  { refine (imply_ex_of_fal_imply $ generalize $ deduction.mp $ deduction.mp $ imply_or_right _ _ ⨀ use #0 _),
    simp[Lindenbaum.eq_top_of_provable_0, rew_by_axiom₁_inv, rew_by_axiom₂] },
  exact case_of_ax (show 𝐈ₒₚₑₙ ⊢ (#0 ≃ 0) ⊔ ∃₁ y, (#1 ≃ Succ y), from (robinson.zero_or_succ #0).extend) zero succ
end

lemma le_or_ge : 𝐈ₒₚₑₙ ⊢ ∀₁ x y, (x ≼ y) ⊔ (y ≼ x) :=
begin
  have ind : 𝐈ₒₚₑₙ ⊢ (#0 ≼ 0) ⊔ (0 ≼ #0) ⟶
                  ∏ ((#1 ≼ #0) ⊔ (#0 ≼ #1) ⟶ (#1 ≼ Succ #0) ⊔ (Succ #0 ≼ #1)) ⟶
                  ∏ (#1 ≼ #0) ⊔ (#0 ≼ #1),
  by simpa using @I_succ_induction ((#1 ≼ #0) ⊔ (#0 ≼ #1)) is_open (by simp[set.mem_def]),
  have zero : 𝐈ₒₚₑₙ ⊢ (#0 ≼ 0) ⊔ (0 ≼ #0), from (imply_or_right _ _ ⨀ (by simp[Herbrand.le_iff_provable_le_0])),
  have succ : 𝐈ₒₚₑₙ ⊢ ∏ ((#1 ≼ #0) ⊔ (#0 ≼ #1) ⟶ (#1 ≼ Succ #0) ⊔ (Succ #0 ≼ #1)),
  { refine generalize _, simp, 
    have orl : 𝐈ₒₚₑₙ ⊢ (#1 ≼ #0) ⟶ (#1 ≼ Succ #0) ⊔ (Succ #0 ≼ #1),
    { refine (deduction.mp $ imply_or_left _ _ ⨀ _),
      have : 𝐈ₒₚₑₙ +{ #1 ≼ #0 } ⊢ #1 ≼ #0, by simp,
      simp[Herbrand.le_iff_provable_le_0] at this ⊢,
      refine Lindenbaum.le_transitive this (by simp) },
    have orr : 𝐈ₒₚₑₙ ⊢ (#0 ≼ #1) ⟶ (#1 ≼ Succ #0) ⊔ (Succ #0 ≼ #1),
    { refine (deduction.mp _),
      have eq      : 𝐈ₒₚₑₙ +{ #0 ≼ #1 } ⊢ (#0 ≃ #1) ⟶ (#1 ≼ Succ #0) ⊔ (Succ #0 ≼ #1),
      { refine (deduction.mp $ imply_or_left _ _ ⨀ _), simp[Herbrand.le_iff_provable_le_0, rew_by_axiom₁] },
      have succ_le : 𝐈ₒₚₑₙ +{ #0 ≼ #1 } ⊢ (Succ #0 ≼ #1) ⟶ (#1 ≼ Succ #0) ⊔ (Succ #0 ≼ #1), by simp[Lindenbaum.le_of_provable_imply_0],
      have : 𝐈ₒₚₑₙ +{ #0 ≼ #1 } ⊢ (#0 ≃ #1) ⊔ (Succ #0 ≼ #1), 
        from deduction.mpr (show 𝐈ₒₚₑₙ ⊢ (#0 ≼ #1) ⟶ (#0 ≃ #1) ⊔ (Succ #0 ≼ #1), by simpa[fal_fn] using eq_or_succ_le_of_le ⊚ #0 ⊚ #1),
      exact case_of_ax this eq succ_le },
    exact or_imply _ _ _ ⨀ orl ⨀ orr },
  refine (generalize _), simp[fal_fn], exact ind ⨀ zero ⨀ succ
end

lemma lt_mul_of_nonzero_of_lt :
  𝐈ₒₚₑₙ ⊢ ∀₁ x y z, (x ≺ y) ⟶ (z ≄ 0) ⟶ (x * z ≺ y * z) :=
begin
  have ind : 𝐈ₒₚₑₙ ⊢
       ((#1 ≺ #0) ⟶ ((0 : term LA) ≄ 0) ⟶ (#1 * 0 ≺ #0 * 0)) ⟶
    ∏ (((#2 ≺ #1) ⟶ (#0 ≄ 0) ⟶ (#2 * #0 ≺ #1 * #0)) ⟶ (#2 ≺ #1) ⟶ (Succ #0 ≄ 0) ⟶ (#2 * Succ #0 ≺ #1 * Succ #0)) ⟶
    ∏ ((#2 ≺ #1) ⟶ (#0 ≄ 0) ⟶ (#2 * #0 ≺ #1 * #0)),
  by simpa[lessthan_def] using @I_succ_induction ((#2 ≺ #1) ⟶ (#0 ≄ 0) ⟶ (#2 * #0 ≺ #1 * #0)) is_open (by simp[lessthan_def, set.mem_def]),
  have zero : 𝐈ₒₚₑₙ ⊢ (#1 ≺ #0) ⟶ ((0 : term LA) ≄ 0) ⟶ (#1 * 0 ≺ #0 * 0), by simp[Lindenbaum.eq_top_of_provable_0],
  have succ : 𝐈ₒₚₑₙ ⊢ ∏ (((#2 ≺ #1) ⟶ (#0 ≄ 0) ⟶ (#2 * #0 ≺ #1 * #0)) ⟶ (#2 ≺ #1) ⟶ (Succ #0 ≄ 0) ⟶ (#2 * Succ #0 ≺ #1 * Succ #0)),
  { refine (generalize $ deduction.mp $ deduction.mp $ deduction.mp _), simp[-iff_and],
    have zero : 𝐈ₒₚₑₙ +{ (#2 ≺ #1) ⟶ (#0 ≄ 0) ⟶ (#2 * #0 ≺ #1 * #0) } +{ #2 ≺ #1 } +{ Succ #0 ≄ 0 } ⊢ (#0 ≃ 0) ⟶ (#2 * Succ #0 ≺ #1 * Succ #0),
    { refine (deduction.mp $ rew_of_eq 0 0 (by simp) _),
      have : 𝐈ₒₚₑₙ +{ (#2 ≺ #1) ⟶ (#0 ≄ 0) ⟶ (#2 * #0 ≺ #1 * #0) } +{ #2 ≺ #1 } +{ Succ #0 ≄ 0 }+{ #0 ≃ 0 } ⊢  #2 ≺ #1, by simp,
      simp[lessthan_def, Herbrand.le_iff_provable_le_0, Lindenbaum.eq_neg_of_provable_neg_0] at this ⊢, exact this },
    have nonzero : 𝐈ₒₚₑₙ +{ (#2 ≺ #1) ⟶ (#0 ≄ 0) ⟶ (#2 * #0 ≺ #1 * #0) } +{ #2 ≺ #1 } +{ Succ #0 ≄ 0 } ⊢ (#0 ≄ 0) ⟶ (#2 * Succ #0 ≺ #1 * Succ #0),
    { refine (deduction.mp _),
      have lt : 𝐈ₒₚₑₙ +{ (#2 ≺ #1) ⟶ (#0 ≄ 0) ⟶ (#2 * #0 ≺ #1 * #0) } +{ #2 ≺ #1 } +{ Succ #0 ≄ 0 } +{ #0 ≄ 0 } ⊢ #2 * #0 ≺ #1 * #0,
        from (show _ ⊢ (#2 ≺ #1) ⟶ (#0 ≄ 0) ⟶ (#2 * #0 ≺ #1 * #0), by simp) ⨀ (by simp) ⨀ (by simp),
      have : 𝐈ₒₚₑₙ ⊢ (#2 * #0 ≺ #1 * #0) ⟶ (#2 ≺ #1) ⟶ (#2 * #0 + #2 ≺ #1 * #0 + #1),
        by simpa[lessthan_def, fal_fn] using add_lt_of_lt_of_lt ⊚ (#2 * #0) ⊚ (#1 * #0) ⊚ #2 ⊚ #1, 
      have : 𝐈ₒₚₑₙ +{ (#2 ≺ #1) ⟶ (#0 ≄ 0) ⟶ (#2 * #0 ≺ #1 * #0) } +{ #2 ≺ #1 } +{ Succ #0 ≄ 0 } +{ #0 ≄ 0 } ⊢ #2 * #0 + #2 ≺ #1 * #0 + #1,
        from this.extend ⨀ lt ⨀ (by simp),
      simp[lessthan_def, Lindenbaum.eq_top_of_provable_0] at this ⊢, exact this },
    refine cases_of _ _ zero nonzero },
  refine (generalize $ generalize _), simp[fal_fn], exact ind ⨀ zero ⨀ succ
end

lemma mul_right_cancel_of_nonzero : 𝐈ₒₚₑₙ ⊢ ∀₁ x y z, (z ≄ 0) ⟶ (x * z ≃ y * z) ⟶ (x ≃ y) :=
begin
  refine (generalize $ generalize $ generalize _), simp[fal_fn],
  suffices : 𝐈ₒₚₑₙ ⊢ (#0 ≄ 0) ⟶ (#2 ≄ #1) ⟶ (#2 * #0 ≄ #1 * #0),
  {  simp[Lindenbaum.eq_top_of_provable_0] at this ⊢, simpa[sup_comm] using this },
  have : 𝐈ₒₚₑₙ ⊢ ∀₁ x y z, (x ≺ y) ⟶ (z ≄ 0) ⟶ (x * z ≺ y * z), from lt_mul_of_nonzero_of_lt,
  have orl : 𝐈ₒₚₑₙ ⊢ (#1 ≼ #2) ⟶ ⁻(#0 ≃ 0) ⟶ ⁻(#2 ≃ #1) ⟶ ⁻(#2 * #0 ≃ #1 * #0),
  { refine (deduction.mp $ deduction.mp $ deduction.mp $ ne_symm _),
    have : 𝐈ₒₚₑₙ +{ #1 ≼ #2 } +{ #0 ≄ 0 } +{ #2 ≄ #1 } ⊢ _, from provable.extend (this ⊚ #1 ⊚ #2 ⊚ #0), 
    have := this ⨀ (by {simp[lessthan_def, fal_fn], refine ne_symm (by simp) }) ⨀ (by simp[fal_fn]),
    simp[lessthan_def, fal_fn] at this, exact this.2 },
  have orr : 𝐈ₒₚₑₙ ⊢ (#2 ≼ #1) ⟶ ⁻(#0 ≃ 0) ⟶ ⁻(#2 ≃ #1) ⟶ ⁻(#2 * #0 ≃ #1 * #0),
  { refine (deduction.mp $ deduction.mp $ deduction.mp _),
    have : 𝐈ₒₚₑₙ +{ #2 ≼ #1 } +{ #0 ≄ 0 } +{ #2 ≄ #1 } ⊢ _, from provable.extend (this ⊚ #2 ⊚ #1 ⊚ #0), 
    have := this ⨀ (by simp[lessthan_def, fal_fn]) ⨀ (by simp[fal_fn]),
    simp[lessthan_def, fal_fn] at this, exact this.2 },
  refine case_of_ax (show 𝐈ₒₚₑₙ ⊢ (#1 ≼ #2) ⊔ (#2 ≼ #1), by simpa[fal_fn] using le_or_ge ⊚ #1 ⊚ #2) orl orr
end

lemma one_divides : 𝐈ₒₚₑₙ ⊢ ∀₁ x, 1 ⍭ x :=
begin
  simp[divides_def, fal_fn, numeral_one_def],
  refine (generalize $ use #1 _), 
  simp[Herbrand.eq_of_provable_equiv_0]
end

lemma divides_self : 𝐈ₒₚₑₙ ⊢ ∀₁ x, x ⍭ x :=
begin
  simp[divides_def, fal_fn, numeral_one_def],
  refine (generalize $ use (Succ 0) _), 
  simp[Herbrand.eq_of_provable_equiv_0]
end

lemma divides_zero : 𝐈ₒₚₑₙ ⊢ ∀₁ x, x ⍭ 0 :=
begin
  simp[divides_def, fal_fn],
  refine (generalize $ use 0 _), 
  simp[Herbrand.eq_of_provable_equiv_0]
end

lemma divides_trans : 𝐈ₒₚₑₙ ⊢ ∀₁ x y z, (x ⍭ y) ⟶ (y ⍭ z) ⟶ (x ⍭ z) :=
begin
  simp[divides_def, fal_fn],
  refine (generalize $ generalize $ generalize $
    imply_ex_of_fal_imply $ generalize $ deduction.mp $
    imply_ex_of_fal_imply $ generalize $ deduction.mp $ use (#0 * #1) _),
  simp[formula.pow_eq, ←sf_dsb],
  show 𝐈ₒₚₑₙ +{ #1 * #5 ≃ #4 } +{ #0 * #4 ≃ #3 } ⊢ #0 * #1 * #5 ≃ #3,
  simp[Herbrand.eq_of_provable_equiv_0, rew_by_axiom₁_inv, rew_by_axiom₂_inv, mul_assoc]
end

end Iopen
/--/ₒ
def 


lemma add_symm : 𝐈ₒₚₑₙ ⊢ ∀₁ x y, (x + y ≃ y + x) :=
begin
  refine (generalize _), simp[fal_fn],
  have zero : 𝐈ₒₚₑₙ ⊢ (#0 ≃ 0) ⟶ ∏ (#1 + #0 ≃ #0 + #1),
  { refine (deduction.mp $ generalize _), simp[←sf_dsb, Herbrand.eq_of_provable_equiv_0, rew_by_axiom₁] },
  have succ : 𝐈ₒₚₑₙ ⊢ (∃₁ y, #1 ≃ Succ y) ⟶ ∏ (#1 + #0 ≃ #0 + #1),
  { refine (imply_ex_of_fal_imply $ generalize $ deduction.mp $ rew_of_eq (Succ #0) 1 (by simp) $ generalize _), simp[formula.pow_eq, ←sf_dsb],
    suffices : 𝐈ₒₚₑₙ ⊢ Succ #1 + #0 ≃ #0 + Succ #1, by simp[this],
     
     }
end




def Ind {C : theory LA} : Lindenbaum 𝐈C 1 → Prop := λ l, ∃ p, p ∈ C ∧ l = ⟦p⟧ᴸ

lemma Ind_mem (p : formula LA) : Ind (⟦p⟧ᴸ : Lindenbaum 𝐈C 1) → (⟦peano_induction p⟧ᴸ : Lindenbaum 𝐈C 0) = ⊤ :=
begin
  simp[Ind], 
  intros p0 h eqn, 
  have : 𝐈C ⊢ succ_induction p0,
  {have := provable.AX (succ_induction_axiom.ind h), exact this },
  simp[@Lindenbaum.provable_top_iff0] at *,
  have eqn : classical_logic.to_quo p = classical_logic.to_quo p0, from equiv_eq_top_iff.mp eqn,
  have : (⟦peano_induction p⟧ᴸ : Lindenbaum 𝐈C 0) = ⟦peano_induction p0⟧ᴸ,
  { simp[succ_induction, Lindenbaum.pow_eq, Lindenbaum.subst_eq, eqn], },
  simp*
end

lemma Lindenbaum_induction 
  (l : Lindenbaum 𝐈C 1) (m : Lindenbaum 𝐈C 0)
  (h : Ind l)
  (zero : m ≤ 0 ⊳ l)
  (succ : m.pow ≤ (♯0 ⊳ l.pow)ᶜ ⊔ (Succ ♯0) ⊳ l.pow) : m ≤ ∏ l :=
begin
  induction l using fopl.Lindenbaum.ind_on with p,
  have P := (provable_top_iff0.mpr (Ind_mem _ h)),
  have trn : (0 : Herbrand 𝐈C 0) ⊳ ⟦p⟧ᴸ ⊓ ∏ ((♯0 ⊳ pow ⟦p⟧ᴸ)ᶜ ⊔ (Succ ♯0) ⊳ pow ⟦p⟧ᴸ) ≤ ∏ ⟦p⟧ᴸ,
  { simp[succ_induction, Lindenbaum.subst_eq, Lindenbaum.pow_eq, compl_sup_iff_le,
    le_of_provable_imply_0, Herbrand.var_eq] at P, refine P },
  have succ' : m ≤ ∏ ((♯0 ⊳ pow ⟦p⟧ᴸ)ᶜ ⊔ (Succ ♯0) ⊳ pow ⟦p⟧ᴸ),
    from Lindenbaum.proper.pow_le_le_fal succ,
  have : m ≤ 0 ⊳ ⟦p⟧ᴸ ⊓ ∏ ((♯0 ⊳ pow ⟦p⟧ᴸ)ᶜ ⊔ (Succ ♯0) ⊳ pow ⟦p⟧ᴸ), 
    from le_inf zero succ',
  exact le_trans this trn
end

lemma Lindenbaum_induction_top {p : formula LA} (l : Lindenbaum 𝐈C 1)
  (h : Ind l)
  (zero : 0 ⊳ l = ⊤)
  (succ : ♯0 ⊳ l.pow ≤ (Succ ♯0) ⊳ l.pow) : (∏ l : Lindenbaum 𝐈C 0) = ⊤ :=
begin
  induction l using fopl.Lindenbaum.ind_on with p,
  have P := (provable_top_iff0.mpr (Ind_mem _ h)),
  have : (0 : Herbrand 𝐈C 0) ⊳ ⟦p⟧ᴸ ⊓ ∏ ((♯0 ⊳ pow ⟦p⟧ᴸ)ᶜ ⊔ (Succ ♯0) ⊳ pow ⟦p⟧ᴸ) ≤ ∏ ⟦p⟧ᴸ,
  { simp[succ_induction, Lindenbaum.subst_eq, Lindenbaum.pow_eq, compl_sup_iff_le,
    le_of_provable_imply_0, Herbrand.var_eq] at P, exact P },
  simp[zero, succ] at this,
  have eqn : (♯0 ⊳ pow ⟦p⟧ᴸ)ᶜ ⊔ (Succ ♯0) ⊳ pow ⟦p⟧ᴸ = ⊤,
    from ((♯0 ⊳ pow ⟦p⟧ᴸ).compl_sup_iff_le ((Succ ♯0) ⊳ pow ⟦p⟧ᴸ)).mpr succ,
  simp[eqn] at this, exact this
end

def Lindenbaum.bd_fal {T : theory LA} (l : Lindenbaum T (i + 1)) (h : Herbrand T i) : Lindenbaum T i := ∏ ((♯0 ≼ h.pow)ᶜ ⊔ l)
def Lindenbaum.bd_ex {T : theory LA} (l : Lindenbaum T (i + 1)) (h : Herbrand T i) : Lindenbaum T i := ∐ ((♯0 ≼ h.pow) ⊓ l)

notation `∏_{≼ `:95 h `} ` l :90 := Lindenbaum.bd_fal l h 
notation `∐_{≼ `:95 h `} ` l :90 := Lindenbaum.bd_ex l h 

theorem collection (p : formula LA) [proper 0 (𝚺⁰1)] :
  𝐈𝚺⁰1 ⊢ ([∏ ≼ #0] ∐ p) ⟶ ∐ [∏ ≼ #1] [∐ ≼ #1] ((p^3).rew ı[4 ⇝ #0]).rew ı[3 ⇝ #1] :=
begin
  simp[le_of_provable_imply_0, bounded_fal, bounded_ex, Lindenbaum.pow_eq p, Herbrand.subst_eq, Lindenbaum.subst_eq],
  suffices : ∀ l : Lindenbaum 𝐐+𝐈𝚺⁰1 2,
    ∏_{≼ ♯1} ∐ l ≤ ∐ ∏_{≼ ♯2} ∐_{≼ ♯2} (♯1 ⊳ ♯0 ⊳ l.pow.pow.pow),
  { sorry },
  intros l,
  have : ∏_{≼ ♯1} ∐ l ≤ ∏ ∏ ((♯0 ≼ ♯1)ᶜ ⊔ ∐ ∏_{≼ ♯1} ∐_{≼ ♯1} l.pow.pow.pow),
  { refine Lindenbaum_induction _ _ _ _ _; sorry }
  
end

theorem collection (p : formula LA) [proper 0 (𝚺⁰1)] : 𝐐+𝐈𝚺⁰1 ⊢ ([∏ ≼ #0] ∐ p) ⟶ ∐ [∏ ≼ #1] [∐ ≼ #1] p :=
begin
  refine deduction.mp _,
  have : ∀ n, ∃ m, (((ı[0 ⇝ #0] ^ 1) ^ 1) ^ 1) m = (#n : term LA) :=
    (rewriting_sf_perm $ rewriting_sf_perm $ rewriting_sf_perm $ slide_perm _ #0), 
  rcases formula.total_rew_inv p this with ⟨q, e_q⟩,
  suffices : 𝐐+𝐈𝚺⁰1+{[∏ ≼ #0] ∐ p} ⊢ ∏ ∏ ((#0 ≼ #1) ⟶ ∐ [∏ ≼ #1] [∐ ≼ #1] q),
  { have := (this.fal_subst #0).fal_subst #0,
    simp[e_q, formula.nested_rew, rewriting_sf_itr.pow_add, subst_pow] at this,
    have eqn : (λ (x : ℕ), term.rew ı[3 ⇝ #3] (ı[4 ⇝ #4] x) : ℕ → term LA) = 
      (λ x, if x < 4 then #x else if 4 < x then #(x - 2) else #3 ),
    { funext x, have C : x < 4 ∨ x = 4 ∨ 4 < x := trichotomous x 4,
      cases C, simp[C], { by_cases C₂ : x < 3, simp[C₂], simp[show x = 3, by omega] },
      cases C; simp[C], 
      { simp[show ¬x < 4, from asymm C, show 3 < x - 1, from nat.lt_sub_left_of_add_lt C, ı],
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
