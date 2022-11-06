import FOL.class_of_formulae FOL.extend

namespace fol
open formula
namespace arithmetic
open logic logic.Theory axiomatic_classical_logic' axiomatic_classical_logic
open_locale logic_symbol

variables {L L' : language.{0}}

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
variables {L} [LA'.language_translation_coe L]

instance LA_ltc_L : LA.language_translation_coe L := language.language_translation_coe.comp LA LA' L

instance additional_ltc_L : additional.language_translation_coe L := language.language_translation_coe.comp additional LA' L

instance commutes_LA : language.commutes LA LA' L := ⟨by refl⟩

instance commutes_additional : language.commutes additional LA' L := ⟨by refl⟩

def lt (t u : term L) : formula L :=
app ((coe : LA'.pr 2 → L.pr 2) (sum.inr additional_pr.lt)) ‹t, u›

def dvd (t u : term L) : formula L :=
app ((coe : LA'.pr 2 → L.pr 2) (sum.inr additional_pr.dvd)) ‹t, u›

def prime (t : term L) : formula L := app ((coe : LA'.pr 1 → L.pr 1) (sum.inr additional_pr.prime)) ‹t›

notation t ` is_prime`:80 := prime t

instance lt_abb : abberavation₂ (@lt L _) := { map_rew := by simp[lt], arity := by simp[lt] }

instance dvd_abb : abberavation₂ (@dvd L _) := { map_rew := by simp[dvd], arity := by simp[dvd] }

instance is_prime_abb : abberavation₁ (@prime L _) := { map_rew := by simp[prime], arity := by simp[prime] }

end additional

local infix ` ≺ `:50 := additional.lt

local infix ` ⍭ `:50 := additional.dvd

inductive robinson : Theory LA
| q1 : robinson ∀₁ x, 0 ≠' Succ x
| q2 : robinson ∀₁ x, ∀₁ y, ((Succ x =' Succ y) ⟶ (x =' y))
| q3 : robinson ∀₁ x, ((x =' 0) ⊔ ∃₁ y, x =' Succ y)
| q4 : robinson ∀₁ x, x + 0 =' x
| q5 : robinson ∀₁ x y, x + Succ y =' Succ (x + y)
| q6 : robinson ∀₁ x, x * 0 =' 0
| q7 : robinson ∀₁ x y, x * Succ y =' x * y + x
| q8 : robinson ∀₁ x y, ((x ≼ y) ⟷ ∃₁ z, z + x =' y)

notation `𝐐` := robinson

instance : closed_Theory 𝐐 := ⟨λ p h, by cases h; simp[is_sentence, lrarrow_def, formula.ex, formula.and, fal_fn, ex_fn]⟩

namespace additional

instance addditional_predicate : additional.predicate := ⟨λ n, pempty.is_empty⟩

@[simp] def df_pr : Π {n} (r : additional.pr n), formula LA
| 2 additional_pr.lt := ((#0 : term LA) ≼ #1) ⊓ ((#0 : term LA) ≠' #1)
| 2 additional_pr.dvd := ∃. (#0 * #1 =' #2)
| 1 additional_pr.prime := ∃. (#0 + 1 =' #1) ⊓ ∀. (∃. (#0 * #2 =' #1) ⟶ (#0 =' 1) ⊔ (#0 =' #1))

@[reducible] def defs : LA.definitions additional :=
{ df_fn := λ n f, by exfalso; exact is_empty.false f,
  hdf_fn := λ n f, by exfalso; exact is_empty.false f,
  df_pr := @df_pr,
  hdf_pr := λ n r, by rcases r; simp[df_pr, numeral_one_def] }

variables [LA'.language_translation_coe L] (T : Theory L) [lextend defs.thy T] {i : ℕ}

@[simp] lemma thy.lt (x y) : T ⊢ (x ≺ y) ⟷ (x ≼ y) ⊓ (x ≠' y) :=
by simpa[fal_fn] using defs.pr' T additional_pr.lt ‹x, y›

@[simp] lemma thy.dvd (x y) : T ⊢ (x ⍭ y) ⟷ ∃. (#0 * x^1 =' y^1) :=
by simpa[fal_fn, ex_fn] using defs.pr' T additional_pr.dvd ‹x, y›

variables {T}

def Herbrand.lt (h₁ h₂ : Herbrand T i) : Lindenbaum T i :=
Lindenbaum.predicate_of ((coe : LA'.pr 2 → L.pr 2) (sum.inr additional_pr.lt)) ‹h₁, h₂›

infix ` ≺' `:50 := Herbrand.lt

@[simp] lemma Lindenbaum.lt_def (v) :
  Lindenbaum.predicate_of ((coe : LA'.pr 2 → L.pr 2) (sum.inr additional_pr.lt)) v = (v 0 ≺' v 1 : Lindenbaum T i) := rfl

lemma Lindenbaum.lt_eq (h₁ h₂ : Herbrand T i) : (h₁ ≺' h₂) = (h₁ ≼ h₂) ⊓ (h₁ =' h₂)ᶜ :=
by induction h₁ using fol.Herbrand.ind_on with t;
   induction h₂ using fol.Herbrand.ind_on with u;
   simpa[lt] using Lindenbaum.eq_of_provable_equiv.mp (thy.lt _ t u)

def Herbrand.dvd (h₁ h₂ : Herbrand T i) : Lindenbaum T i :=
Lindenbaum.predicate_of ((coe : LA'.pr 2 → L.pr 2) (sum.inr additional_pr.dvd)) ‹h₁, h₂›

infix ` ⍭' `:50 := Herbrand.dvd

@[simp] lemma Lindenbaum.dvd_def (v) :
  Lindenbaum.predicate_of ((coe : LA'.pr 2 → L.pr 2) (sum.inr additional_pr.dvd)) v = (v 0 ⍭' v 1 : Lindenbaum T i) := rfl

lemma Lindenbaum.dvd_eq (h₁ h₂ : Herbrand T i) : (h₁ ⍭' h₂) = ∃' (♯0 * h₁.pow =' h₂.pow : Lindenbaum T (i + 1)) :=
by induction h₁ using fol.Herbrand.ind_on with t;
   induction h₂ using fol.Herbrand.ind_on with u;
   simpa[dvd] using Lindenbaum.eq_of_provable_equiv.mp (thy.dvd _ t u)

end additional

namespace Ind

section
variables [LA.language_translation_coe L]

def succ_induction (p : formula L) : formula L := ∀.* (p.rew (0 ⌢ ı) ⟶ ∀. (p ⟶ p.rew ((Succ #0) ⌢ (λ x, #(x+1)))) ⟶ ∀. p)

def test (p : formula L) : formula L := p.rew (0 ⌢ ı)

@[simp] lemma succ_induction_sentence (p : formula L) : is_sentence (succ_induction p) := by simp[succ_induction]

def succ_induction_axiom (C : Theory LA) : Theory LA := 𝐐 ∪ (succ_induction '' C)

prefix `𝐈`:max := succ_induction_axiom

@[reducible] def peano : Theory LA := 𝐈set.univ

notation `𝐏𝐀` := peano

instance {C : Theory LA} : closed_Theory 𝐈C := 
⟨λ p h, by { rcases h with (h | ⟨p, hp, rfl⟩), { refine closed_Theory.cl h }, { simp[succ_induction] } }⟩

def collection (p : formula L) : formula L :=
  ∀₁ u, (∀₁ x ≼ᵇ u, ∃₁ y, p.rew ı-{2}) ⟶ (∃₁ v, ∀₁ x ≼ᵇ u, ∃₁ y ≼ᵇ v, p.rew ı-{2}-{2})

def collection_axiom (C : Theory LA) : Theory LA := 𝐐 ∪ (collection '' C)

prefix `𝐁`:max := collection_axiom

end 

section
variables [LA'.language_translation_coe L]

def order_induction (p : formula L) : formula L := (∀₁ x, ((∀₁ y ≺ᵇ x, p.rew ı-{1}) ⟶ p)) ⟶ ∀₁ x, p

def order_induction_axiom (C : Theory LA') : Theory LA' := ↑𝐐 ∪ (order_induction '' C)

prefix `𝐈′`:max := order_induction_axiom

end

@[simp] lemma Q_ss_I {C} : 𝐐 ⊆ 𝐈C := by simp[succ_induction_axiom]

instance extend_Q_I (C : Theory LA) : extend 𝐐 𝐈C := ⟨λ p h, weakening Q_ss_I h⟩

instance extend_ax₁ (C : Theory LA) (p : formula LA) : extend 𝐐 (𝐈C +{ p }) :=
Theory.extend_of_inclusion (λ p mem, by simp[Q_ss_I mem])

instance extend_ax₂ (C : Theory LA) (p q : formula LA) : extend 𝐐 (𝐈C +{ p }+{ q }) :=
Theory.extend_of_inclusion (λ p mem, by simp[Q_ss_I mem])

instance extend_ax₃ (C : Theory LA) (p q r : formula LA) : extend 𝐐 (𝐈C +{ p }+{ q }+{ r }) :=
Theory.extend_of_inclusion (λ p mem, by simp[Q_ss_I mem])

instance extend_ax₄ (C : Theory LA) (p q r s : formula LA) : extend 𝐐 (𝐈C +{ p }+{ q }+{ r }+{ s }) :=
Theory.extend_of_inclusion (λ p mem, by simp[Q_ss_I mem])

end Ind

namespace robinson
open Herbrand Lindenbaum provable
variables {L} [LA.language_translation_coe L] (Q : Theory L) [lextend 𝐐 Q] (i : ℕ)

@[simp] lemma zero_ne_succ (t : term L) : Q ⊢ 0 ≠' Succ t :=
by { have : Q ⊢ ∀₁ x, 0 ≠' Succ x, by simpa[fal_fn] using provable.lextend (by_axiom robinson.q1) Q,
     simpa using this ⊚ t }

@[simp] lemma Lindembaum.zero_ne_succ (h : Herbrand Q i) : 0 =' Succ h = (⊥ : Lindenbaum Q i) :=
by { induction h using fol.Herbrand.ind_on with t,
     simpa[Lindenbaum.eq_neg_of_provable_neg_0] using zero_ne_succ (Q^i) t }

@[simp] lemma Lindenbaum.succ_ne_zero (h : Herbrand Q i) : Succ h =' 0 = (⊥ : Lindenbaum Q i) :=
by simp [Lindenbaum.equal_symm (Succ h) 0]

@[simp] lemma succ_inj (t u : term L) :
  Q ⊢ (Succ t =' Succ u) ⟶ (t =' u) :=
by { have : Q ⊢ ∀₁ x y, (Succ x =' Succ y) ⟶ (x =' y), by simpa[fal_fn] using provable.lextend (by_axiom robinson.q2) Q,
     simpa[fal_fn] using this ⊚ t ⊚ u }

@[simp] lemma Lindenbaum.succ_inj  (h₁ h₂ : Herbrand Q i) : (Succ h₁ =' Succ h₂ : Lindenbaum Q i) = (h₁ =' h₂) :=
by { induction h₁ using fol.Herbrand.ind_on with t,
     induction h₂ using fol.Herbrand.ind_on with u,
     have : Q^i ⊢ (Succ t =' Succ u) ⟷ (t =' u), by simp[iff_equiv],
     simpa using Lindenbaum.eq_of_provable_equiv.mp this }

lemma Herbrand.succ_injective : function.injective (has_succ.succ : Herbrand Q i → Herbrand Q i) :=
λ h₁ h₂,
begin
  induction h₁ using fol.Herbrand.ind_on with t,
  induction h₂ using fol.Herbrand.ind_on with u,
  intros h,
  have lmm₁ : Q^i ⊢ Succ t =' Succ u, from Herbrand.eq_of_provable_equiv.mpr (by simp[h]),
  have lmm₂ : Q^i ⊢ (Succ t =' Succ u) ⟶ (t =' u), by simp, 
  have : Q^i ⊢ t =' u, from lmm₂ ⨀ lmm₁,
  exact Herbrand.eq_of_provable_equiv.mp this
end

@[simp] lemma Herbrand.succ_injective_iff (h₁ h₂ : Herbrand Q i) : Succ h₁ = Succ h₂ ↔ h₁ = h₂ :=
⟨@@Herbrand.succ_injective _ Q _ i, λ h, by simp[h]⟩

@[simp] lemma zero_or_succ (t) : Q ⊢ (t =' 0) ⊔ (∃₁ y, t^1 =' Succ y) :=
by { have : Q ⊢ ∀₁ x, (x =' 0) ⊔ (∃₁ y, x =' Succ y), by simpa[fal_fn, ex_fn] using provable.lextend (by_axiom robinson.q3) Q,
     simpa[fal_fn, ex_fn] using this ⊚ t }

@[simp] lemma add_zero (t : term L) : Q ⊢ t + 0 =' t :=
by { have : Q ⊢ ∀₁ x, (x + 0 =' x), by simpa[fal_fn, ex_fn] using provable.lextend (by_axiom robinson.q4) Q,
     simpa[fal_fn, ex_fn] using this ⊚ t }

@[simp] lemma Herbrand.add_zero (h : Herbrand Q i) : h + 0 = h :=
by { induction h using fol.Herbrand.ind_on with t,
     simpa using Herbrand.eq_of_provable_equiv.mp (add_zero (Q^i) t) }

@[simp] lemma add_succ (t u : term L) : Q ⊢ t + Succ u =' Succ (t + u) :=
by { have : Q ⊢ ∀₁ x y, x + Succ y =' Succ (x + y), by simpa[fal_fn, ex_fn] using provable.lextend (by_axiom robinson.q5) Q,
     simpa[fal_fn, ex_fn] using this ⊚ t ⊚ u }

@[simp] lemma Herbrand.add_succ {i} (h₁ h₂ : Herbrand Q i) : h₁ + Succ h₂ = Succ (h₁ + h₂) :=
by { induction h₁ using fol.Herbrand.ind_on with t,
     induction h₂ using fol.Herbrand.ind_on with u,
     simpa using Herbrand.eq_of_provable_equiv.mp (add_succ (Q^i) t u) }

@[simp] lemma mul_zero (t : term L) : Q ⊢ t * 0 =' 0 :=
by { have : Q ⊢ ∀₁ x, x * 0 =' 0, by simpa[fal_fn, ex_fn] using provable.lextend (by_axiom robinson.q6) Q,
     simpa[fal_fn, ex_fn] using this ⊚ t }

@[simp] lemma Herbrand.mul_zero  (h : Herbrand Q i) : h * 0 = 0 :=
by { induction h using fol.Herbrand.ind_on with t,
     simpa using Herbrand.eq_of_provable_equiv.mp (mul_zero (Q^i) t) }

@[simp] lemma mul_succ (t u : term L) : Q ⊢ t * Succ u =' t * u + t :=
by { have : Q ⊢ ∀₁ x y, x * Succ y =' x * y + x, by simpa[fal_fn, ex_fn] using provable.lextend (by_axiom robinson.q7) Q,
     simpa[fal_fn, ex_fn] using this ⊚ t ⊚ u }

@[simp] lemma Herbrand.mul_succ {i} (h₁ h₂ : Herbrand Q i) : h₁ * Succ h₂ = h₁ * h₂ + h₁ :=
by { induction h₁ using fol.Herbrand.ind_on with t,
     induction h₂ using fol.Herbrand.ind_on with u,
     simpa using Herbrand.eq_of_provable_equiv.mp (mul_succ (Q^i) t u) }

@[simp] lemma le_iff (t u : term L) : Q ⊢ (t ≼ u) ⟷ ∃. (#0 + t^1 =' u^1) :=
by { have : Q ⊢ ∀₁ x y, (x ≼ y) ⟷ ∃₁ z, (z + x =' y), by simpa[fal_fn, ex_fn] using provable.lextend (by_axiom robinson.q8) Q,
     simpa[fal_fn, ex_fn, ←term.pow_rew_distrib] using this ⊚ t ⊚ u }

lemma Lindenbaum.le_iff {h₁ h₂ : Herbrand Q i} :
  (h₁ ≼ h₂ : Lindenbaum Q i) = ∃' (♯0 + h₁.pow =' h₂.pow : Lindenbaum Q (i + 1)) :=
by { induction h₁ using fol.Herbrand.ind_on with t,
     induction h₂ using fol.Herbrand.ind_on with u,
     simpa[ex_fn] using Lindenbaum.eq_of_provable_equiv.mp (le_iff (Q^i) t u) }

namespace Lindenbaum

lemma le_of_eq (e : Herbrand Q i) {h₁ h₂ : Herbrand Q i} (h : e + h₁ = h₂) : h₁ ≤ h₂ :=
begin
  induction e using fol.Herbrand.ind_on with u,
  induction h₁ using fol.Herbrand.ind_on with t₁,
  induction h₂ using fol.Herbrand.ind_on with t₂,
  have lmm₁ : Q^i ⊢ ∃. (#0 + t₁^1 =' t₂^1),
  { refine use u _, simp, refine Herbrand.eq_of_provable_equiv.mpr (by simp[h]) },
  have lmm₂ : Q^i ⊢ (t₁ ≼ t₂) ⟷ ∃. (#0 + t₁^1 =' t₂^1), by simp,
  exact Herbrand.le_iff_provable_le.mp (of_equiv lmm₁ (equiv_symm lmm₂))
end

@[simp] lemma le_add_self (h₁ h₂ : Herbrand Q i) : h₁ ≤ h₂ + h₁ := le_of_eq Q i h₂ rfl

@[simp] lemma succ_inj_le {h₁ h₂ : Herbrand Q i} :
  (Succ h₁ ≼ Succ h₂ : Lindenbaum Q i) = (h₁ ≼ h₂) := by simp[le_iff, succ_pow]

lemma add_numeral_eq_numeral_add (m n : ℕ) : (n˙ : Herbrand Q i) + m˙ = (n + m)˙ :=
by induction m with m IH; simp[numeral, *, ←nat.add_one, ←add_assoc]

lemma mul_numeral_eq_numeral_mul (m n : ℕ) : (n˙ : Herbrand Q i) * m˙ = (n * m)˙ :=
by induction m with m IH; simp[numeral, *, ←nat.add_one, add_numeral_eq_numeral_add, mul_add]

lemma succ_add_numeral_eq_add_succ_numeral (h : Herbrand Q i) (n : ℕ) : Succ h + n˙ = h + (n + 1)˙ :=
by induction n with n IH; simp[numeral, *]

end Lindenbaum

@[simp] lemma add_eq_zero : Q ⊢ ∀₁ x y, (x + y =' 0) ⟶ (x =' 0) ⊓ (y =' 0) :=
begin
  refine generalize (generalize _), simp[fal_fn], 
  have lmm₁ : ⤊⤊Q ⊢ (#0 =' 0) ⟶ (#1 + #0 =' 0) ⟶ (#1 =' 0) ⊓ (#0 =' 0),
    from (deduction.mp (by simp [le_of_provable_imply_0, rew_by_axiom₁])),
  have lmm₂ : ⤊⤊Q ⊢ (∃₁ y, #1 =' Succ y) ⟶ (#1 + #0 =' 0) ⟶ (#1 =' 0) ⊓ (#0 =' 0),
    from imply_ex_of_fal_imply (generalize (deduction.mp (by simp [le_of_provable_imply_0, rew_by_axiom₁]))), 
  exact case_of_ax (zero_or_succ _ #0) lmm₁ lmm₂
end

@[simp] lemma Lindenbaum.add_eq_0_of_eq_0 (x y : Herbrand Q i) :
  (x + y =' 0 : Lindenbaum Q i) = (x =' 0) ⊓ (y =' 0) :=
begin
  induction x using fol.Herbrand.ind_on,
  induction y using fol.Herbrand.ind_on,
  have : Q^i ⊢ (x + y =' 0) ⟷ (x =' 0) ⊓ (y =' 0), 
  { simp[iff_equiv],
    refine ⟨by simpa[fal_fn] using add_eq_zero (Q^i) ⊚ x ⊚ y, deduction.mp _⟩, simp,
    simp[Herbrand.eq_of_provable_equiv_0, rew_by_axiom₁, rew_by_axiom₂] },
  simpa using Lindenbaum.eq_of_provable_equiv.mp this
end

lemma mul_eq_zero : Q ⊢ ∀₁ x y, (x * y =' 0) ⟶ (x =' 0) ⊔ (y =' 0) :=
begin
  refine generalize (generalize _), simp[fal_fn], 
  have lmm₁ : ⤊⤊Q ⊢ (#0 =' 0) ⟶ (#1 * #0 =' 0) ⟶ (#1 =' 0) ⊔ (#0 =' 0),
  { refine (deduction.mp _),
    simp[le_of_provable_imply_0, rew_by_axiom₁] },
  have lmm₂ : ⤊⤊Q ⊢ (∃₁ y, #1 =' Succ y) ⟶ (#1 * #0 =' 0) ⟶ (#1 =' 0) ⊔ (#0 =' 0),
  { refine imply_ex_of_fal_imply (generalize (deduction.mp _)), simp,
    simp[le_of_provable_imply_0, rew_by_axiom₁] },
  exact case_of_ax (zero_or_succ _ #0) lmm₁ lmm₂
end

lemma zero_le : Q ⊢ ∀₁ x, 0 ≼ x :=
begin
  refine generalize _, simp[fal_fn],
  have : ⤊Q ⊢ (0 ≼ #0) ⟷ (∃₁ z, z + 0 =' #1), by simpa using (le_iff ⤊Q 0 #0), 
  refine of_equiv (use #0 (by simp)) (equiv_symm this),
end

@[simp] lemma Lindenbaum.zero_le (h : Herbrand Q i) : 0 ≤ h :=
by induction h using fol.Herbrand.ind_on with t;
   simpa using Herbrand.le_iff_provable_le.mp (by simpa[fal_fn] using zero_le (Q^i) ⊚ t)

@[simp] lemma le_zero_equiv_eq_zero : Q ⊢ ∀₁ x, (x ≼ 0) ⟷ (x =' 0) :=
begin
  refine generalize _, simp[fal_fn],
  suffices : ⤊Q ⊢ ∃. (#0 + #1 =' 0) ⟷ (#0 =' 0),
    by simpa[Lindenbaum.eq_of_provable_equiv_0, Lindenbaum.le_iff] using this,
  simp[iff_equiv], split,
  { refine ((pnf_imply_ex_iff_fal_imply₁ _ _).mpr $ generalize _),
    simp[Lindenbaum.le_of_provable_imply_0] },
  { refine deduction.mp (use 0 _), simp[ı, Herbrand.eq_of_provable_equiv_0, rew_by_axiom₁] }
end

@[simp] lemma Lindenbaum.le_zero_eq_eq_zero (h : Herbrand Q i) : (h ≼ 0 : Lindenbaum Q i) = (h =' 0) :=
by induction h using fol.Herbrand.ind_on with t;
   simpa[Lindenbaum.eq_of_provable_equiv_0] using (le_zero_equiv_eq_zero (Q^i) ⊚ t)

@[simp] lemma add_numeral_eq_numeral_add (n m : ℕ) : Q ⊢ (n˙ : term L) + m˙ =' (n + m)˙ :=
by simp[Herbrand.eq_of_provable_equiv_0, Lindenbaum.add_numeral_eq_numeral_add]

@[simp] lemma mul_numeral_eq_numeral_mul (n m : ℕ) : Q ⊢ (n˙ : term L) * m˙ =' (n * m)˙ :=
by simp[Herbrand.eq_of_provable_equiv_0, Lindenbaum.mul_numeral_eq_numeral_mul]

lemma le_numeral_of_le {n m : ℕ} (h : n ≤ m) : Q ⊢ (n˙ : term L) ≼ m˙ :=
begin
  let l := m - n,
  have : m = l + n, from (nat.sub_eq_iff_eq_add h).mp rfl,
  simp[this],
  refine of_equiv (use (l˙) _) (equiv_symm $ le_iff Q (n˙) ((l + n)˙)), simp
end

lemma le_numeral_iff (n : ℕ) : Q ⊢ ∀. ((#0 ≼ n˙) ⟷ ⋁ i : fin (n+1), #0 =' (i : ℕ)˙) :=
begin
  suffices : ∀ k : ℕ, Q^k ⊢ ∀. ((#0 ≼ n˙) ⟷ ⋁ i : fin (n+1), #0 =' (i : ℕ)˙),
  { exact this 0 },
  induction n with n IH,
  { intros k, refine generalize _, simp[Lindenbaum.eq_of_provable_equiv_0], exact Lindenbaum.le_zero_eq_eq_zero _ _ _ },
  { intros k, refine generalize _,
    simp[←Theory.sf_itr_succ, iff_equiv, -finitary.disjunction], split,
    { have zero : Q^(k + 1) ⊢ (#0 =' 0) ⟶ (#0 ≼ (n + 1)˙) ⟶ ⋁ (i : fin (n.succ + 1)), #0 =' ↑i˙,
      { refine (deduction.mp $ deduction.mp $ imply_or_right _ _ ⨀ (rew_of_eq 0 0 (by simp) _)), 
        simp, refine disjunction_of ⟨0, by simp⟩ (by simp[numeral]) },
      have succ : Q^(k + 1) ⊢ (∃₁ y, #1 =' Succ y) ⟶ (#0 ≼ (n + 1)˙) ⟶ ⋁ (i : fin (n.succ + 1)), #0 =' ↑i˙,
      { refine (imply_ex_of_fal_imply $ generalize $ deduction.mp $ rew_of_eq (Succ #0) 1 (by simp) (deduction.mp _)),
        simp[ -finitary.disjunction, ←Theory.sf_itr_succ], 
        have : (Q^(k + 2)) +{ #1 =' Succ #0 } +{ Succ #0 ≼ (n + 1)˙ } ⊢ #0 ≼ n˙,
          from of_equiv_p (show _ ⊢ Succ #0 ≼ (n + 1)˙, by simp) (by simp[numeral, Lindenbaum.eq_of_provable_equiv_0]), 
        have lmm₁ : (Q^(k + 2)) +{ #1 =' Succ #0 } +{ Succ #0 ≼ (n + 1)˙ } ⊢ ⋁ (i : fin (n + 1)), #0 =' ↑i˙,
          from of_equiv_p this (weakening
            (show Q^(k + 2) ⊆ (Q^(k + 2)) +{ #1 =' Succ #0 } +{ Succ #0 ≼ (n + 1)˙ }, by { intros p mem, refine set.subset_insert _ _ (set.subset_insert _ _ mem) })
            (show Q^(k + 2) ⊢ (#0 ≼ n˙) ⟷ ⋁ (i : fin (n + 1)), #0 =' ↑i˙, by simpa using IH (k + 2) ⊚ #0)),
        have lmm₂ : (Q^(k + 2)) +{ #1 =' Succ #0 } +{ Succ #0 ≼ (n + 1)˙ } ⊢ (⋁ (i : fin (n + 1)), #0 =' ↑i˙) ⟶ (⋁ (i : fin (n.succ + 1)), Succ #0 =' ↑i˙),
        { suffices : (Q^(k + 2)) +{ #1 =' Succ #0 } +{ Succ #0 ≼ (n + 1)˙ } ⊢ ⋀ (i : fin (n + 1)), (#0 =' ↑i˙) ⟶ ⋁ (i : fin (n.succ + 1)), Succ #0 =' ↑i˙,
            from of_equiv this (conj_imply_iff_disj_imply _ _),
          refine conjunction_iff.mpr (λ i, deduction.mp $ rew_of_eq (↑i˙) 0 (by simp) _), simp[-finitary.disjunction],
          refine disjunction_of ⟨i + 1, by simp⟩ (by simp[numeral]) },
        exact lmm₂ ⨀ lmm₁ },
      exact case_of_ax (show (Q^(k + 1)) ⊢ (#0 =' 0) ⊔ ∃₁ y, (#1 =' Succ y), from zero_or_succ (Q^(k + 1)) #0) zero succ },
    { refine of_equiv (conjunction_iff.mpr _) (conj_imply_iff_disj_imply _ _),
      rintros ⟨i, hi⟩, refine (deduction.mp $  rew_of_eq (i˙) 0 (by simp) _),
      simp[←nat.add_one],
      exact le_numeral_of_le _ (show i ≤ n + 1, from nat.lt_succ_iff.mp hi) } }
end

end robinson

namespace Ind
open Herbrand Lindenbaum robinson.Lindenbaum provable
variables (C : Theory LA)
          {L} [LA.language_translation_coe L] (T : Theory L) [lextend 𝐈C T]
          {L'} [LA'.language_translation_coe L'] (T' : Theory L') [lextend 𝐈C T']

lemma I_succ_induction_aux (p : formula LA) (h : p ∈ C) :
  T ⊢ succ_induction p :=
by { have : 𝐈C ⊢ succ_induction p, from by_axiom (by { simp[succ_induction_axiom, h], refine or.inr ⟨p, by simp[h]⟩ }),
     simpa[succ_induction, language.language_translation_coe.coe_p_rew] using provable.lextend this T }

lemma I_succ_induction (p : formula LA) (h : p ∈ C) :
  T ⊢ p.rew (0 ⌢ ı) ⟶ ∀. (p ⟶ p.rew ((Succ #0) ⌢ (λ x, #(x+1)))) ⟶ ∀. p :=
by simpa using provable.fal_complete_rew _ ı ⨀ (I_succ_induction_aux C T p h)

lemma equiv_succ_induction_of_equiv {T₀ : Theory L} [closed_Theory T₀] {p q : formula L} (h : T₀ ⊢ p ⟷ q) :
  T₀ ⊢ succ_induction p ⟷ succ_induction q :=
begin
  refine (equiv_fal_complete_of_equiv _), simp,
  refine (equiv_imply_of_equiv _ $ equiv_imply_of_equiv _ _),
  { simpa using cl_prove_rew h (0 ⌢ ı) },
  { refine equiv_univ_of_equiv (equiv_imply_of_equiv _ _); simp*, simpa using cl_prove_rew h _ },
  { refine equiv_univ_of_equiv (by simp[h]) }
end

@[simp] lemma equiv_succ_induction_of_equgiv {L₁ L₂ : language.{0}}
  [LA.language_translation_coe L₁] [LA.language_translation_coe L₂] [L₁.language_translation_coe L₂] [LA.commutes L₁ L₂]
  (p : formula L₁) :
  (↑(succ_induction p : formula L₁) : formula L₂) = succ_induction (↑p : formula L₂) :=
by simp[succ_induction, language.language_translation_coe.coe_p_rew, function.comp]

section
variables {L₁ L₂ : language.{0}}
  [LA'.language_translation_coe L₁] [LA'.language_translation_coe L₂] [L₁.language_translation_coe L₂] [LA'.commutes L₁ L₂]

@[simp] lemma coe_lt (t u : term L₁) : ((t ≺ u : formula L₁) : formula L₂) = (t ≺ u) :=
by simp[additional.lt]; refine language.commutes.coe_coe_pr_of_commute _

@[simp] lemma coe_dvd (t u : term L₁) : ((t ⍭ u : formula L₁) : formula L₂) = (t ⍭ u) :=
by simp[additional.dvd]; refine language.commutes.coe_coe_pr_of_commute _

@[simp] lemma quantifier_fn_aux_lt (s) (f g : term L₁ → term L₁) (t u : term L₁) :
  quantifier_fn_aux s (λ x, f x ≺ g x) (t ≺ u) = (f #s ≺ g #s) := rfl

@[simp] lemma quantifier_fn_aux_dvd (s) (f g : term L₁ → term L₁) (t u : term L₁) :
  quantifier_fn_aux s (λ x, f x ⍭ g x) (t ⍭ u) = (f #s ⍭ g #s) := rfl

end

end Ind

namespace Iopen
open Lindenbaum Herbrand additional robinson Ind robinson.Lindenbaum provable
variables {L} [LA.language_translation_coe L] (Iₒₚₑₙ : Theory L) [lextend 𝐈is_open Iₒₚₑₙ] (i : ℕ)
          {L'} [LA'.language_translation_coe L'] (Iₒₚₑₙ' : Theory L') [lextend 𝐈is_open Iₒₚₑₙ']
          [lextend additional.defs.thy Iₒₚₑₙ']

instance lextend_Q : lextend 𝐐 Iₒₚₑₙ := Theory.lextend_trans 𝐐 𝐈is_open Iₒₚₑₙ

lemma I_succ_induction_LA (p : formula LA') (h : formula.coe_inv_is_open defs p):
  Iₒₚₑₙ' ⊢ p.rew (0 ⌢ ı) ⟶ ∀. (p ⟶ p.rew ((Succ #0) ⌢ (λ x, #(x+1)))) ⟶ ∀. p :=
begin
  have : Iₒₚₑₙ' ⊢ succ_induction ↑p ⟷ succ_induction ↑(coe_inv defs p),
    by simpa using provable.lextend (equiv_succ_induction_of_equiv (coe_inv_equiv additional.defs p)) Iₒₚₑₙ',
  have : Iₒₚₑₙ' ⊢ succ_induction ↑p,
    from of_equiv_p (I_succ_induction_aux is_open Iₒₚₑₙ' (coe_inv defs p) (by simp[set.mem_def, h])) (equiv_symm this),
  simpa using provable.fal_complete_rew _ ı ⨀ this
end

@[simp] lemma zero_add : Iₒₚₑₙ ⊢ ∀₁ x, 0 + x =' x :=
begin
  have lmm₁ : Iₒₚₑₙ ⊢ (0 + 0 =' 0) ⟶ ∀. ((0 + #0 =' #0) ⟶ (0 + Succ #0 =' Succ #0)) ⟶ ∀. (0 + #0 =' #0), 
    by simpa using Ind.I_succ_induction is_open Iₒₚₑₙ (0 + #0 =' #0) (by simp[set.mem_def]),
  have lmm₂ : Iₒₚₑₙ ⊢ ∀. ((0 + #0 =' #0) ⟶ (0 + Succ #0 =' Succ #0)),
  { refine generalize (deduction.mp _), 
    have : ⤊Iₒₚₑₙ +{ 0 + #0 =' #0 } ⊢ 0 + #0 =' #0, by simp,
    simp[Herbrand.eq_of_provable_equiv_0] at this ⊢, exact this },
  simpa using (lmm₁ ⨀ (by simp[Herbrand.eq_of_provable_equiv_0]) ⨀ lmm₂)
end

@[simp] lemma Lindenbaum.zero_add (h : Herbrand Iₒₚₑₙ i) : 0 + h = h :=
by induction h using fol.Herbrand.ind_on with t;
   simpa using Herbrand.eq_of_provable_equiv.mp (zero_add (Iₒₚₑₙ^i) ⊚ t)

@[simp] lemma succ_add : Iₒₚₑₙ ⊢ ∀₁ x y, Succ x + y =' Succ (x + y) :=
begin
  have ind : ⤊Iₒₚₑₙ ⊢ (Succ #0 + 0 =' Succ (#0 + 0)) ⟶
                    ∀. ((Succ #1 + #0 =' Succ (#1 + #0)) ⟶ (Succ #1 + Succ #0 =' Succ (#1 + Succ #0))) ⟶
                    ∀. (Succ #1 + #0 =' Succ (#1 + #0)), 
  by simpa using Ind.I_succ_induction is_open ⤊Iₒₚₑₙ (Succ #1 + #0 =' Succ (#1 + #0)) (by simp[set.mem_def]),
  have zero : ⤊Iₒₚₑₙ ⊢ Succ #0 + 0 =' Succ (#0 + 0),  by simp[Herbrand.eq_of_provable_equiv_0],
  have succ : ⤊Iₒₚₑₙ ⊢ ∀. ((Succ #1 + #0 =' Succ (#1 + #0)) ⟶ (Succ #1 + Succ #0 =' Succ (#1 + Succ #0))),
  { refine (generalize $ deduction.mp _), simp,
    have : ⤊⤊Iₒₚₑₙ +{ Succ #1 + #0 =' Succ (#1 + #0) } ⊢ Succ #1 + #0 =' Succ (#1 + #0), by simp,
    simp[Herbrand.eq_of_provable_equiv_0] at this ⊢,  exact this },
  simpa using (generalize $ ind ⨀ zero ⨀ succ)
end

@[simp] lemma Lindenbaum.succ_add (h₁ h₂ : Herbrand Iₒₚₑₙ i) : Succ h₁ + h₂ = Succ (h₁ + h₂) :=
by induction h₁ using fol.Herbrand.ind_on with t;
   induction h₂ using fol.Herbrand.ind_on with u;
   simpa using Herbrand.eq_of_provable_equiv.mp (succ_add (Iₒₚₑₙ^i) ⊚ t ⊚ u)

lemma add_commutative : Iₒₚₑₙ ⊢ ∀₁ x y, x + y =' y + x :=
begin
  have ind : ⤊Iₒₚₑₙ ⊢ (#0 + 0 =' 0 + #0) ⟶ ∀. ((#1 + #0 =' #0 + #1) ⟶ (#1 + Succ #0 =' Succ #0 + #1)) ⟶ ∀. (#1 + #0 =' #0 + #1),
    by simpa using Ind.I_succ_induction is_open ⤊Iₒₚₑₙ (#1 + #0 =' #0 + #1) (by simp[set.mem_def]),
  have zero : ⤊Iₒₚₑₙ ⊢ #0 + 0 =' 0 + #0, by simp[Herbrand.eq_of_provable_equiv_0],
  have succ : ⤊Iₒₚₑₙ ⊢ ∀. ((#1 + #0 =' #0 + #1) ⟶ (#1 + Succ #0 =' Succ #0 + #1)),
  { refine (generalize $ deduction.mp _), simp,
    have : ⤊⤊Iₒₚₑₙ +{ #1 + #0 =' #0 + #1 } ⊢ #1 + #0 =' #0 + #1, by simp,
    simp[Herbrand.eq_of_provable_equiv_0] at this ⊢, exact this },
  simpa using (generalize $ ind ⨀ zero ⨀ succ)
end

lemma Lindenbaum.add_commutative (h₁ h₂ : Herbrand Iₒₚₑₙ i) : h₁ + h₂ = h₂ + h₁ :=
by induction h₁ using fol.Herbrand.ind_on with t;
   induction h₂ using fol.Herbrand.ind_on with u;
   simpa using Herbrand.eq_of_provable_equiv.mp (add_commutative (Iₒₚₑₙ^i) ⊚ t ⊚ u)

lemma add_associative : Iₒₚₑₙ ⊢ ∀₁ x y z, x + y + z =' x + (y + z) :=
begin
  have ind : ⤊⤊Iₒₚₑₙ ⊢ (#1 + #0 + 0 =' #1 + (#0 + 0)) ⟶
                     ∀. ((#2 + #1 + #0 =' #2 + (#1 + #0)) ⟶ (#2 + #1 + Succ #0 =' #2 + (#1 + Succ #0))) ⟶
                     ∀. (#2 + #1 + #0 =' #2 + (#1 + #0)),
  by simpa using Ind.I_succ_induction is_open ⤊⤊Iₒₚₑₙ (#2 + #1 + #0 =' #2 + (#1 + #0)) (by simp[set.mem_def]),
  have zero : ⤊⤊Iₒₚₑₙ ⊢ #1 + #0 + 0 =' #1 + (#0 + 0), by simp[Herbrand.eq_of_provable_equiv_0],
  have succ : ⤊⤊Iₒₚₑₙ ⊢ ∀. ((#2 + #1 + #0 =' #2 + (#1 + #0)) ⟶ (#2 + #1 + Succ #0 =' #2 + (#1 + Succ #0))),
  { refine (generalize $ deduction.mp _), simp,
    have : ⤊⤊⤊Iₒₚₑₙ +{ #2 + #1 + #0 =' #2 + (#1 + #0) } ⊢ #2 + #1 + #0 =' #2 + (#1 + #0), by simp,
    simp[Herbrand.eq_of_provable_equiv_0] at this ⊢, exact this },
  simpa using (generalize $ generalize $ ind ⨀ zero ⨀ succ)
end

lemma Lindenbaum.add_associative (h₁ h₂ h₃ : Herbrand Iₒₚₑₙ i) : h₁ + h₂ + h₃ = h₁ + (h₂ + h₃) :=
by induction h₁ using fol.Herbrand.ind_on with t₁;
   induction h₂ using fol.Herbrand.ind_on with t₂;
   induction h₃ using fol.Herbrand.ind_on with t₃;
   simpa using Herbrand.eq_of_provable_equiv.mp (add_associative _ ⊚ t₁ ⊚ t₂ ⊚ t₃)


instance Lindenbaum.add_comm_semigroup : add_comm_semigroup (Herbrand Iₒₚₑₙ i) :=
{ add := (+),
  add_assoc := Lindenbaum.add_associative _ _,
  add_comm := Lindenbaum.add_commutative _ _ }

lemma zero_mul : Iₒₚₑₙ ⊢ ∀₁ x, 0 * x =' 0 :=
begin
  have ind : Iₒₚₑₙ ⊢ (0 * 0 =' 0) ⟶ ∀. ((0 * #0 =' 0) ⟶ (0 * Succ #0 =' 0)) ⟶ ∀. (0 * #0 =' 0),
    by simpa using Ind.I_succ_induction is_open Iₒₚₑₙ (0 * #0 =' 0) (by simp[set.mem_def]), 
  have zero : Iₒₚₑₙ ⊢ 0 * 0 =' 0, by simp[Herbrand.eq_of_provable_equiv_0],
  have succ : Iₒₚₑₙ ⊢ ∀. ((0 * #0 =' 0) ⟶ (0 * Succ #0 =' 0)),
  { refine (generalize $ deduction.mp _),
    have : ⤊Iₒₚₑₙ +{ 0 * #0 =' 0 } ⊢ 0 * #0 =' 0, by simp,
    simp[Herbrand.eq_of_provable_equiv_0] at this ⊢, simp[this] },
  simpa using ind ⨀ zero ⨀ succ
end

@[simp] lemma Lindenbaum.zero_mul (h : Herbrand Iₒₚₑₙ i) : 0 * h = 0 :=
by induction h using fol.Herbrand.ind_on with t;
   simpa using Herbrand.eq_of_provable_equiv.mp (zero_mul _ ⊚ t)

lemma succ_mul : Iₒₚₑₙ ⊢ ∀₁ x y, Succ x * y =' x * y + y :=
begin
  have ind : ⤊Iₒₚₑₙ ⊢ (Succ #0 * 0 =' #0 * 0 + 0) ⟶
                    ∀. ((Succ #1 * #0 =' #1 * #0 + #0) ⟶ (Succ #1 * Succ #0 =' #1 * Succ #0 + Succ #0)) ⟶
                    ∀. (Succ #1 * #0 =' #1 * #0 + #0),
  by simpa using Ind.I_succ_induction is_open ⤊Iₒₚₑₙ (Succ #1 * #0 =' #1 * #0 + #0) (by simp[set.mem_def]),
  have zero : ⤊Iₒₚₑₙ ⊢ Succ #0 * 0 =' #0 * 0 + 0, by simp[Herbrand.eq_of_provable_equiv_0],
  have succ : ⤊Iₒₚₑₙ ⊢ ∀. ((Succ #1 * #0 =' #1 * #0 + #0) ⟶ (Succ #1 * Succ #0 =' #1 * Succ #0 + Succ #0)),
  { refine (generalize $ deduction.mp _),
    have : ⤊⤊Iₒₚₑₙ +{ Succ #1 * #0 =' #1 * #0 + #0 } ⊢ Succ #1 * #0 =' #1 * #0 + #0, by simp,
    simp[Herbrand.eq_of_provable_equiv_0] at this ⊢,
    calc (Succ ♯1 * ♯0 + ♯1 : Herbrand (⤊⤊Iₒₚₑₙ +{ Succ #1 * #0 =' #1 * #0 + #0 }) 0)
        = ♯1 * ♯0 + ♯0 + ♯1   : by rw[this]
    ... = ♯1 * ♯0 + (♯1 + ♯0) : by simp[add_assoc, add_comm]
    ... = ♯1 * ♯0 + ♯1 + ♯0   : by simp[add_assoc] },
  simpa using (generalize $ ind ⨀ zero ⨀ succ)
end

@[simp] lemma Lindenbaum.succ_mul (h₁ h₂ : Herbrand Iₒₚₑₙ i) : Succ h₁ * h₂ = h₁ * h₂ + h₂ :=
by induction h₁ using fol.Herbrand.ind_on with t;
   induction h₂ using fol.Herbrand.ind_on with u;
   simpa using Herbrand.eq_of_provable_equiv.mp (succ_mul _ ⊚ t ⊚ u)

lemma mul_commutative : Iₒₚₑₙ ⊢ ∀₁ x y, x * y =' y * x :=
begin
  have ind : ⤊Iₒₚₑₙ ⊢ (#0 * 0 =' 0 * #0) ⟶ ∀. ((#1 * #0 =' #0 * #1) ⟶ (#1 * Succ #0 =' Succ #0 * #1)) ⟶ ∀. (#1 * #0 =' #0 * #1),
    by simpa using Ind.I_succ_induction is_open ⤊Iₒₚₑₙ (#1 * #0 =' #0 * #1) (by simp[set.mem_def]),
  have zero : ⤊Iₒₚₑₙ ⊢ #0 * 0 =' 0 * #0, by simp[Herbrand.eq_of_provable_equiv_0],
  have succ : ⤊Iₒₚₑₙ ⊢ ∀. ((#1 * #0 =' #0 * #1) ⟶ (#1 * Succ #0 =' Succ #0 * #1)),
  { refine (generalize $ deduction.mp _), simp,
    have : ⤊⤊Iₒₚₑₙ +{ #1 * #0 =' #0 * #1 } ⊢ #1 * #0 =' #0 * #1, by simp,
    simp[Herbrand.eq_of_provable_equiv_0] at this ⊢, simp[this] },
  simpa using (generalize $ ind ⨀ zero ⨀ succ)
end

lemma Lindenbaum.mul_commutative (h₁ h₂ : Herbrand Iₒₚₑₙ i) : h₁ * h₂ = h₂ * h₁ :=
by induction h₁ using fol.Herbrand.ind_on with t;
   induction h₂ using fol.Herbrand.ind_on with u;
   simpa using Herbrand.eq_of_provable_equiv.mp (mul_commutative _ ⊚ t ⊚ u)

lemma mul_add : Iₒₚₑₙ ⊢ ∀₁ x y z, x * (y + z) =' x * y + x * z :=
begin
  have ind : ⤊⤊Iₒₚₑₙ ⊢ (#1 * (#0 + 0) =' #1 * #0 + #1 * 0) ⟶
                     ∀. ((#2 * (#1 + #0) =' #2 * #1 + #2 * #0) ⟶ (#2 * (#1 + Succ #0) =' #2 * #1 + #2 * Succ #0)) ⟶
                     ∀. (#2 * (#1 + #0) =' #2 * #1 + #2 * #0),
  by simpa using Ind.I_succ_induction is_open ⤊⤊Iₒₚₑₙ (#2 * (#1 + #0) =' #2 * #1 + #2 * #0) (by simp[set.mem_def]),
  have zero : ⤊⤊Iₒₚₑₙ ⊢ #1 * (#0 + 0) =' #1 * #0 + #1 * 0, by simp[Herbrand.eq_of_provable_equiv_0],
  have succ : ⤊⤊Iₒₚₑₙ ⊢ ∀. ((#2 * (#1 + #0) =' #2 * #1 + #2 * #0) ⟶ (#2 * (#1 + Succ #0) =' #2 * #1 + #2 * Succ #0)),
  { refine (generalize $ deduction.mp _), simp, 
    have : ⤊⤊⤊Iₒₚₑₙ +{ #2 * (#1 + #0) =' #2 * #1 + #2 * #0 } ⊢ #2 * (#1 + #0) =' #2 * #1 + #2 * #0, by simp,
    simp[Herbrand.eq_of_provable_equiv_0] at this ⊢,
    simp[this, add_assoc] },
  simpa using (generalize $ generalize $ ind ⨀ zero ⨀ succ)
end

lemma Lindenbaum.mul_add (h₁ h₂ h₃ : Herbrand Iₒₚₑₙ i) : h₁ * (h₂ + h₃) = h₁ * h₂ + h₁ * h₃ :=
by induction h₁ using fol.Herbrand.ind_on with t₁;
   induction h₂ using fol.Herbrand.ind_on with t₂;
   induction h₃ using fol.Herbrand.ind_on with t₃;
   simpa using Herbrand.eq_of_provable_equiv.mp (mul_add _ ⊚ t₁ ⊚ t₂ ⊚ t₃)

lemma mul_associative : Iₒₚₑₙ ⊢ ∀₁ x y z, x * y * z =' x * (y * z) :=
begin
  have ind : ⤊⤊Iₒₚₑₙ ⊢ (#1 * #0 * 0 =' #1 * (#0 * 0)) ⟶
                     ∀. ((#2 * #1 * #0 =' #2 * (#1 * #0)) ⟶ (#2 * #1 * Succ #0 =' #2 * (#1 * Succ #0))) ⟶
                     ∀. (#2 * #1 * #0 =' #2 * (#1 * #0)),
  by simpa using Ind.I_succ_induction is_open ⤊⤊Iₒₚₑₙ (#2 * #1 * #0 =' #2 * (#1 * #0)) (by simp[set.mem_def]),
  have zero : ⤊⤊Iₒₚₑₙ ⊢ #1 * #0 * 0 =' #1 * (#0 * 0), by simp[Herbrand.eq_of_provable_equiv_0],
  have succ : ⤊⤊Iₒₚₑₙ ⊢ ∀. ((#2 * #1 * #0 =' #2 * (#1 * #0)) ⟶ (#2 * #1 * Succ #0 =' #2 * (#1 * Succ #0))),
  { refine (generalize $ deduction.mp _),
    have : ⤊⤊⤊Iₒₚₑₙ +{ #2 * #1 * #0 =' #2 * (#1 * #0) } ⊢ #2 * #1 * #0 =' #2 * (#1 * #0), by simp,
    simp[Herbrand.eq_of_provable_equiv_0] at this ⊢, simp[this, Lindenbaum.mul_add] },
  simpa using (generalize $ generalize $ ind ⨀ zero ⨀ succ)
end

lemma Lindenbaum.mul_associative (h₁ h₂ h₃ : Herbrand Iₒₚₑₙ i) : h₁ * h₂ * h₃ = h₁ * (h₂ * h₃) :=
by induction h₁ using fol.Herbrand.ind_on with t₁;
   induction h₂ using fol.Herbrand.ind_on with t₂;
   induction h₃ using fol.Herbrand.ind_on with t₃;
   simpa using Herbrand.eq_of_provable_equiv.mp (mul_associative _ ⊚ t₁ ⊚ t₂ ⊚ t₃)

@[simp] lemma mul_one : Iₒₚₑₙ ⊢ ∀₁ x, x * 1 =' x := generalize (Herbrand.eq_of_provable_equiv_0.mpr (by simp[numeral_one_def]))

@[simp] lemma Lindenbaum.mul_one (h : Herbrand Iₒₚₑₙ i) : h * 1 = h := by simp[numeral_one_def]

instance Lindenbaum.comm_semigroup : comm_semigroup (Herbrand Iₒₚₑₙ i) :=
{ mul := (*),
  mul_assoc := Lindenbaum.mul_associative _ _,
  mul_comm := Lindenbaum.mul_commutative _ _ }

instance Lindenbaum.distrib : distrib (Herbrand Iₒₚₑₙ i) :=
{ mul := (*), add := (+),
  left_distrib := Lindenbaum.mul_add _ _,
  right_distrib := λ a b c, by simp[mul_comm (a + b), mul_comm a, mul_comm b, Lindenbaum.mul_add] }

lemma add_right_cancel : Iₒₚₑₙ ⊢ ∀₁ x y z, (x + z =' y + z) ⟶ (x =' y) :=
begin
  have ind : ⤊⤊Iₒₚₑₙ ⊢ ((#1 + 0 =' #0 + 0) ⟶ (#1 =' #0)) ⟶
                     ∀. (((#2 + #0 =' #1 + #0) ⟶ (#2 =' #1)) ⟶ (#2 + Succ #0 =' #1 + Succ #0) ⟶ (#2 =' #1)) ⟶
                     ∀. ((#2 + #0 =' #1 + #0) ⟶ (#2 =' #1)),
  by simpa using Ind.I_succ_induction is_open ⤊⤊Iₒₚₑₙ ((#2 + #0 =' #1 + #0) ⟶ (#2 =' #1)) (by simp[set.mem_def]),
  have zero : ⤊⤊Iₒₚₑₙ ⊢ (#1 + 0 =' #0 + 0) ⟶ (#1 =' #0), by simp[Lindenbaum.le_of_provable_imply_0],
  have succ : ⤊⤊Iₒₚₑₙ ⊢ ∀. (((#2 + #0 =' #1 + #0) ⟶ (#2 =' #1)) ⟶ (#2 + Succ #0 =' #1 + Succ #0) ⟶ (#2 =' #1)),
  { refine (generalize $ deduction.mp $ deduction.mp _), simp,
    have : ⤊⤊⤊Iₒₚₑₙ +{ (#2 + #0 =' #1 + #0) ⟶ (#2 =' #1) } +{ #2 + Succ #0 =' #1 + Succ #0 } ⊢ #2 + #0 =' #1 + #0,
      from deduction.mpr (by simp[Lindenbaum.le_of_provable_imply_0]),
    exact (show _ ⊢ (#2 + #0 =' #1 + #0) ⟶ (#2 =' #1), by simp) ⨀ this },
  simpa using (generalize $ generalize $ ind ⨀ zero ⨀ succ)
end

lemma Herbrand.add_right_cancel (h₁ h₂ h₃ : Herbrand Iₒₚₑₙ i) : h₁ + h₃ = h₂ + h₃ ↔ h₁ = h₂ :=
⟨λ h, begin
  induction h₁ using fol.Herbrand.ind_on with t₁,
  induction h₂ using fol.Herbrand.ind_on with t₂,
  induction h₃ using fol.Herbrand.ind_on with t₃,
  have lmm₁ : Iₒₚₑₙ^i ⊢ t₁ + t₃ =' t₂ + t₃, from Herbrand.eq_of_provable_equiv.mpr (by simp[h]),
  have lmm₂ : Iₒₚₑₙ^i ⊢ (t₁ + t₃ =' t₂ + t₃) ⟶ (t₁ =' t₂), by simpa[fal_fn] using add_right_cancel _ ⊚ t₁ ⊚ t₂ ⊚ t₃,
  exact Herbrand.eq_of_provable_equiv.mp (lmm₂ ⨀ lmm₁)
end, λ h, by simp[h]⟩

lemma Herbrand.add_left_cancel (h₁ h₂ h₃ : Herbrand Iₒₚₑₙ i) : h₃ + h₁ = h₃ + h₂ ↔ h₁ = h₂ :=
by simp[add_comm h₃, Herbrand.add_right_cancel]

@[simp] lemma Lindenbaum.add_right_cancel (h₁ h₂ h₃ : Herbrand Iₒₚₑₙ i) : (h₁ + h₃ =' h₂ + h₃ : Lindenbaum Iₒₚₑₙ i) = (h₁ =' h₂) :=
begin
  induction h₁ using fol.Herbrand.ind_on with t₁,
  induction h₂ using fol.Herbrand.ind_on with t₂,
  induction h₃ using fol.Herbrand.ind_on with t₃,
  have : Iₒₚₑₙ^i ⊢ (t₁ + t₃ =' t₂ + t₃) ⟷ (t₁ =' t₂),
  { simp[iff_equiv], refine ⟨by simpa[fal_fn] using add_right_cancel _ ⊚ t₁ ⊚ t₂ ⊚ t₃, deduction.mp _⟩,
  simp[Herbrand.eq_of_provable_equiv_0, Lindenbaum.rew_by_axiom₁] },
  simpa using Lindenbaum.eq_of_provable_equiv.mp this
end

lemma add_le_add : Iₒₚₑₙ ⊢ ∀₁ x y z, (x + z ≼ y + z) ⟷ (x ≼ y) :=
begin
  refine (generalize $ generalize $ generalize _), simp[fal_fn],
  suffices : ⤊⤊⤊Iₒₚₑₙ ⊢ ∃. (#0 + (#3 + #1) =' #2 + #1) ⟷ ∃. (#0 + #3 =' #2),
  { simpa[Lindenbaum.eq_top_of_provable_0, Lindenbaum.le_iff] using this },
  simp[iff_equiv], split,
  { refine (imply_ex_of_fal_imply $ generalize $ deduction.mp $ use #0 _), simp[formula.pow_eq], 
    have : ⤊⤊⤊⤊Iₒₚₑₙ +{ #0 + (#3 + #1) =' #2 + #1 } ⊢ #0 + (#3 + #1) =' #2 + #1, by simp,
    simp[Herbrand.eq_of_provable_equiv_0, ←add_assoc, Herbrand.add_right_cancel] at this ⊢, exact this },
  { refine (imply_ex_of_fal_imply $ generalize $ deduction.mp $ use #0 _), simp[formula.pow_eq],
    have : ⤊⤊⤊⤊Iₒₚₑₙ +{ #0 + #3 =' #2 } ⊢ #0 + #3 =' #2, by simp,
    simp[Herbrand.eq_of_provable_equiv_0, ←add_assoc, Herbrand.add_right_cancel] at this ⊢, exact this }
end 

@[simp] lemma Lindenbaum.le_add_right_cancel (h₁ h₂ h₃ : Herbrand Iₒₚₑₙ i) :
  (h₁ + h₃ ≼ h₂ + h₃ : Lindenbaum Iₒₚₑₙ i) = (h₁ ≼ h₂) :=
begin
  induction h₁ using fol.Herbrand.ind_on with t₁,
  induction h₂ using fol.Herbrand.ind_on with t₂,
  induction h₃ using fol.Herbrand.ind_on with t₃,
  have : Iₒₚₑₙ^i ⊢ (t₁ + t₃ ≼ t₂ + t₃) ⟷ (t₁ ≼ t₂), by simpa[fal_fn] using add_le_add _ ⊚ t₁ ⊚ t₂ ⊚ t₃,
  simpa using Lindenbaum.eq_of_provable_equiv.mp this
end

lemma lt_equiv : Iₒₚₑₙ' ⊢ ∀₁ x y, (x ≺ y) ⟷ ∃₁ z, (Succ z + x =' y) :=
begin
  refine (generalize $ generalize _), simp[fal_fn, ex_fn],
  suffices : ⤊⤊Iₒₚₑₙ' ⊢ (#1 ≼ #0) ⊓ (#1 ≠' #0) ⟷ ∃. (Succ #0 + #(1 + 1) =' #1),
    by simpa[lt, Lindenbaum.eq_of_provable_equiv_0, Lindenbaum.lt_eq] using this,
  simp[iff_equiv], split,
  { suffices : ⤊⤊Iₒₚₑₙ' ⊢ (∃. (#0 + #2 =' #1)) ⟶ ∼(#1 =' #0) ⟶ ∃. (Succ #0 + #2 =' #1),
    { simp[Lindenbaum.le_of_provable_imply_0, Lindenbaum.le_iff] at this ⊢,
      simpa[sdiff_eq] using sdiff_le_iff.mpr (by simpa[sdiff_eq] using this) },
    refine (imply_ex_of_fal_imply $ generalize $ deduction.mp $ rew_of_eq (#0 + #2) 1 (eq_symm $ by simp) _),
    simp[formula.pow_eq],
    have zero : ⤊⤊⤊Iₒₚₑₙ' +{ #0 + #2 =' #1 } ⊢ (#0 =' 0) ⟶ (#2 ≠' #0 + #2) ⟶ ∃. (Succ #0 + #3 =' #1 + #3),
    { refine (deduction.mp _), simp[Lindenbaum.le_of_provable_imply_0, Lindenbaum.rew_by_axiom₁] },
    have succ : ⤊⤊⤊Iₒₚₑₙ' +{ #0 + #2 =' #1 } ⊢ (∃₁ y, #1 =' Succ y) ⟶ (#2 ≠' #0 + #2) ⟶ ∃. (Succ #0 + #3 =' #1 + #3),
    { refine (imply_ex_of_fal_imply $ generalize $ deduction.mp $ deduction.mp $ use #0 _), simp[←sf_dsb], 
      simp[Herbrand.eq_of_provable_equiv_0, Lindenbaum.rew_by_axiom₂] },
    exact case_of_ax (zero_or_succ _ #0) zero succ },
  { refine (imply_ex_of_fal_imply $ generalize $ deduction.mp $ rew_of_eq (Succ #0 + #2) 1 (eq_symm $ by simp) _), simp,
    simp[Herbrand.le_iff_provable_le_0, Lindenbaum.eq_neg_of_provable_neg_0, -Lindenbaum.succ_add],
    simpa using Lindenbaum.add_right_cancel (⤊⤊⤊Iₒₚₑₙ' +{ Succ #0 + #2 =' #1 }) 0 0 (Succ ♯0) ♯2, }
end

lemma lt_equiv' (x y) : Iₒₚₑₙ' ⊢ (x ≺ y) ⟷ ∃₁ z, (Succ z + x^1 =' y^1) :=
by simpa[lt, fal_fn, ex_fn, ←term.pow_rew_distrib] using (lt_equiv _) ⊚ x ⊚ y 

lemma Lindenbaum.lt_eq (h₁ h₂ : Herbrand Iₒₚₑₙ' i) :
  (h₁ ≺' h₂) = ∃' (Succ ♯0 + h₁.pow =' h₂.pow : Lindenbaum Iₒₚₑₙ' (i + 1)) :=
by induction h₁ using fol.Herbrand.ind_on with t;
   induction h₂ using fol.Herbrand.ind_on with u;
   simpa[lt, fal_fn, ex_fn] using Lindenbaum.eq_of_provable_equiv.mp ((lt_equiv' (Iₒₚₑₙ'^i) t u))

@[simp, refl] lemma Lindenbaum.le_refl (h : Herbrand Iₒₚₑₙ i) : h ≤ h :=
by { have : h ≤ 0 + h, from robinson.Lindenbaum.le_add_self Iₒₚₑₙ i h 0,
     simpa using this }

@[simp] lemma Lindenbaum.le_succ_refl (h : Herbrand Iₒₚₑₙ i) : h ≤ Succ h :=
by { have : h ≤ 1 + h, from robinson.Lindenbaum.le_add_self Iₒₚₑₙ i h 1, 
     simpa[numeral_one_def] using this }

lemma le_transitive : Iₒₚₑₙ ⊢ ∀₁ x y z, (x ≼ y) ⟶ (y ≼ z) ⟶ (x ≼ z) :=
begin
  refine (generalize $ generalize $ generalize _), simp[fal_fn],
  suffices : ⤊⤊⤊Iₒₚₑₙ ⊢ ∃. (#0 + #3 =' #2) ⟶ ∃. (#0 + #2 =' #1) ⟶ ∃. (#0 + #3 =' #1),
  { simp[Lindenbaum.eq_top_of_provable_0, Lindenbaum.le_iff] at this ⊢, exact this },
  refine (imply_ex_of_fal_imply $ generalize $ deduction.mp $ imply_ex_of_fal_imply $ generalize $ deduction.mp $ use (#0 + #1) _),
  simp[←sf_dsb, formula.pow_eq],
  show (Iₒₚₑₙ^5) +{ #1 + #4 =' #3 } +{ #0 + #3 =' #2 } ⊢ #0 + #1 + #4 =' #2,
  by simp[Herbrand.eq_of_provable_equiv_0, Lindenbaum.rew_by_axiom₁_inv, Lindenbaum.rew_by_axiom₂_inv, add_assoc]
end

@[trans] lemma Lindenbaum.le_transitive {h₁ h₂ h₃ : Herbrand Iₒₚₑₙ i} : h₁ ≤ h₂ → h₂ ≤ h₃ → h₁ ≤ h₃ := λ le₁₂ le₂₃,
begin
  induction h₁ using fol.Herbrand.ind_on with t₁,
  induction h₂ using fol.Herbrand.ind_on with t₂,
  induction h₃ using fol.Herbrand.ind_on with t₃,
  have le₁₂ : Iₒₚₑₙ^i ⊢ t₁ ≼ t₂, from Herbrand.le_iff_provable_le.mpr le₁₂,
  have le₂₃ : Iₒₚₑₙ^i ⊢ t₂ ≼ t₃, from Herbrand.le_iff_provable_le.mpr le₂₃,
  have : Iₒₚₑₙ^i ⊢ (t₁ ≼ t₂) ⟶ (t₂ ≼ t₃) ⟶ (t₁ ≼ t₃), by simpa[fal_fn] using le_transitive _ ⊚ t₁ ⊚ t₂ ⊚ t₃,
  exact Herbrand.le_iff_provable_le.mp (this ⨀ le₁₂ ⨀ le₂₃)
end

lemma add_lt_of_lt_of_lt : Iₒₚₑₙ' ⊢ ∀₁ x y z v, (x ≺ y) ⟶ (z ≺ v) ⟶ (x + z ≺ y + v) :=
begin
  refine (generalize $ generalize $ generalize $ generalize _), simp[fal_fn],
  show Iₒₚₑₙ'^4 ⊢ (#3 ≺ #2) ⟶ (#1 ≺ #0) ⟶ (#3 + #1 ≺ #2 + #0),
  suffices : Iₒₚₑₙ'^4 ⊢ ∃. (Succ #0 + #4 =' #3) ⟶ ∃. (Succ #0 + #2 =' #1) ⟶ ∃. (Succ #0 + #4 + #2 =' #3 + #1),
  { simp[lt, Lindenbaum.eq_top_of_provable_0, Lindenbaum.lt_eq, add_pow, add_assoc] at this ⊢, simpa using this },
  refine (imply_ex_of_fal_imply $ generalize $ deduction.mp $ imply_ex_of_fal_imply $ generalize $ deduction.mp $ use (Succ #1 + #0) _),
  simp[←sf_dsb, formula.pow_eq],
  show (Iₒₚₑₙ'^6)+{ Succ #1 + #5 =' #4 }+{ Succ #0 + #3 =' #2 } ⊢ Succ (Succ #1 + #0) + #5 + #3 =' #4 + #2,
  simp[Herbrand.eq_of_provable_equiv_0, rew_by_axiom₁_inv, rew_by_axiom₂_inv],
  calc    (♯1 + ♯0 + ♯5 + ♯3 : Herbrand ((Iₒₚₑₙ'^6)+{ Succ #1 + #5 =' #4 }+{ Succ #0 + #3 =' #2 }) 0) 
        = (♯1 + (♯0 + ♯5) + ♯3) : by simp[add_assoc]
    ... = (♯1 + (♯5 + ♯0) + ♯3) : by simp[add_comm]
    ... = ♯1 + ♯5 + (♯0 + ♯3)   : by simp[add_assoc]
end

lemma eq_or_succ_le_of_le : Iₒₚₑₙ ⊢ ∀₁ x y, (x ≼ y) ⟶ (x =' y) ⊔ (Succ x ≼ y) :=
begin
  refine (generalize $ generalize _), simp[fal_fn],
  suffices : ⤊⤊Iₒₚₑₙ ⊢ ∃. (#0 + #2 =' #1) ⟶ (#1 =' #0) ⊔ ∃. (#0 + Succ #2 =' #1),
  { simp[Lindenbaum.eq_top_of_provable_0, Lindenbaum.le_iff] at this ⊢, exact this },
  refine (imply_ex_of_fal_imply $ generalize _), simp[formula.pow_eq],
  show Iₒₚₑₙ^3 ⊢ (#0 + #2 =' #1) ⟶ (#2 =' #1) ⊔ ∃. (#0 + Succ #3 =' #2),
  have zero : Iₒₚₑₙ^3 ⊢ (#0 =' 0) ⟶ (#0 + #2 =' #1) ⟶ (#2 =' #1) ⊔ ∃. (#0 + Succ #3 =' #2),
  { refine (deduction.mp $ deduction.mp _),
    simp[Lindenbaum.eq_top_of_provable_0, Lindenbaum.rew_by_axiom₁_inv, Lindenbaum.rew_by_axiom₂] },
  have succ : Iₒₚₑₙ^3 ⊢ (∃₁ y, #1 =' Succ y) ⟶ (#0 + #2 =' #1) ⟶ (#2 =' #1) ⊔ ∃. (#0 + Succ #3 =' #2),
  { refine (imply_ex_of_fal_imply $ generalize $ deduction.mp $ deduction.mp $ imply_or_right _ _ ⨀ use #0 _),
    simp[Lindenbaum.eq_top_of_provable_0, Lindenbaum.rew_by_axiom₁_inv, Lindenbaum.rew_by_axiom₂] },
  exact case_of_ax (zero_or_succ _ #0) zero succ
end

lemma le_or_ge : Iₒₚₑₙ ⊢ ∀₁ x y, (x ≼ y) ⊔ (y ≼ x) :=
begin
  have ind : Iₒₚₑₙ^1 ⊢ (#0 ≼ 0) ⊔ (0 ≼ #0) ⟶
                  ∀. ((#1 ≼ #0) ⊔ (#0 ≼ #1) ⟶ (#1 ≼ Succ #0) ⊔ (Succ #0 ≼ #1)) ⟶
                  ∀. (#1 ≼ #0) ⊔ (#0 ≼ #1),
  by simpa using Ind.I_succ_induction is_open ⤊Iₒₚₑₙ ((#1 ≼ #0) ⊔ (#0 ≼ #1)) (by simp[set.mem_def]),
  have zero : Iₒₚₑₙ^1 ⊢ (#0 ≼ 0) ⊔ (0 ≼ #0), from (imply_or_right _ _ ⨀ (by simp[Herbrand.le_iff_provable_le_0])),
  have succ : Iₒₚₑₙ^1 ⊢ ∀. ((#1 ≼ #0) ⊔ (#0 ≼ #1) ⟶ (#1 ≼ Succ #0) ⊔ (Succ #0 ≼ #1)),
  { refine generalize _, 
    have orl : Iₒₚₑₙ^2 ⊢ (#1 ≼ #0) ⟶ (#1 ≼ Succ #0) ⊔ (Succ #0 ≼ #1),
    { refine (deduction.mp $ imply_or_left _ _ ⨀ _),
      have : (Iₒₚₑₙ^2)+{ #1 ≼ #0 } ⊢ #1 ≼ #0, by simp,
      simp[Herbrand.le_iff_provable_le_0] at this ⊢,
      refine Lindenbaum.le_transitive _ _ this (by simp) },
    have orr : Iₒₚₑₙ^2 ⊢ (#0 ≼ #1) ⟶ (#1 ≼ Succ #0) ⊔ (Succ #0 ≼ #1),
    { refine (deduction.mp _),
      have eq      : (Iₒₚₑₙ^2) +{ #0 ≼ #1 } ⊢ (#0 =' #1) ⟶ (#1 ≼ Succ #0) ⊔ (Succ #0 ≼ #1),
      { refine (deduction.mp $ imply_or_left _ _ ⨀ _), simp[Herbrand.le_iff_provable_le_0, rew_by_axiom₁] },
      have succ_le : (Iₒₚₑₙ^2) +{ #0 ≼ #1 } ⊢ (Succ #0 ≼ #1) ⟶ (#1 ≼ Succ #0) ⊔ (Succ #0 ≼ #1),
        by simp[Lindenbaum.le_of_provable_imply_0],
      have : (Iₒₚₑₙ^2) +{ #0 ≼ #1 } ⊢ (#0 =' #1) ⊔ (Succ #0 ≼ #1), 
        from deduction.mpr (show (Iₒₚₑₙ^2) ⊢ (#0 ≼ #1) ⟶ (#0 =' #1) ⊔ (Succ #0 ≼ #1),
        by simpa[fal_fn] using eq_or_succ_le_of_le _ ⊚ #0 ⊚ #1),
      exact case_of_ax this eq succ_le },
    exact or_imply _ _ _ ⨀ orl ⨀ orr },
  refine (generalize _), simp[fal_fn], exact ind ⨀ zero ⨀ succ
end

@[simp] lemma prec_open (t u : term LA') : coe_inv_is_open defs (t ≺ u) :=
by { have : ((coe : LA'.pr 2 → LA'.pr 2) (sum.inr additional_pr.lt)) = sum.inr additional_pr.lt,
       from language.language_translation_coe.coe_pr_eq_self _,
     simp[lt, this] }

lemma lt_mul_of_nonzero_of_lt :
  Iₒₚₑₙ' ⊢ ∀₁ x y z, (x ≺ y) ⟶ (z ≠' 0) ⟶ (x * z ≺ y * z) :=
begin
  have ind : Iₒₚₑₙ'^2 ⊢
       ((#1 ≺ #0) ⟶ ((0 : term LA) ≠' 0) ⟶ (#1 * 0 ≺ #0 * 0)) ⟶
    ∀. (((#2 ≺ #1) ⟶ (#0 ≠' 0) ⟶ (#2 * #0 ≺ #1 * #0)) ⟶ (#2 ≺ #1) ⟶ (Succ #0 ≠' 0) ⟶ (#2 * Succ #0 ≺ #1 * Succ #0)) ⟶
    ∀. ((#2 ≺ #1) ⟶ (#0 ≠' 0) ⟶ (#2 * #0 ≺ #1 * #0)),
  by simpa[additional.lt] using
    I_succ_induction_LA (Iₒₚₑₙ'^2) ((#2 ≺ #1) ⟶ (#0 ≠' 0) ⟶ (#2 * #0 ≺ #1 * #0)) (by simp),
  have zero : Iₒₚₑₙ'^2 ⊢ (#1 ≺ #0) ⟶ ((0 : term LA) ≠' 0) ⟶ (#1 * 0 ≺ #0 * 0), by simp[Lindenbaum.eq_top_of_provable_0],
  have succ : Iₒₚₑₙ'^2 ⊢ ∀. (((#2 ≺ #1) ⟶ (#0 ≠' 0) ⟶ (#2 * #0 ≺ #1 * #0)) ⟶ (#2 ≺ #1) ⟶ (Succ #0 ≠' 0) ⟶ (#2 * Succ #0 ≺ #1 * Succ #0)),
  { refine (generalize $ deduction.mp $ deduction.mp $ deduction.mp _), simp[-iff_and],
    have zero : (Iₒₚₑₙ'^3) +{ (#2 ≺ #1) ⟶ (#0 ≠' 0) ⟶ (#2 * #0 ≺ #1 * #0) } +{ #2 ≺ #1 } +{ Succ #0 ≠' 0 } ⊢ (#0 =' 0) ⟶ (#2 * Succ #0 ≺ #1 * Succ #0),
    { refine (deduction.mp $ rew_of_eq 0 0 (by simp) _),
      have : (Iₒₚₑₙ'^3) +{ (#2 ≺ #1) ⟶ (#0 ≠' 0) ⟶ (#2 * #0 ≺ #1 * #0) } +{ #2 ≺ #1 } +{ Succ #0 ≠' 0 }+{ #0 =' 0 } ⊢ #2 ≺ #1, by simp,
      simpa[Herbrand.iff_abberavation₂_0] using this },
    have nonzero : (Iₒₚₑₙ'^3) +{ (#2 ≺ #1) ⟶ (#0 ≠' 0) ⟶ (#2 * #0 ≺ #1 * #0) } +{ #2 ≺ #1 } +{ Succ #0 ≠' 0 } ⊢ (#0 ≠' 0) ⟶ (#2 * Succ #0 ≺ #1 * Succ #0),
    { refine (deduction.mp _),
      have lt : (Iₒₚₑₙ'^3) +{ (#2 ≺ #1) ⟶ (#0 ≠' 0) ⟶ (#2 * #0 ≺ #1 * #0) } +{ #2 ≺ #1 } +{ Succ #0 ≠' 0 } +{ #0 ≠' 0 } ⊢ #2 * #0 ≺ #1 * #0,
        from (show _ ⊢ (#2 ≺ #1) ⟶ (#0 ≠' 0) ⟶ (#2 * #0 ≺ #1 * #0), by simp) ⨀ (by simp) ⨀ (by simp),
      have : (Iₒₚₑₙ'^3) ⊢ (#2 * #0 ≺ #1 * #0) ⟶ (#2 ≺ #1) ⟶ (#2 * #0 + #2 ≺ #1 * #0 + #1),
      by simpa[fal_fn] using ((add_lt_of_lt_of_lt (Iₒₚₑₙ'^3)) ⊚ (#2 * #0) ⊚ (#1 * #0) ⊚ #2 ⊚ #1),
      have : (Iₒₚₑₙ'^3) +{ (#2 ≺ #1) ⟶ (#0 ≠' 0) ⟶ (#2 * #0 ≺ #1 * #0) } +{ #2 ≺ #1 } +{ Succ #0 ≠' 0 } +{ #0 ≠' 0 } ⊢ #2 * #0 + #2 ≺ #1 * #0 + #1,
        from this.extend ⨀ lt ⨀ (by simp),
      simp[Lindenbaum.eq_top_of_provable_0] at this ⊢, exact this },
    refine cases_of _ _ zero nonzero },
  refine (generalize $ generalize _), simp[fal_fn], exact ind ⨀ zero ⨀ succ
end

#check 0  /-
lemma mul_right_cancel_of_nonzero_aux : Iₒₚₑₙ' ⊢ ∀₁ x y z, (z ≠' 0) ⟶ (x * z =' y * z) ⟶ (x =' y) :=
begin
  refine (generalize $ generalize $ generalize _), simp[fal_fn],
  suffices : Iₒₚₑₙ'^3 ⊢ (#0 ≠' 0) ⟶ (#2 ≠' #1) ⟶ (#2 * #0 ≠' #1 * #0),
  {  simp[Lindenbaum.eq_top_of_provable_0] at this ⊢, simpa[sup_comm] using this },
  have : Iₒₚₑₙ'^3 ⊢ ∀₁ x y z, (x ≺ y) ⟶ (z ≠' 0) ⟶ (x * z ≺ y * z),
  have := (lt_mul_of_nonzero_of_lt (Iₒₚₑₙ'^3)),

  simp[fal_fn] at this,
  have orl : Iₒₚₑₙ' ⊢ (#1 ≼ #2) ⟶ ∼(#0 =' 0) ⟶ ∼(#2 =' #1) ⟶ ∼(#2 * #0 =' #1 * #0),
  { refine (deduction.mp $ deduction.mp $ deduction.mp $ ne_symm _),
    have : Iₒₚₑₙ' +{ #1 ≼ #2 } +{ #0 ≠' 0 } +{ #2 ≠' #1 } ⊢ _, { have h := (this ⊚ #1 ⊚ #2 ⊚ #0),  }, 
    have := this ⨀ (by {simp[lessthan_def, fal_fn], refine ne_symm (by simp) }) ⨀ (by simp[fal_fn]),
    simp[lessthan_def, fal_fn] at this, exact this.2 },
  have orr : Iₒₚₑₙ ⊢ (#2 ≼ #1) ⟶ ∼(#0 =' 0) ⟶ ∼(#2 =' #1) ⟶ ∼(#2 * #0 =' #1 * #0),
  { refine (deduction.mp $ deduction.mp $ deduction.mp _),
    have : Iₒₚₑₙ +{ #2 ≼ #1 } +{ #0 ≠' 0 } +{ #2 ≠' #1 } ⊢ _, from provable.extend (this ⊚ #2 ⊚ #1 ⊚ #0), 
    have := this ⨀ (by simp[lessthan_def, fal_fn]) ⨀ (by simp[fal_fn]),
    simp[lessthan_def, fal_fn] at this, exact this.2 },
  refine case_of_ax (show Iₒₚₑₙ ⊢ (#1 ≼ #2) ⊔ (#2 ≼ #1), by simpa[fal_fn] using le_or_ge ⊚ #1 ⊚ #2) orl orr
end

lemma one_divides : Iₒₚₑₙ ⊢ ∀₁ x, 1 ⍭ x :=
begin
  simp[divides_def, fal_fn, numeral_one_def],
  refine (generalize $ use #1 _), 
  simp[Herbrand.eq_of_provable_equiv_0]
end

lemma divides_self : Iₒₚₑₙ ⊢ ∀₁ x, x ⍭ x :=
begin
  simp[divides_def, fal_fn, numeral_one_def],
  refine (generalize $ use (Succ 0) _), 
  simp[Herbrand.eq_of_provable_equiv_0]
end

lemma divides_zero : Iₒₚₑₙ ⊢ ∀₁ x, x ⍭ 0 :=
begin
  simp[divides_def, fal_fn],
  refine (generalize $ use 0 _), 
  simp[Herbrand.eq_of_provable_equiv_0]
end

lemma divides_trans : Iₒₚₑₙ ⊢ ∀₁ x y z, (x ⍭ y) ⟶ (y ⍭ z) ⟶ (x ⍭ z) :=
begin
  simp[divides_def, fal_fn],
  refine (generalize $ generalize $ generalize $
    imply_ex_of_fal_imply $ generalize $ deduction.mp $
    imply_ex_of_fal_imply $ generalize $ deduction.mp $ use (#0 * #1) _),
  simp[formula.pow_eq, ←sf_dsb],
  show Iₒₚₑₙ +{ #1 * #5 =' #4 } +{ #0 * #4 =' #3 } ⊢ #0 * #1 * #5 =' #3,
  simp[Herbrand.eq_of_provable_equiv_0, rew_by_axiom₁_inv, rew_by_axiom₂_inv, mul_assoc]
end
-/
end Iopen
/-ₒ
def 


lemma add_symm : Iₒₚₑₙ ⊢ ∀₁ x y, (x + y =' y + x) :=
begin
  refine (generalize _), simp[fal_fn],
  have zero : Iₒₚₑₙ ⊢ (#0 =' 0) ⟶ ∀. (#1 + #0 =' #0 + #1),
  { refine (deduction.mp $ generalize _), simp[←sf_dsb, Herbrand.eq_of_provable_equiv_0, rew_by_axiom₁] },
  have succ : Iₒₚₑₙ ⊢ (∃₁ y, #1 =' Succ y) ⟶ ∀. (#1 + #0 =' #0 + #1),
  { refine (imply_ex_of_fal_imply $ generalize $ deduction.mp $ rew_of_eq (Succ #0) 1 (by simp) $ generalize _), simp[formula.pow_eq, ←sf_dsb],
    suffices : Iₒₚₑₙ ⊢ Succ #1 + #0 =' #0 + Succ #1, by simp[this],
     
     }
end




def Ind {C : Theory LA} : Lindenbaum 𝐈C 1 → Prop := λ l, ∃ p, p ∈ C ∧ l = ⟦p⟧ᴸ

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
  (succ : m.pow ≤ (♯0 ⊳ l.pow)ᶜ ⊔ (Succ ♯0) ⊳ l.pow) : m ≤ ∀. l :=
begin
  induction l using fol.Lindenbaum.ind_on with p,
  have P := (provable_top_iff0.mpr (Ind_mem _ h)),
  have trn : (0 : Herbrand 𝐈C 0) ⊳ ⟦p⟧ᴸ ⊓ ∀. ((♯0 ⊳ pow ⟦p⟧ᴸ)ᶜ ⊔ (Succ ♯0) ⊳ pow ⟦p⟧ᴸ) ≤ ∀. ⟦p⟧ᴸ,
  { simp[succ_induction, Lindenbaum.subst_eq, Lindenbaum.pow_eq, compl_sup_iff_le,
    le_of_provable_imply_0, Herbrand.var_eq] at P, refine P },
  have succ' : m ≤ ∀. ((♯0 ⊳ pow ⟦p⟧ᴸ)ᶜ ⊔ (Succ ♯0) ⊳ pow ⟦p⟧ᴸ),
    from Lindenbaum.proper.pow_le_le_fal succ,
  have : m ≤ 0 ⊳ ⟦p⟧ᴸ ⊓ ∀. ((♯0 ⊳ pow ⟦p⟧ᴸ)ᶜ ⊔ (Succ ♯0) ⊳ pow ⟦p⟧ᴸ), 
    from le_inf zero succ',
  exact le_trans this trn
end

lemma Lindenbaum_induction_top {p : formula LA} (l : Lindenbaum 𝐈C 1)
  (h : Ind l)
  (zero : 0 ⊳ l = ⊤)
  (succ : ♯0 ⊳ l.pow ≤ (Succ ♯0) ⊳ l.pow) : (∀. l : Lindenbaum 𝐈C 0) = ⊤ :=
begin
  induction l using fol.Lindenbaum.ind_on with p,
  have P := (provable_top_iff0.mpr (Ind_mem _ h)),
  have : (0 : Herbrand 𝐈C 0) ⊳ ⟦p⟧ᴸ ⊓ ∀. ((♯0 ⊳ pow ⟦p⟧ᴸ)ᶜ ⊔ (Succ ♯0) ⊳ pow ⟦p⟧ᴸ) ≤ ∀. ⟦p⟧ᴸ,
  { simp[succ_induction, Lindenbaum.subst_eq, Lindenbaum.pow_eq, compl_sup_iff_le,
    le_of_provable_imply_0, Herbrand.var_eq] at P, exact P },
  simp[zero, succ] at this,
  have eqn : (♯0 ⊳ pow ⟦p⟧ᴸ)ᶜ ⊔ (Succ ♯0) ⊳ pow ⟦p⟧ᴸ = ⊤,
    from ((♯0 ⊳ pow ⟦p⟧ᴸ).compl_sup_iff_le ((Succ ♯0) ⊳ pow ⟦p⟧ᴸ)).mpr succ,
  simp[eqn] at this, exact this
end

def Lindenbaum.bd_fal {T : Theory LA} (l : Lindenbaum T (i + 1)) (h : Herbrand T i) : Lindenbaum T i := ∀. ((♯0 ≼ h.pow)ᶜ ⊔ l)
def Lindenbaum.bd_ex {T : Theory LA} (l : Lindenbaum T (i + 1)) (h : Herbrand T i) : Lindenbaum T i := ∃. ((♯0 ≼ h.pow) ⊓ l)

notation `∀._{≼ `:95 h `} ` l :90 := Lindenbaum.bd_fal l h 
notation `∃._{≼ `:95 h `} ` l :90 := Lindenbaum.bd_ex l h 

theorem collection (p : formula LA) [proper 0 (𝚺⁰1)] :
  𝐈𝚺⁰1 ⊢ ([∀. ≼ #0] ∃. p) ⟶ ∃. [∀. ≼ #1] [∃. ≼ #1] ((p^3).rew ı[4 ⇝ #0]).rew ı[3 ⇝ #1] :=
begin
  simp[le_of_provable_imply_0, bounded_fal, bounded_ex, Lindenbaum.pow_eq p, Herbrand.subst_eq, Lindenbaum.subst_eq],
  suffices : ∀ l : Lindenbaum 𝐐+𝐈𝚺⁰1 2,
    ∀._{≼ ♯1} ∃. l ≤ ∃. ∀._{≼ ♯2} ∃._{≼ ♯2} (♯1 ⊳ ♯0 ⊳ l.pow.pow.pow),
  { sorry },
  intros l,
  have : ∀._{≼ ♯1} ∃. l ≤ ∀. ∀. ((♯0 ≼ ♯1)ᶜ ⊔ ∃. ∀._{≼ ♯1} ∃._{≼ ♯1} l.pow.pow.pow),
  { refine Lindenbaum_induction _ _ _ _ _; sorry }
  
end

theorem collection (p : formula LA) [proper 0 (𝚺⁰1)] : 𝐐+𝐈𝚺⁰1 ⊢ ([∀. ≼ #0] ∃. p) ⟶ ∃. [∀. ≼ #1] [∃. ≼ #1] p :=
begin
  refine deduction.mp _,
  have : ∀ n, ∃ m, (((ı[0 ⇝ #0] ^ 1) ^ 1) ^ 1) m = (#n : term LA) :=
    (rewriting_sf_perm $ rewriting_sf_perm $ rewriting_sf_perm $ slide_perm _ #0), 
  rcases formula.total_rew_inv p this with ⟨q, e_q⟩,
  suffices : 𝐐+𝐈𝚺⁰1+{[∀. ≼ #0] ∃. p} ⊢ ∀. ∀. ((#0 ≼ #1) ⟶ ∃. [∀. ≼ #1] [∃. ≼ #1] q),
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
-/
end arithmetic

end fol
