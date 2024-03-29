import lib.lib order.bounded_order

universe u

open_locale logic_symbol

class intuitionistic_logic {F : Sort*} [has_logic_symbol F] (P : F → Prop) :=
(modus_ponens {p q : F} : P (p ⟶ q) → P p → P q)
(imply₁ {p q : F} : P (p ⟶ q ⟶ p))
(imply₂ {p q r : F} : P ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r))
(conj₁ {p q : F} : P (p ⊓ q ⟶ p))
(conj₂ {p q : F} : P (p ⊓ q ⟶ q))
(conj₃ {p q : F} : P (p ⟶ q ⟶ p ⊓ q))
(disj₁ {p q : F} : P (p ⟶ p ⊔ q))
(disj₂ {p q : F} : P (q ⟶ p ⊔ q))
(disj₃ {p q r : F} : P ((p ⟶ r) ⟶ (q ⟶ r) ⟶ p ⊔ q ⟶ r))
(neg₁ {p q : F} : P ((p ⟶ q) ⟶ (p ⟶ ∼q) ⟶ ∼p))
(neg₂ {p q : F} : P (p ⟶ ∼p ⟶ q))
(provable_top : P ⊤)
(bot_eq : (⊥ : F) = ∼⊤)

class classical_logic {F : Sort*} [has_logic_symbol F] (P : set F) :=
(modus_ponens {p q : F} : p ⟶ q ∈ P → p ∈ P → q ∈ P)
(imply₁ {p q : F} : p ⟶ q ⟶ p ∈ P)
(imply₂ {p q r : F} : (p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r ∈ P)
(contraposition {p q : F} : (∼p ⟶ ∼q) ⟶ q ⟶ p ∈ P)
(provable_top : ⊤ ∈ P)
(bot_eq : (⊥ : F) = ∼⊤)
(and_def {p q : F} : p ⊓ q = ∼(p ⟶ ∼q))
(or_def {p q : F} : p ⊔ q = ∼p ⟶ q)

attribute [simp] classical_logic.imply₁ classical_logic.imply₂ classical_logic.contraposition
  classical_logic.provable_top

class axiomatic_classical_logic' (F : Sort*) [has_logic_symbol F] extends has_turnstile F :=
(classical {T : set F} : classical_logic ((⊢) T : F → Prop))
(by_axiom {T : set F} {p : F} : p ∈ T → T ⊢ p)

class axiomatic_classical_logic (F : Sort*) [has_logic_symbol F] extends axiomatic_classical_logic' F :=
(deduction' {T : set F} {p q : F} : insert p T ⊢ q → T ⊢ p ⟶ q)
(weakening {T : set F} {U : set F} {p : F} : T ⊆ U → T ⊢ p → U ⊢ p)

namespace classical_logic

variables {F : Type*} [has_logic_symbol F]
  (P : set F) (T : set F) [CL : classical_logic P]
include CL

@[simp] lemma neg_top_eq : (∼⊤ : F) = ⊥ := eq.symm (bot_eq P)

variables {P}

@[simp] lemma not_top_eq_bot : (∼⊤ : F) = ⊥ := eq.symm (classical_logic.bot_eq P)

local infixl ` ⨀ `:90 := modus_ponens

@[simp] lemma refl (p : F) : p ⟶ p ∈ P :=
begin
  have l₀ : (p ⟶ (p ⟶ p) ⟶ p) ⟶ (p ⟶ p ⟶ p) ⟶ p ⟶ p ∈ P, simp,
  have l₁ : p ⟶ (p ⟶ p) ⟶ p ∈ P, simp,
  have l₂ : (p ⟶ p ⟶ p) ⟶ p ⟶ p ∈ P, refine l₀ ⨀ l₁,
  have l₃ : p ⟶ p ⟶ p ∈ P, simp,
  simp[set.mem_def],
  refine l₂ ⨀ l₃
end

variables {T}

@[simp] lemma hyp_right {p : F} (h : p ∈ P) (q) : q ⟶ p ∈ P :=
by { have : p ⟶ q ⟶ p ∈ P, simp, exact this ⨀ h }

@[simp] lemma T_hyp_eliminate {p} : ⊤ ⟶ p ∈ P ↔ p ∈ P :=
⟨λ h, by { have : ⊤ ∈ P, simp, exact h ⨀ this }, λ h, by simp[h]⟩

lemma modus_ponens_hyp {p q r : F} (hqr : p ⟶ q ⟶ r ∈ P) (hq : p ⟶ q ∈ P) : p ⟶ r ∈ P :=
by { have : (p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r ∈ P, simp, exact this ⨀ hqr ⨀ hq }

local infixl ` ⨀₁ `:90 := modus_ponens_hyp

lemma modus_ponens_hyp₂ {p q r s : F} (hqr : p ⟶ q ⟶ r ⟶ s ∈ P) (hq : p ⟶ q ⟶ r ∈ P) : p ⟶ q ⟶ s ∈ P :=
by { have : p ⟶ (q ⟶ r ⟶ s) ⟶ (q ⟶ r) ⟶ q ⟶ s ∈ P, simp, exact this ⨀₁ hqr ⨀₁ hq }

local infixl ` ⨀₂ `:90 := modus_ponens_hyp₂

lemma modus_ponens_hyp₃ {p q r s t : F} (hqr : p ⟶ q ⟶ r ⟶ s ⟶ t ∈ P) (hq : p ⟶ q ⟶ r ⟶ s ∈ P) : p ⟶ q ⟶ r ⟶ t ∈ P :=
by { have : p ⟶ q ⟶ (r ⟶ s ⟶ t) ⟶ (r ⟶ s) ⟶ r ⟶ t ∈ P, simp, exact this ⨀₂ hqr ⨀₂ hq }

local infixl ` ⨀₃ `:90 := modus_ponens_hyp₃

lemma impl_trans {p q r : F} : (p ⟶ q ∈ P) → (q ⟶ r ∈ P) → (p ⟶ r ∈ P) := λ h₁ h₂,
begin
  have l₁ : (p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ (p ⟶ r) ∈ P, simp,  
  have l₂ : (p ⟶ q ⟶ r) ∈ P, simp[h₂],
  have l₃ : (p ⟶ q) ⟶ (p ⟶ r) ∈ P, from l₁ ⨀ l₂,
  exact l₃ ⨀ h₁
end

@[simp] lemma imply₁' {p q r : F} : p ⟶ q ⟶ r ⟶ p ∈ P :=
begin
  have lmm₁ : p ⟶ q ⟶ p ⟶ r ⟶ p ∈ P, simp,
  have lmm₂ : p ⟶ q ⟶ p ∈ P, simp,
  exact lmm₁ ⨀₂ lmm₂
end

@[simp] lemma dne (p : F) : ∼∼p ⟶ p ∈ P :=
begin
  have lmm₁ : ∼∼p ⟶ (∼∼∼∼p ⟶ ∼∼p) ⟶ ∼p ⟶ ∼∼∼p ∈ P, simp,
  have lmm₂ : ∼∼p ⟶ ∼∼∼∼p ⟶ ∼∼p ∈ P, simp,
  have lmm₃ : ∼∼p ⟶ (∼p ⟶ ∼∼∼p) ⟶ ∼∼p ⟶ p ∈ P, simp,  
  have lmm₄ : ∼∼p ⟶ ∼p ⟶ ∼∼∼p ∈ P, from lmm₁ ⨀₁ lmm₂,
  have lmm₅ : ∼∼p ⟶ ∼∼p ⟶ p ∈ P, from lmm₃ ⨀₁ lmm₄,
  have lmm₆ : ∼∼p ⟶ ∼∼p ∈ P, simp,
  exact lmm₅ ⨀₁ lmm₆
end

@[simp] lemma dni (p : F) : p ⟶ ∼∼p ∈ P :=
by { have : (∼∼∼p ⟶ ∼p) ⟶ p ⟶ ∼∼p ∈ P, simp, exact this ⨀ (by simp) }

@[simp] lemma dn_iff {p : F} : ∼∼p ∈ P ↔ p ∈ P :=
⟨λ h, (show ∼∼p ⟶ p ∈ P, by simp) ⨀ h, λ h, (show p ⟶ ∼∼p ∈ P, by simp) ⨀ h⟩

@[simp] lemma dn1_iff {p q : F} : (∼∼p ⟶ q ∈ P) ↔ (p ⟶ q ∈ P) :=
⟨impl_trans (dni _), impl_trans (dne _)⟩

@[simp] lemma dn2_iff {p q : F} : (p ⟶ ∼∼q ∈ P) ↔ (p ⟶ q ∈ P) :=
⟨λ h, impl_trans h (dne _), λ h, impl_trans h (dni _)⟩

lemma explosion {p : F} (h₁ : p ∈ P) (h₂ : ∼p ∈ P) {q : F} : q ∈ P :=
begin
  have : ∼p ⟶ ∼q ⟶ ∼p ∈ P, simp,
  have : ∼q ⟶ ∼p ∈ P, from this ⨀ h₂,
  have : p ⟶ q ∈ P, from (show (∼q ⟶ ∼p) ⟶ p ⟶ q ∈ P, by simp) ⨀ this,
  exact this ⨀ h₁
end

lemma explosion_hyp {p q : F} (h₁ : p ⟶ q ∈ P) (h₂ : p ⟶ ∼q ∈ P) {r : F} : p ⟶ r ∈ P :=
begin
  have : p ⟶ ∼q ⟶ ∼r ⟶ ∼q ∈ P, simp,
  have : p ⟶ ∼r ⟶ ∼q ∈ P, from this ⨀₁ h₂,
  have : p ⟶ q ⟶ r ∈ P, from (show p ⟶ (∼r ⟶ ∼q) ⟶ q ⟶ r ∈ P, by simp) ⨀₁ this,
  exact this ⨀₁ h₁
end

lemma explosion_hyp₂ {p q r : F} (h₁ : p ⟶ q ⟶ r ∈ P) (h₂ : p ⟶ q ⟶ ∼r ∈ P) {s : F} : p ⟶ q ⟶ s ∈ P :=
begin
  have : p ⟶ q ⟶ ∼r ⟶ ∼s ⟶ ∼r ∈ P, simp,
  have : p ⟶ q ⟶ ∼s ⟶ ∼r ∈ P, from this ⨀₂ h₂,
  have : p ⟶ q ⟶ r ⟶ s ∈ P, from (show p ⟶ q ⟶ (∼s ⟶ ∼r) ⟶ r ⟶ s ∈ P, by simp) ⨀₂ this,
  exact this ⨀₂ h₁
end

@[simp] lemma hyp_bot (p : F) : ⊥ ⟶ p ∈ P :=
explosion_hyp (show (⊥ ⟶ ⊤ : F) ∈ P, by simp) (show (⊥ : F) ⟶ ∼⊤ ∈ P, by simp[neg_top_eq P])

lemma contrapose {p q : F} : (∼p ⟶ ∼q ∈ P) ↔ (q ⟶ p ∈ P) :=
⟨λ h, (show (∼p ⟶ ∼q) ⟶ q ⟶ p ∈ P, by simp) ⨀ h, λ h,
  by { have : ∼∼q ⟶ p ∈ P, from impl_trans (show ∼∼q ⟶ q ∈ P, by simp) h,
       exact (show (∼∼q ⟶ ∼∼p) ⟶ ∼p ⟶ ∼q ∈ P, by simp) ⨀ (impl_trans this (show p ⟶ ∼∼p ∈ P, by simp)) }⟩

lemma neg_hyp {p : F} (h : p ⟶ ∼p ∈ P) : ∼p ∈ P :=
begin
  have : p ⟶ ∼(p ⟶ ∼p) ∈ P,
  { have lmm₁ : p ⟶ p ∈ P, { simp }, exact explosion_hyp lmm₁ h },
  have : (p ⟶ ∼p) ⟶ ∼p ∈ P, from impl_trans (dni _) (contrapose.mpr this),
  exact this ⨀ h
end

lemma raa {p : F} (q : F) (h₁ : p ⟶ q ∈ P) (h₂ : p ⟶ ∼q ∈ P) : ∼p ∈ P :=
neg_hyp (explosion_hyp h₁ h₂)

@[simp] lemma and_left (p q : F) : p ⊓ q ⟶ p ∈ P :=
begin
  simp[and_def P],
  have : ∼p ⟶ p ⟶ ∼q ∈ P, from explosion_hyp₂ (show ∼p ⟶ p ⟶ p ∈ P, by simp) (show ∼p ⟶ p ⟶ ∼p ∈ P, by simp),
  have : ∼(p ⟶ ∼q) ⟶ ∼∼p ∈ P, from contrapose.mpr this,
  simp* at*
end

@[simp] lemma and_right (p q : F) : p ⊓ q ⟶ q ∈ P :=
begin
  simp[and_def P],
  have : ∼q ⟶ p ⟶ ∼q ∈ P, simp,
  have : ∼(p ⟶ ∼q) ⟶ q ∈ P, from impl_trans (contrapose.mpr this) (by simp),
  exact this
end

@[simp] lemma and_inply_left {p₁ p₂ q : F} : (p₁ ⟶ q) ⟶ p₁ ⊓ p₂ ⟶ q ∈ P :=
(show (p₁ ⟶ q) ⟶ p₁ ⊓ p₂ ⟶ p₁ ⟶ q ∈ P, by simp) ⨀₂ (show (p₁ ⟶ q) ⟶ p₁ ⊓ p₂ ⟶ p₁ ∈ P, by simp)

lemma and_imply_of_imply_left {p₁ p₂ q : F} (h : p₁ ⟶ q ∈ P) : p₁ ⊓ p₂ ⟶ q ∈ P :=
(show (p₁ ⟶ q) ⟶ p₁ ⊓ p₂ ⟶ q ∈ P, by simp) ⨀ h

@[simp] lemma and_imply_right {p₁ p₂ q : F} : (p₂ ⟶ q) ⟶ p₁ ⊓ p₂ ⟶ q ∈ P :=
(show (p₂ ⟶ q) ⟶ p₁ ⊓ p₂ ⟶ p₂ ⟶ q ∈ P, by simp) ⨀₂ (show (p₂ ⟶ q) ⟶ p₁ ⊓ p₂ ⟶ p₂ ∈ P, by simp)

lemma and_imply_of_imply_right {p₁ p₂ q : F} (h : p₂ ⟶ q ∈ P) : p₁ ⊓ p₂ ⟶ q ∈ P :=
(show (p₂ ⟶ q) ⟶ p₁ ⊓ p₂ ⟶ q ∈ P, by simp) ⨀ h

@[simp] lemma iff_and_p {p q : F} : (p ⊓ q ∈ P) ↔ (p ∈ P ∧ q ∈ P) :=
⟨λ h, by { split,
   { exact modus_ponens (show p ⊓ q ⟶ p ∈ P, by simp) h },
   { exact modus_ponens (show p ⊓ q ⟶ q ∈ P, by simp) h } },
 λ h, by { simp[and_def P], rcases h with ⟨h₁, h₂⟩,
   have : (p ⟶ ∼q) ⟶ ∼q ∈ P, from (show (p ⟶ ∼q) ⟶ p ⟶ ∼q ∈ P, by simp) ⨀₁ (by simp[h₁]),
   have : q ⟶ ∼(p ⟶ ∼q) ∈ P, from impl_trans (dni _) (contrapose.mpr this),
   exact modus_ponens this h₂ }⟩

@[simp] lemma conjunction_iff {n} {p : finitary F n} : (finitary.conjunction n p ∈ P) ↔ (∀ i, p i ∈ P) :=
by { induction n with n IH; simp*,
     { split,
       { rintros h i, refine fin.last_cases _ _ i; simp[h] },
       { intros h, simp[h] } } }

@[simp] lemma list_conjunction_iff {l : list F} : (l.conjunction ∈ P) ↔ (∀ p ∈ l, p ∈ P) :=
by induction l with a l IH; simp*

lemma iff_equiv_p {p q : F} : (p ⟷ q ∈ P) ↔ (p ⟶ q ∈ P ∧ q ⟶ p ∈ P) :=
by simp[lrarrow_def, iff_and_p]

lemma iff_of_equiv {p q : F} (h : p ⟷ q ∈ P) : p ∈ P ↔ q ∈ P :=
by { simp[iff_equiv_p] at h, refine ⟨λ hp, h.1 ⨀ hp, λ hq, h.2 ⨀ hq⟩ }

lemma of_equiv {p₁ p₂ : F} (h : p₁ ∈ P) (hp : p₁ ⟷ p₂ ∈ P) : p₂ ∈ P :=
by { simp[iff_equiv_p] at hp, refine hp.1 ⨀ h }

lemma equiv_imply_of_equiv {p₁ q₁ p₂ q₂ : F} (hp : p₁ ⟷ p₂ ∈ P) (hq : q₁ ⟷ q₂ ∈ P) : (p₁ ⟶ q₁) ⟷ (p₂ ⟶ q₂) ∈ P :=
begin
  simp[iff_equiv_p] at*, split,
  { have : (p₁ ⟶ q₁) ⟶ p₂ ⟶ q₁ ∈ P, from (show (p₁ ⟶ q₁) ⟶ p₂ ⟶ p₁ ⟶ q₁ ∈ P, by simp) ⨀₂ (by simp[hp]),
    exact (show (p₁ ⟶ q₁) ⟶ p₂ ⟶ q₁ ⟶ q₂ ∈ P, by simp[hq]) ⨀₂ this },
  { have : (p₂ ⟶ q₂) ⟶ p₁ ⟶ q₂ ∈ P, from (show (p₂ ⟶ q₂) ⟶ p₁ ⟶ p₂ ⟶ q₂ ∈ P, by simp) ⨀₂ (by simp[hp]),
    exact (show (p₂ ⟶ q₂) ⟶ p₁ ⟶ q₂ ⟶ q₁ ∈ P, by simp[hq]) ⨀₂ this }
end

lemma imply_of_equiv {p₁ q₁ p₂ q₂ : F} (h : p₁ ⟶ q₁ ∈ P) (hp : p₁ ⟷ p₂ ∈ P) (hq : q₁ ⟷ q₂ ∈ P) : p₂ ⟶ q₂ ∈ P :=
by { have : (p₁ ⟶ q₁) ⟶ p₂ ⟶ q₂ ∈ P ∧ (p₂ ⟶ q₂) ⟶ p₁ ⟶ q₁ ∈ P, from iff_equiv_p.mp (equiv_imply_of_equiv hp hq),
     exact this.1 ⨀ h }

lemma equiv_neg_of_equiv {p₁ p₂ : F} (hp : p₁ ⟷ p₂ ∈ P) : ∼p₁ ⟷ ∼p₂ ∈ P :=
by simp[iff_equiv_p, contrapose] at*; simp[hp]

lemma neg_of_equiv {p₁ p₂ : F} (h : ∼p₁ ∈ P) (hp : p₁ ⟷ p₂ ∈ P) : ∼p₂ ∈ P :=
by { have : ∼p₁ ⟶ ∼p₂ ∈ P, from (iff_equiv_p.mp (equiv_neg_of_equiv hp)).1, exact this ⨀ h }

lemma equiv_and_of_equiv {p₁ q₁ p₂ q₂: F} (hp : p₁ ⟷ p₂ ∈ P) (hq : q₁ ⟷ q₂ ∈ P) : p₁ ⊓ q₁ ⟷ p₂ ⊓ q₂ ∈ P :=
by { simp only [and_def P], refine equiv_neg_of_equiv (equiv_imply_of_equiv hp (equiv_neg_of_equiv hq)) }

lemma equiv_conjunction_of_equiv {n} {p₁ p₂ : finitary F n} (hp : ∀ i, p₁ i ⟷ p₂ i ∈ P) :
  finitary.conjunction n p₁ ⟷ finitary.conjunction n p₂ ∈ P :=
by { induction n with n IH; simp[- iff_equiv_p], { simp[iff_equiv_p] },
     { refine equiv_and_of_equiv (hp _) (IH _), intros i, exact hp _ } }

lemma and_of_equiv {p₁ q₁ p₂ q₂: F} (h : p₁ ⊓ q₁ ∈ P) (hp : p₁ ⟷ p₂ ∈ P) (hq : q₁ ⟷ q₂ ∈ P) : p₂ ⊓ q₂ ∈ P :=
by { have : p₁ ⊓ q₁ ⟶ p₂ ⊓ q₂ ∈ P, from (iff_equiv_p.mp (equiv_and_of_equiv hp hq)).1, exact this ⨀ h }

lemma equiv_or_of_equiv {p₁ q₁ p₂ q₂: F} (hp : p₁ ⟷ p₂ ∈ P) (hq : q₁ ⟷ q₂ ∈ P) : p₁ ⊔ q₁ ⟷ p₂ ⊔ q₂ ∈ P :=
by { simp only [or_def P], refine (equiv_imply_of_equiv (equiv_neg_of_equiv hp) hq) }

lemma or_of_equiv {p₁ q₁ p₂ q₂: F} (h : p₁ ⊔ q₁ ∈ P) (hp : p₁ ⟷ p₂ ∈ P) (hq : q₁ ⟷ q₂ ∈ P) : p₂ ⊔ q₂ ∈ P :=
by { have : p₁ ⊔ q₁ ⟶ p₂ ⊔ q₂ ∈ P, from (iff_equiv_p.mp (equiv_or_of_equiv hp hq)).1, exact this ⨀ h }

lemma equiv_equiv_of_equiv {p₁ q₁ p₂ q₂: F} (hp : p₁ ⟷ p₂ ∈ P) (hq : q₁ ⟷ q₂ ∈ P) : (p₁ ⟷ q₁) ⟷ (p₂ ⟷ q₂) ∈ P :=
by { refine (equiv_and_of_equiv (equiv_imply_of_equiv hp hq) (equiv_imply_of_equiv hq hp)) }

lemma equiv_of_equiv {p₁ q₁ p₂ q₂: F} (h : p₁ ⟷ q₁ ∈ P) (hp : p₁ ⟷ p₂ ∈ P) (hq : q₁ ⟷ q₂ ∈ P) : p₂ ⟷ q₂ ∈ P :=
by { have : (p₁ ⟷ q₁) ⟶ (p₂ ⟷ q₂) ∈ P, from (iff_equiv_p.mp (equiv_equiv_of_equiv hp hq)).1, exact this ⨀ h }

@[refl, simp] lemma equiv_refl (p : F) : p ⟷ p ∈ P := by simp[iff_equiv_p]

@[symm] lemma equiv_symm {p q : F} : p ⟷ q ∈ P → q ⟷ p ∈ P := by { simp[iff_equiv_p], intros, simp* }

@[trans] lemma equiv_trans {p q r : F} : p ⟷ q ∈ P → q ⟷ r ∈ P → p ⟷ r ∈ P :=
by { simp[iff_equiv_p], intros hpq hqp hqr hrq, exact ⟨impl_trans hpq hqr, impl_trans hrq hqp⟩ }

@[simp] lemma bot_of_neg_top : (∼⊤ : F) ⟶ ⊥ ∈ P := by simp[@not_top_eq_bot F _ P _]

@[simp] lemma neg_top : (∼⊥ : F) ∈ P := @neg_of_equiv _ _ P _ (∼⊤) _ (by simp) (by simp[iff_equiv_p])

variables (P)

@[reducible] def equiv (p q : F) : Prop := p ⟷ q ∈ P

variables {P}

@[refl, simp] lemma equiv.refl (p : F) : equiv P p p := equiv_refl p

@[symm] lemma equiv.symm {p q : F} : equiv P p q → equiv P q p := equiv_symm

@[trans] lemma equiv.trans {p q r : F} : equiv P p q → equiv P q r → equiv P p r := equiv_trans

variables (P)

theorem equiv_equivalence : equivalence (equiv P) :=
⟨equiv.refl, @equiv.symm _ _ _ _, @equiv.trans _ _ _ _⟩

variables {P}

@[simp] lemma iff_dn_refl_right (p : F) : p ⟷ ∼∼p ∈ P := by simp[iff_equiv_p]

@[simp] lemma iff_dn_refl_left (p : F) : ∼∼p ⟷ p ∈ P := by simp[iff_equiv_p]

@[simp] lemma contraposition_inv (p q : F) : (p ⟶ q) ⟶ (∼q ⟶ ∼p) ∈ P :=
by { have : (∼∼p ⟶ ∼∼q) ⟶ ∼q ⟶ ∼p ∈ P, simp, 
     refine imply_of_equiv this (equiv_imply_of_equiv _ _) _; simp }

@[simp] lemma contraposition_iff (p q : F) : (p ⟶ q) ⟷ (∼q ⟶ ∼p) ∈ P :=
by simp[iff_equiv_p]

@[simp] lemma contraposition_iff₁ (p q : F) : (∼p ⟶ q) ⟷ (∼q ⟶ p) ∈ P :=
by { have : ∼p ⟶ q ⟷ ∼q ⟶ ∼∼p ∈ P, from contraposition_iff (∼p) q,
     refine equiv_of_equiv this (by simp) (equiv_imply_of_equiv (by simp) (by simp)) }

@[simp] lemma contraposition_iff₂ (p q : F) : (p ⟶ ∼q) ⟷ (q ⟶ ∼p) ∈ P :=
by { have : p ⟶ ∼q ⟷ ∼∼q ⟶ ∼p ∈ P, from contraposition_iff p (∼q),
     refine equiv_of_equiv this (by simp) (equiv_imply_of_equiv (by simp) (by simp)) }

@[simp] lemma contraposition_iff_inv (p q : F) : (∼p ⟶ ∼q) ⟷ (q ⟶ p) ∈ P :=
by simp[iff_equiv_p]

@[simp] lemma neg_hyp' (p : F) : (p ⟶ ∼p) ⟶ ∼p ∈ P :=
begin
  have : (p ⟶ ∼p) ⟶ p ⟶ ∼(p ⟶ ∼p) ∈ P,
  { have lmm₁ : (p ⟶ ∼p) ⟶ p ⟶ p ∈ P, { simp }, exact explosion_hyp₂ lmm₁ (by simp) },
  have : (p ⟶ ∼p) ⟶ ∼∼(p ⟶ ∼p) ⟶ ∼p ∈ P,
  { refine imply_of_equiv this _ _; simp[iff_equiv_p] },
  exact this ⨀₁ (show (p ⟶ ∼p) ⟶ ∼∼(p ⟶ ∼p) ∈ P, by simp)
end

@[simp] lemma neg_iff (p : F) : ∼p ⟷ (p ⟶ ⊥) ∈ P :=
begin
  simp[iff_equiv_p], split,
  { exact explosion_hyp₂ (show ∼p ⟶ p ⟶ p ∈ P, by simp) (show ∼p ⟶ p ⟶ ∼p ∈ P, by simp) },
  { have : (p ⟶ ⊥) ⟶ p ⟶ ∼p ∈ P,
      from explosion_hyp₂ (show (p ⟶ ⊥) ⟶ p ⟶ ⊤ ∈ P, by simp) (show (p ⟶ ⊥) ⟶ p ⟶ ∼⊤ ∈ P, by simp[bot_eq P]),
    refine (show (p ⟶ ⊥) ⟶ (p ⟶ ∼p) ⟶ ∼p ∈ P, by simp) ⨀₁ this }
end

@[simp] lemma imply_iff_of {p} (h : p ∈ P) (q) : (p ⟶ q) ⟷ q ∈ P :=
by simp[iff_equiv_p]; exact (show (p ⟶ q) ⟶ p ⟶ q ∈ P, by simp) ⨀₁ (by simp[h])

@[simp] lemma neg_impl_equiv_and (p q : F) : ∼(p ⟶ q) ⟷ p ⊓ ∼q ∈ P :=
by simp only [and_def P]; refine (equiv_neg_of_equiv (equiv_imply_of_equiv _ _)); simp

lemma neg_impl_iff_and_p {p q : F} : (∼(p ⟶ q) ∈ P) ↔ (p ⊓ ∼q ∈ P) :=
begin
  simp [and_def P], split; intros h,
  { refine neg_of_equiv h (equiv_imply_of_equiv _ _); simp },
  { refine neg_of_equiv h (equiv_imply_of_equiv _ _); simp }
end

@[simp] lemma impl_iff_or_p {p q : F} : (p ⟶ q) ⟷ (∼p ⊔ q) ∈ P :=
by {simp [or_def P, -iff_equiv_p], refine equiv_imply_of_equiv _ _; simp }


@[simp] lemma excluded_middle_p {p : F} : (p ⊔ ∼p) ∈ P :=
by simp[or_def P]

@[simp] lemma equiv_symm_and (p q : F) : p ⊓ q ⟷ q ⊓ p ∈ P :=
by { simp only [and_def P], refine equiv_neg_of_equiv _,
     refine equiv_of_equiv (show p ⟶ ∼q ⟷ ∼∼q ⟶ ∼p ∈ P, by simp) _ (equiv_imply_of_equiv _ _); simp }

@[simp] lemma equiv_symm_equiv (p q : F) : (p ⟷ q) ⟷ (q ⟷ p) ∈ P := equiv_symm_and _ _

@[simp] lemma equiv_or_symm (p q : F) : p ⊔ q ⟷ q ⊔ p ∈ P :=
by { simp only [or_def P],
     refine equiv_of_equiv (show ∼p ⟶ q ⟷ ∼q ⟶ ∼∼p ∈ P, by simp) _ (equiv_imply_of_equiv _ _); simp }

@[simp] lemma impl_iff_or'_p {p q : F} : (p ⟶ q) ⟷ (q ⊔ ∼p) ∈ P :=
equiv_trans (impl_iff_or_p) (by simp)

@[simp] lemma and_destruct (p q : F) : p ⟶ q ⟶ p ⊓ q ∈ P :=
by { simp only [and_def P],
     have : p ⟶ (p ⟶ ∼q) ⟶ ∼q ∈ P, from (show p ⟶ (p ⟶ ∼q) ⟶ p ⟶ ∼q ∈ P, by simp) ⨀₂ (show p ⟶ (p ⟶ ∼q) ⟶ p ∈ P, by simp),
     refine imply_of_equiv this (by simp) _,
     have : (p ⟶ ∼q) ⟶ ∼q ⟷ ∼∼q ⟶ ∼(p ⟶ ∼q) ∈ P, { simp }, refine equiv_of_equiv this _ (equiv_imply_of_equiv _ _); simp }

@[simp] lemma imply_or_left (p q : F) : p ⟶ p ⊔ q ∈ P :=
by simp[or_def P]; refine explosion_hyp₂ (show p ⟶ ∼p ⟶ p ∈ P, by simp) (show p ⟶ ∼p ⟶ ∼p ∈ P, by simp)

@[simp] lemma imply_or_right (p q : F) : q ⟶ p ⊔ q ∈ P :=
by simp[or_def P]

lemma disjunction_of {n} {p : finitary F n} (i) (h : p i ∈ P) : finitary.disjunction n p ∈ P :=
begin
  induction n with n IH; simp*,
  { exfalso, exact i.val.not_lt_zero i.property },
  { revert h, refine fin.last_cases _ _ i,
    { intros h, exact imply_or_right _ _ ⨀ h },
    { intros i h, exact imply_or_left _ _ ⨀ (IH i h) } }
end

lemma ldisj_of {l : list F} {p : F} (h : p ∈ l) (b : p ∈ P) : l.disjunction ∈ P :=
begin
  induction l with a l IH generalizing p; simp*,
  { exfalso, simp at h, contradiction },
  { simp at h, rcases h with (rfl | h),
    { exact imply_or_right _ _ ⨀ b },
    { exact imply_or_left _ _ ⨀ IH h b } }
end

lemma fdisj_of {s : finset F} {p : F} (h : p ∈ s) (b : p ∈ P) : s.disjunction ∈ P :=
by simp[finset.disjunction]; refine ldisj_of (by simpa using h) b

lemma fconj_of {s : finset F} {p : F} : s.conjunction ∈ P ↔ ∀ p ∈ s, p ∈ P:=
by simp[finset.conjunction]

@[simp] lemma imply_ldisj {l : list F} {p : F} (h : p ∈ l) : p ⟶ l.disjunction ∈ P :=
begin
  induction l with q l IH,
  { simp at h, contradiction },
  { simp at h ⊢, rcases h with (rfl| h),
    { simp },
    { refine impl_trans (IH h) (by simp) } }
end

@[simp] lemma lconj_imply {l : list F} {p : F} (h : p ∈ l) : l.conjunction ⟶ p ∈ P :=
begin
  induction l with q l IH,
  { simp at h, contradiction },
  { simp at h ⊢, rcases h with (rfl| h),
    { simp },
    { refine impl_trans (by simp) (IH h) } }
end

lemma imply_fdisj {s : finset F} {p : F} (h : p ∈ s) : p ⟶ s.disjunction ∈ P :=
by simp[finset.disjunction]; refine imply_ldisj (by simpa using h)

lemma fconj_imply {s : finset F} {p : F} (h : p ∈ s) : s.conjunction ⟶ p ∈ P :=
by simp[finset.conjunction]; refine lconj_imply (by simpa using h)

@[simp] lemma imply_and (p q r : F) : (p ⟶ q) ⟶ (p ⟶ r) ⟶ p ⟶ q ⊓ r ∈ P :=
begin
  have : (p ⟶ q) ⟶ (p ⟶ r) ⟶ p ⟶ r ⟶ q ⊓ r ∈ P,
    from (show (p ⟶ q) ⟶ (p ⟶ r) ⟶ p ⟶ q ⟶ r ⟶ q ⊓ r ∈ P, by simp) ⨀₃ (show (p ⟶ q) ⟶ (p ⟶ r) ⟶ p ⟶ q ∈ P, by simp),
  exact this ⨀₃ (show (p ⟶ q) ⟶ (p ⟶ r) ⟶ p ⟶ r ∈ P, by simp),
end

@[simp] lemma neg_and_equiv_or_neg (p q : F) : ∼(p ⊓ q) ⟷ ∼p ⊔ ∼q ∈ P :=
begin
  simp only [and_def P, or_def P],
  refine equiv_of_equiv (show p ⟶ ∼q ⟷ p ⟶ ∼q ∈ P, by simp) _ (equiv_imply_of_equiv _ _); simp
end

@[simp] lemma neg_conj_equiv_disj_neg {n} (p : finitary F n) : ∼(finitary.conjunction n p) ⟷ (⋁ i, ∼p i) ∈ P :=
begin
  induction n with n IH; simp[-iff_equiv_p],
  { simp[iff_equiv_p] },
  { have lmm₁ : ∼(p (fin.last n) ⊓ finitary.conjunction n (p ∘ fin.cast_succ)) ⟷
      ∼p (fin.last n) ⊔ ∼finitary.conjunction n (p ∘ fin.cast_succ) ∈ P, from neg_and_equiv_or_neg _ _,
    have lmm₂ : ∼p (fin.last n) ⊔ ∼finitary.conjunction n (p ∘ fin.cast_succ) ⟷ 
      ∼finitary.conjunction n (p ∘ fin.cast_succ) ⊔ ∼p (fin.last n) ∈ P, from equiv_or_symm _ _,
    refine equiv_of_equiv (equiv_trans lmm₁ lmm₂) (equiv_refl _) (equiv_or_of_equiv (IH (p ∘ fin.cast_succ)) (equiv_refl _)) }
end

@[simp] lemma neg_lconj_equiv_ldisj_neg (l : list F) : ∼l.conjunction ⟷ (l.map has_negation.neg).disjunction ∈ P :=
begin
  induction l with p l IH; simp[-iff_equiv_p],
  { simp[iff_equiv_p] },
  { have lmm₁ : ∼(p ⊓ l.conjunction) ⟷ ∼p ⊔ ∼l.conjunction ∈ P, from neg_and_equiv_or_neg _ _,
    have lmm₂ : ∼p ⊔ ∼l.conjunction ⟷ ∼l.conjunction ⊔ ∼p ∈ P, from equiv_or_symm _ _,
    refine equiv_of_equiv (equiv_trans lmm₁ lmm₂) (equiv_refl _)
    (equiv_or_of_equiv IH (equiv_refl _)) }
end

@[simp] lemma neg_or_equiv_and_neg (p q : F) : ∼(p ⊔ q) ⟷ ∼p ⊓ ∼q ∈ P :=
begin
  simp only [and_def P, or_def P],
  refine equiv_of_equiv (show ∼(∼p ⟶ q) ⟷ ∼(∼p ⟶ q) ∈ P, by simp) _ (equiv_neg_of_equiv (equiv_imply_of_equiv _ _)); simp
end

@[simp] lemma neg_disj_equiv_conj_neg {n} (p : finitary F n) : ∼(finitary.disjunction n p) ⟷ (⋀ i, ∼p i) ∈ P :=
begin
  induction n with n IH; simp[-iff_equiv_p],
  { simp[iff_equiv_p] },
  { have lmm₁ : ∼(finitary.disjunction n (p ∘ fin.cast_succ) ⊔ p (fin.last n)) ⟷
      ∼finitary.disjunction n (p ∘ fin.cast_succ) ⊓ ∼p (fin.last n) ∈ P, from neg_or_equiv_and_neg _ _,
    have lmm₂ : ∼finitary.disjunction n (p ∘ fin.cast_succ) ⊓ ∼p (fin.last n) ⟷
      ∼p (fin.last n) ⊓ ∼finitary.disjunction n (p ∘ fin.cast_succ) ∈ P, from equiv_symm_and _ _,
    refine equiv_of_equiv (equiv_trans lmm₁ lmm₂) (equiv_refl _) (equiv_and_of_equiv (equiv_refl _) (IH (p ∘ fin.cast_succ)))  }
end

@[simp] lemma or_imply (p q r : F) : (p ⟶ r) ⟶ (q ⟶ r) ⟶ p ⊔ q ⟶ r ∈ P :=
begin
  have : (∼r ⟶ ∼p) ⟶ (∼r ⟶ ∼q) ⟶ ∼r ⟶ ∼p ⊓ ∼q ∈ P, { simp },
  refine imply_of_equiv this (by simp) (equiv_imply_of_equiv (by simp) _),
  have : ∼r ⟶ ∼(p ⊔ q) ⟷ p ⊔ q ⟶ r ∈ P, { simp },
  refine equiv_of_equiv (show ∼r ⟶ ∼(p ⊔ q) ⟷ p ⊔ q ⟶ r ∈ P, by simp) (equiv_imply_of_equiv _ _) _; simp
end

@[simp] lemma le_sup_inf (p q r : F) : (p ⊔ q) ⊓ (p ⊔ r) ⟶ p ⊔ q ⊓ r ∈ P :=
begin
  simp[or_def P],
  exact (show (∼p ⟶ q) ⊓ (∼p ⟶ r) ⟶ (∼p ⟶ q) ⟶ (∼p ⟶ r) ⟶ ∼p ⟶ q ⊓ r ∈ P, by simp) ⨀₁
        (show (∼p ⟶ q) ⊓ (∼p ⟶ r) ⟶ (∼p ⟶ q) ∈ P, by simp) ⨀₁
        (show (∼p ⟶ q) ⊓ (∼p ⟶ r) ⟶ (∼p ⟶ r) ∈ P, by simp)
end

lemma case_of_p {p q r : F} (hpq : p ⊔ q ∈ P) (hpr : p ⟶ r ∈ P) (hqr : q ⟶ r ∈ P) : r ∈ P :=
(show (p ⟶ r) ⟶ (q ⟶ r) ⟶ p ⊔ q ⟶ r ∈ P, by simp) ⨀ hpr ⨀ hqr ⨀ hpq

@[simp] lemma and_imply_equiv_imply_imply (p q r : F) : (p ⟶ q ⟶ r) ⟷ (p ⊓ q ⟶ r) ∈ P :=
begin
  simp[iff_equiv_p], split,
  { exact (show (p ⟶ q ⟶ r) ⟶ p ⊓ q ⟶ p ⟶ q ⟶ r ∈ P, by simp) ⨀₂ (show (p ⟶ q ⟶ r) ⟶ p ⊓ q ⟶ p ∈ P, by simp) ⨀₂ (show (p ⟶ q ⟶ r) ⟶ p ⊓ q ⟶ q ∈ P, by simp) },
  { exact (show (p ⊓ q ⟶ r) ⟶ p ⟶ q ⟶ (p ⊓ q ⟶ r) ∈ P, by simp) ⨀₃ (show (p ⊓ q ⟶ r) ⟶ p ⟶ q ⟶ (p ⊓ q) ∈ P, by simp) }
end

lemma and_imply_of {p q r} : p ⊓ q ⟶ r ∈ P ↔ p ⟶ q ⟶ r ∈ P :=
(iff_of_equiv $ and_imply_equiv_imply_imply p q r).symm

@[simp] lemma imply_and_equiv_or_imply (p q r : F) : (p ⟶ r) ⊓ (q ⟶ r) ⟷ p ⊔ q ⟶ r ∈ P :=
begin
  simp[iff_equiv_p], split,
  { refine of_equiv (or_imply p q r) (and_imply_equiv_imply_imply _ _ _) },
  { have lmm₁ : (p ⊔ q ⟶ r) ⟶ p ⟶ r ∈ P, from (show (p ⊔ q ⟶ r) ⟶ p ⟶ p ⊔ q ⟶ r ∈ P, by simp) ⨀₂ (show (p ⊔ q ⟶ r) ⟶ p ⟶ p ⊔ q ∈ P, by simp),
    have lmm₂ : (p ⊔ q ⟶ r) ⟶ q ⟶ r ∈ P, from (show (p ⊔ q ⟶ r) ⟶ q ⟶ p ⊔ q ⟶ r ∈ P, by simp) ⨀₂ (show (p ⊔ q ⟶ r) ⟶ q ⟶ p ⊔ q ∈ P, by simp),
    refine imply_and _ _ _ ⨀ lmm₁ ⨀ lmm₂ }
end

@[simp] lemma conj_imply_iff_disj_imply {n} (p : finitary F n) (q : F) : (⋀ i, (p i ⟶ q)) ⟷ ((⋁ i, p i) ⟶ q) ∈ P :=
begin
  induction n with n IH, { simp[iff_equiv_p] }, 
  { simp[-iff_equiv_p, (∘)],
    have : (p (fin.last n) ⟶ q) ⊓ ((⋁ i, p i.cast_succ) ⟶ q) ⟷ (p (fin.last n) ⊔ ⋁ i, p i.cast_succ) ⟶ q ∈ P,
    from imply_and_equiv_or_imply (p (fin.last n)) (⋁ i, p i.cast_succ) q,
    refine equiv_of_equiv this (equiv_and_of_equiv (equiv_refl _) (equiv_symm (IH _)))
      (equiv_imply_of_equiv (equiv_or_symm _ _) (by refl)), }
end

@[simp] lemma lconj_imply_iff_ldisj_imply (l : list F) (q : F) :
  (l.map (λ p, (p ⟶ q))).conjunction ⟷ (l.disjunction ⟶ q) ∈ P :=
begin
  induction l with p l IH, { simp[iff_equiv_p] }, 
  { simp[-iff_equiv_p, (∘)],
    refine equiv_of_equiv (imply_and_equiv_or_imply p l.disjunction q)
      (equiv_and_of_equiv (equiv_refl _) (equiv_symm (IH)))
      (equiv_imply_of_equiv (equiv_or_symm _ _) (by refl)) }
end

@[simp] lemma imply_lconj_of {l : list F} {q : F} (h : ∀ p ∈ l, q ⟶ p ∈ P) : q ⟶ l.conjunction ∈ P :=
by { induction l with p l IH; simp,
     { simp at h, refine imply_and _ _ _ ⨀ _ ⨀ _,
       { exact h.1 },
       { exact IH h.2 } } }

@[simp] lemma ldisj_imply_of {l : list F} {q : F} (h : ∀ p ∈ l, p ⟶ q ∈ P) : l.disjunction ⟶ q ∈ P :=
by { have : (l.map (λ p, (p ⟶ q))).conjunction ∈ P, by simpa using h,
     exact (iff_equiv_p.mp $ lconj_imply_iff_ldisj_imply l q).1 ⨀ this }

@[simp] lemma imply_fconj_of {s : finset F} {q : F} (h : ∀ p ∈ s, q ⟶ p ∈ P) : q ⟶ s.conjunction ∈ P :=
by simp[finset.conjunction]; exact imply_lconj_of (by simpa using h)

@[simp] lemma fdisj_imply_of {s : finset F} {q : F} (h : ∀ p ∈ s, p ⟶ q ∈ P) : s.disjunction ⟶ q ∈ P :=
by simp[finset.disjunction]; exact ldisj_imply_of (by simpa using h)

@[simp] lemma equiv_or_assoc (p q r : F) : (p ⊔ q) ⊔ r ⟷ p ⊔ (q ⊔ r) ∈ P :=
begin
  simp[iff_equiv_p], split,
  { have l₁ : p ⟶ p ⊔ (q ⊔ r) ∈ P, from imply_or_left p (q ⊔ r),
    have l₂ : q ⟶ p ⊔ (q ⊔ r) ∈ P, from impl_trans (imply_or_left q r) (imply_or_right p (q ⊔ r)),
    have l₃ : r ⟶ p ⊔ (q ⊔ r) ∈ P, from impl_trans (imply_or_right q r) (imply_or_right p (q ⊔ r)),
    exact or_imply _ _ _ ⨀ (or_imply _ _ _ ⨀ l₁ ⨀ l₂) ⨀ l₃ },
  { have l₁ : p ⟶ (p ⊔ q) ⊔ r ∈ P, from impl_trans (imply_or_left p q) (imply_or_left (p ⊔ q) r),
    have l₂ : q ⟶ (p ⊔ q) ⊔ r ∈ P, from impl_trans (imply_or_right p q) (imply_or_left (p ⊔ q) r),
    have l₃ : r ⟶ (p ⊔ q) ⊔ r ∈ P, from imply_or_right (p ⊔ q) r,
    exact or_imply _ _ _ ⨀ l₁ ⨀ (or_imply _ _ _ ⨀ l₂ ⨀ l₃) }
end

lemma equiv_append (l₁ l₂ : list F) : (l₁ ++ l₂).disjunction ⟷ l₁.disjunction ⊔ l₂.disjunction ∈ P :=
begin
  induction l₁; simp[-iff_equiv_p],
  case nil { simp[iff_equiv_p], refine or_imply ⊥ l₂.disjunction l₂.disjunction ⨀ (hyp_bot l₂.disjunction) ⨀ (refl l₂.disjunction) },
  case cons : p l IH
  { have l₁ : (l ++ l₂).disjunction ⊔ p ⟷ l.disjunction ⊔ (l₂.disjunction ⊔ p) ∈ P,
      from equiv_trans (equiv_or_of_equiv IH (equiv_refl p)) (equiv_or_assoc l.disjunction l₂.disjunction p),
    have l₂ : l.disjunction ⊔ (l₂.disjunction ⊔ p) ⟷ l.disjunction ⊔ p ⊔ l₂.disjunction ∈ P,
      from equiv_trans (equiv_or_of_equiv (equiv_refl l.disjunction) (equiv_or_symm l₂.disjunction p))
      (equiv_symm (equiv_or_assoc _ _ _)),
    exact equiv_trans l₁ l₂ }
end

lemma fconj_insert_equiv_inf {s : finset F} {p : F} : (insert p s).conjunction ⟷ p ⊓ s.conjunction ∈ P :=
begin
  simp[iff_equiv_p], split,
  { refine imply_and _ _ _ ⨀ _ ⨀ _,
    refine fconj_imply (by simp),
    refine imply_fconj_of (by { intros q hq, refine fconj_imply (by simp[hq]) }) },
  { refine imply_fconj_of _, intros q hq, simp at hq, rcases hq with (rfl | hq),
    { simp }, { refine impl_trans (and_right _ _) (fconj_imply hq) } }
end

lemma fdisj_insert_equiv_sup {s : finset F} {p : F} : (insert p s).disjunction ⟷ s.disjunction ⊔ p ∈ P :=
begin
  simp[iff_equiv_p], split,
  { refine fdisj_imply_of _, intros q hq, simp at hq, rcases hq with (rfl | hq),
    { simp }, { refine impl_trans (imply_fdisj hq) (imply_or_left _ _) } },
  { refine or_imply _ _ _ ⨀ _ ⨀ _,
    refine fdisj_imply_of (by { intros q hq, refine imply_fdisj (by simp[hq]) }),
    refine imply_fdisj (by simp) }
end

variables (P)

def lindenbaum := quotient (⟨equiv P, equiv_equivalence P⟩ : setoid F)

variables {P}

def to_quo (p : F) : lindenbaum P := quotient.mk' p

local notation `⟦` p `⟧ᴾ` := to_quo p

namespace lindenbaum

@[elab_as_eliminator]
protected lemma ind_on {C : lindenbaum P → Prop} (d : lindenbaum P)
  (h : ∀ p : F, C (to_quo p)) : C d := quotient.induction_on' d h

@[elab_as_eliminator, reducible]
protected def lift_on {φ : Sort*} (p : lindenbaum P) (f : F → φ)
  (h : ∀ p q : F, p ⟷ q ∈ P → f p = f q) : φ := quotient.lift_on' p f h

@[simp]
protected lemma lift_on_eq {φ : Sort*} (p : F) (f : F → φ)
  (h : ∀ p q, p ⟷ q ∈ P → f p = f q) : classical_logic.lindenbaum.lift_on ⟦p⟧ᴾ f h = f p := rfl

@[elab_as_eliminator, reducible, simp]
protected def lift_on₂ {φ : Sort*} (p₁ p₂ : lindenbaum P) (f : F → F → φ)
  (h : ∀ p₁ p₂ q₁ q₂, p₁ ⟷ q₁ ∈ P → p₂ ⟷ q₂ ∈ P → f p₁ p₂ = f q₁ q₂) : φ :=
quotient.lift_on₂' p₁ p₂ f h

@[simp]
protected lemma lift_on₂_eq {φ : Sort*} (p₁ p₂ : F) (f : F → F → φ)
  (h : ∀ p₁ p₂ q₁ q₂, p₁ ⟷ q₁ ∈ P → p₂ ⟷ q₂ ∈ P → f p₁ p₂ = f q₁ q₂)  :
classical_logic.lindenbaum.lift_on₂ ⟦p₁⟧ᴾ ⟦p₂⟧ᴾ f h = f p₁ p₂ := rfl

@[elab_as_eliminator, reducible]
protected def lift_on_finitary {φ : Sort*} {n : ℕ} (v : finitary (lindenbaum P) n) (f : finitary F n → φ)
  (h : ∀ v₁ v₂ : finitary F n, (∀ n, v₁ n ⟷ v₂ n ∈ P) → f v₁ = f v₂) : φ :=
quotient.lift_on_finitary v f h 

@[simp]
protected lemma lift_on_finitary_eq {φ : Sort*} {n : ℕ} (v : finitary F n) (f : finitary F n → φ)
  (h : ∀ v₁ v₂ : finitary F n, (∀ n, v₁ n ⟷ v₂ n ∈ P) → f v₁ = f v₂) :
classical_logic.lindenbaum.lift_on_finitary (λ x, ⟦v x⟧ᴾ) f h = f v :=
quotient.lift_on_finitary_eq v f h

lemma of_eq_of {p q : F} : (⟦p⟧ᴾ : lindenbaum P) = ⟦q⟧ᴾ ↔ p ⟷ q ∈ P :=
by simp[to_quo, equiv, quotient.eq']

instance : distrib_lattice (lindenbaum P) :=
{ le := λ p₁ p₂, classical_logic.lindenbaum.lift_on₂ p₁ p₂ (λ p₁ p₂, p₁ ⟶ p₂ ∈ P)
    (λ p₁ p₂ q₁ q₂ h₁ h₂,
      by { simp, exact ⟨λ h, imply_of_equiv h h₁ h₂, λ h, imply_of_equiv h (equiv_symm h₁) (equiv_symm h₂)⟩ }),
  le_refl := λ p, by induction p using classical_logic.lindenbaum.ind_on; simp,
  le_trans := λ p₁ p₂ p₃ h₁₂ h₂₃,
  by { induction p₁ using classical_logic.lindenbaum.ind_on,
       induction p₂ using classical_logic.lindenbaum.ind_on,
       induction p₃ using classical_logic.lindenbaum.ind_on,
       simp at h₁₂ h₂₃ ⊢, exact impl_trans h₁₂ h₂₃ },
  le_antisymm := λ p₁ p₂,
  by { induction p₁ using classical_logic.lindenbaum.ind_on,
       induction p₂ using classical_logic.lindenbaum.ind_on,
       simp[has_le.le], intros h₁ h₂, simp[*, of_eq_of, iff_equiv_p] },
  inf := λ p₁ p₂, classical_logic.lindenbaum.lift_on₂ p₁ p₂ (λ p₁ p₂, (⟦p₁ ⊓ p₂⟧ᴾ : lindenbaum P))
    (λ p₁ p₂ q₁ q₂ h₁ h₂, by { simp[of_eq_of], exact equiv_and_of_equiv h₁ h₂ }),
  sup := λ p₁ p₂, classical_logic.lindenbaum.lift_on₂ p₁ p₂ (λ p₁ p₂, (⟦p₁ ⊔ p₂⟧ᴾ : lindenbaum P))
    (λ p₁ p₂ q₁ q₂ h₁ h₂, by { simp[of_eq_of], exact equiv_or_of_equiv h₁ h₂ }),
  le_sup_left := λ p q,
  by { induction p using classical_logic.lindenbaum.ind_on,
       induction q using classical_logic.lindenbaum.ind_on,
       simp[has_le.le, preorder.le] },
  le_sup_right := λ p q,
  by { induction p using classical_logic.lindenbaum.ind_on,
       induction q using classical_logic.lindenbaum.ind_on,
       simp[has_le.le, preorder.le] },
  sup_le := λ p q r,
  by { induction p using classical_logic.lindenbaum.ind_on,
       induction q using classical_logic.lindenbaum.ind_on,
       induction r using classical_logic.lindenbaum.ind_on,
       simp[has_le.le, preorder.le],
       intros hpr hqr, exact (show (p ⟶ r) ⟶ (q ⟶ r) ⟶ p ⊔ q ⟶ r ∈ P, by simp) ⨀ hpr ⨀ hqr },
  inf_le_left := λ p q,
  by { induction p using classical_logic.lindenbaum.ind_on,
       induction q using classical_logic.lindenbaum.ind_on,
       simp[has_le.le, preorder.le] },
  inf_le_right := λ p q,
  by { induction p using classical_logic.lindenbaum.ind_on,
       induction q using classical_logic.lindenbaum.ind_on,
       simp[has_le.le, preorder.le] },
  le_inf := λ p q r,
  by { induction p using classical_logic.lindenbaum.ind_on,
       induction q using classical_logic.lindenbaum.ind_on,
       induction r using classical_logic.lindenbaum.ind_on,
       simp[has_le.le, preorder.le],
       intros hpq hpr, exact (show (p ⟶ q) ⟶ (p ⟶ r) ⟶ p ⟶ q ⊓ r ∈ P, by simp) ⨀ hpq ⨀ hpr },
  le_sup_inf := λ p q r,
  by { induction p using classical_logic.lindenbaum.ind_on,
       induction q using classical_logic.lindenbaum.ind_on,
       induction r using classical_logic.lindenbaum.ind_on,
       simp[has_le.le, preorder.le, partial_order.le, semilattice_inf.le,
         has_sup.sup, semilattice_sup.sup, has_inf.inf, semilattice_inf.inf] } }

instance : has_compl (lindenbaum P) := ⟨λ p, classical_logic.lindenbaum.lift_on p (λ p, (⟦∼p⟧ᴾ : lindenbaum P))
    (λ p q h, by { simp[of_eq_of], exact equiv_neg_of_equiv h })⟩

lemma le_def (p q : F) : (⟦p⟧ᴾ : lindenbaum P) ≤ ⟦q⟧ᴾ ↔ p ⟶ q ∈ P := by refl

lemma neg_def (p : F) : (⟦p⟧ᴾ : lindenbaum P)ᶜ = ⟦∼p⟧ᴾ := rfl

lemma inf_def (p q : F) : (⟦p⟧ᴾ : lindenbaum P) ⊓ ⟦q⟧ᴾ = ⟦p ⊓ q⟧ᴾ := rfl

lemma sup_def (p q : F) : (⟦p⟧ᴾ : lindenbaum P) ⊔ ⟦q⟧ᴾ = ⟦p ⊔ q⟧ᴾ := rfl

instance : boolean_algebra (lindenbaum P) :=
{ top := ⟦⊤⟧ᴾ,
  bot := ⟦⊥⟧ᴾ,
  le_top := λ p, by induction p using classical_logic.lindenbaum.ind_on; simp[le_def],
  bot_le := λ p, by induction p using classical_logic.lindenbaum.ind_on; simp[le_def],
  compl := has_compl.compl,
  inf_compl_le_bot := λ p,
  by { induction p using classical_logic.lindenbaum.ind_on, simp[bounded_order.bot],
       refine explosion_hyp (show p ⊓ ∼p ⟶ p ∈ P, by simp) (by simp) },
  top_le_sup_compl := λ p, 
  by { induction p using classical_logic.lindenbaum.ind_on, 
       simp[bounded_order.top, or_def P, le_def, sup_def, neg_def] },
  ..lindenbaum.distrib_lattice }

lemma top_def : (⊤ : lindenbaum P) = ⟦⊤⟧ᴾ := rfl

lemma bot_def : (⊥ : lindenbaum P) = ⟦⊥⟧ᴾ := rfl

lemma imply_eq (p q : F) : (⟦p ⟶ q⟧ᴾ : lindenbaum P) = ⟦p⟧ᴾ ⇨ ⟦q⟧ᴾ:=
by simp[of_eq_of, himp_eq, neg_def, sup_def]

lemma fconj_eq (s : finset F) : (⟦s.conjunction⟧ᴾ : lindenbaum P) = s.inf to_quo :=
begin
  induction s using finset.induction_on with p s hs IH,
  { simp, refl },
  { simp, rw[←IH, inf_def, of_eq_of], exact fconj_insert_equiv_inf }
end

lemma fdisj_eq (s : finset F) : (⟦s.disjunction⟧ᴾ : lindenbaum P) = s.sup to_quo :=
begin
  induction s using finset.induction_on with p s hs IH,
  { simp, refl },
  { simp, rw[sup_comm, ←IH, sup_def, of_eq_of], exact fdisj_insert_equiv_sup }
end

end lindenbaum

open lindenbaum

lemma equiv_of_lindenbaum {p q : F} : p ⟷ q ∈ P ↔ (⟦p⟧ᴾ : lindenbaum P) = ⟦q⟧ᴾ :=
lindenbaum.of_eq_of.symm

lemma fdisj_insert_equiv_fconj_imply (p : F) (s : finset F) :
  (insert p s).disjunction ⟷ ((s.image has_negation.neg).conjunction ⟶ p) ∈ P :=
by simp [equiv_of_lindenbaum, fdisj_eq, fconj_eq, imply_eq, himp_eq, ←neg_def, finset.sup_finset_image, (∘)]

lemma fconj_imply_equiv_fdisj_neg (p : F) (s : finset F) :
  (s.conjunction ⟶ p) ⟷ (insert p (s.image has_negation.neg)).disjunction ∈ P :=
by simp [equiv_of_lindenbaum, fdisj_eq, fconj_eq, imply_eq, himp_eq, ←neg_def, finset.sup_finset_image, (∘)]

@[simp] lemma neg_bot_equiv_top : (∼⊥ : F) ⟷ ⊤ ∈ P :=
by simp[equiv_of_lindenbaum, ←neg_def, ←top_def, ←bot_def]

end classical_logic

namespace axiomatic_classical_logic'
open classical_logic
variables {F : Type*} [has_logic_symbol F]
  (T : set F) [axiomatic_classical_logic' F]

instance : classical_logic ((⊢) T) := axiomatic_classical_logic'.classical

variables {T}

lemma modus_ponens {p q : F} : T ⊢ p ⟶ q → T ⊢ p → T ⊢ q := modus_ponens

lemma modus_ponens_hyp {p q r : F} : T ⊢ p ⟶ q ⟶ r → T ⊢ p ⟶ q → T ⊢ p ⟶ r :=
modus_ponens_hyp

lemma modus_ponens_hyp₂ {p q r s : F} : T ⊢ p ⟶ q ⟶ r ⟶ s → T ⊢ p ⟶ q ⟶ r → T ⊢ p ⟶ q ⟶ s :=
modus_ponens_hyp₂

lemma modus_ponens_hyp₃ {p q r s t : F} :
  T ⊢ p ⟶ q ⟶ r ⟶ s ⟶ t → T ⊢ p ⟶ q ⟶ r ⟶ s → T ⊢ p ⟶ q ⟶ r ⟶ t :=
modus_ponens_hyp₃

localized "infixl ` ⨀ `:90 := axiomatic_classical_logic'.modus_ponens" in aclogic
localized "infixl ` ⨀₁ `:90 := axiomatic_classical_logic'.modus_ponens_hyp" in aclogic
localized "infixl ` ⨀₂ `:90 := axiomatic_classical_logic'.modus_ponens_hyp₂" in aclogic
localized "infixl ` ⨀₃ `:90 := axiomatic_classical_logic'.modus_ponens_hyp₃" in aclogic

open_locale aclogic

@[simp] lemma mem_iff_prov (p : F) : (@has_mem.mem F (set F) _) p ((⊢) T : set F) ↔ T ⊢ p := by refl

@[simp] lemma imply₁ (p q : F) : T ⊢ p ⟶ q ⟶ p := imply₁

@[simp] lemma imply₂ (p q r : F) : T ⊢ (p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r := imply₂

lemma imply_trans {p q r : F} : (T ⊢ p ⟶ q) → (T ⊢ q ⟶ r) → (T ⊢ p ⟶ r) :=
impl_trans

@[simp] lemma contraposition (p q : F) : T ⊢ (∼p ⟶ ∼q) ⟶ q ⟶ p := contraposition

@[simp] lemma provable_top : T ⊢ (⊤ : F) := provable_top

@[simp] lemma refl (p : F) : T ⊢ p ⟶ p := classical_logic.refl p

@[simp] lemma hyp_right {p : F} (h : T ⊢ p) (q) : T ⊢ q ⟶ p := hyp_right h q

@[simp] lemma T_hyp_eliminate {p : F} : T ⊢ ⊤ ⟶ p ↔ T ⊢ p := T_hyp_eliminate

@[simp] lemma dne (p : F) : T ⊢ ∼∼p ⟶ p := dne p

@[simp] lemma imply₁' {p q r : F} : T ⊢ p ⟶ q ⟶ r ⟶ p := imply₁'

@[simp] lemma dni (p : F) : T ⊢ p ⟶ ∼∼p := dni p

@[simp] lemma dn_iff {p : F} : T ⊢ ∼∼p ↔ T ⊢ p := dn_iff

@[simp] lemma dn1_iff {p q : F} : T ⊢ ∼∼p ⟶ q ↔ T ⊢ p ⟶ q := dn1_iff

@[simp] lemma dn2_iff {p q : F} : T ⊢ p ⟶ ∼∼q ↔ T ⊢ p ⟶ q := dn2_iff

@[simp] lemma hyp_bot (p : F) : T ⊢ ⊥ ⟶ p := hyp_bot p

@[simp] lemma and_left (p q : F) : T ⊢ p ⊓ q ⟶ p := and_left p q

@[simp] lemma and_right (p q : F) : T ⊢ p ⊓ q ⟶ q := and_right p q

@[simp] lemma iff_and {p q : F} : T ⊢ p ⊓ q ↔ (T ⊢ p ∧ T ⊢ q) := iff_and_p

@[simp] lemma conjunction_iff {n} {p : finitary F n} : (T ⊢ finitary.conjunction n p) ↔ (∀ i, T ⊢ p i) :=
conjunction_iff

lemma iff_equiv {p q : F} : T ⊢ p ⟷ q ↔ (T ⊢ p ⟶ q ∧ T ⊢ q ⟶ p) := iff_equiv_p

lemma equiv_mp {p q : F} (h : T ⊢ p ⟷ q) : T ⊢ p ⟶ q := (iff_equiv.mp h).1

lemma equiv_mpr {p q : F} (h : T ⊢ p ⟷ q) : T ⊢ q ⟶ p := (iff_equiv.mp h).2

lemma iff_of_equiv {p q : F} (h : T ⊢ p ⟷ q) : T ⊢ p ↔ T ⊢ q := iff_of_equiv h

@[refl, simp] lemma equiv_refl (p : F) : T ⊢ p ⟷ p := equiv_refl p

@[symm] lemma equiv_symm {p q : F} : T ⊢ p ⟷ q → T ⊢ q ⟷ p := equiv_symm

@[trans] lemma equiv_trans {p q r : F} : T ⊢ p ⟷ q → T ⊢ q ⟷ r → T ⊢ p ⟷ r := equiv_trans

@[simp] lemma iff_dn_refl_right (p : F) : T ⊢ p ⟷ ∼∼p := iff_dn_refl_right p

@[simp] lemma iff_dn_refl_left (p : F) : T ⊢ ∼∼p ⟷ p := iff_dn_refl_left p

@[simp] lemma contraposition_inv (p q : F) : T ⊢ (p ⟶ q) ⟶ (∼q ⟶ ∼p) := contraposition_inv p q

@[simp] lemma contraposition_iff (p q : F) : T ⊢ (p ⟶ q) ⟷ (∼q ⟶ ∼p) := contraposition_iff p q

@[simp] lemma contraposition_iff₁ (p q : F) : T ⊢ (∼p ⟶ q) ⟷ (∼q ⟶ p) := contraposition_iff₁ _ _

@[simp] lemma contraposition_iff₂ (p q : F) : T ⊢ (p ⟶ ∼q) ⟷ (q ⟶ ∼p) := contraposition_iff₂ _ _

@[simp] lemma contraposition_iff_inv (p q : F) : T ⊢ (∼p ⟶ ∼q) ⟷ (q ⟶ p) := contraposition_iff_inv p q

@[simp] lemma neg_hyp' (p : F) : T ⊢ (p ⟶ ∼p) ⟶ ∼p := neg_hyp' p

@[simp] lemma neg_iff (p : F) : T ⊢ ∼p ⟷ (p ⟶ ⊥) := neg_iff p

@[simp] lemma imply_iff_of {p} (h : T ⊢ p) (q) : T ⊢ (p ⟶ q) ⟷ q := imply_iff_of h q

@[simp] lemma neg_impl_equiv_and (p q : F) : T ⊢ ∼(p ⟶ q) ⟷ p ⊓ ∼q := neg_impl_equiv_and p q




lemma neg_impl_iff_and {p q : F} : T ⊢ ∼(p ⟶ q) ↔ T ⊢ p ⊓ ∼q := neg_impl_iff_and_p

lemma of_equiv {p₁ p₂ : F} (h : T ⊢ p₁) (hp : T ⊢ p₁ ⟷ p₂) : T ⊢ p₂ := of_equiv h hp

@[simp] lemma impl_iff_or {p q : F} : T ⊢ (p ⟶ q) ⟷ (∼p ⊔ q) := impl_iff_or_p

@[simp] lemma impl_iff_or' {p q : F} : T ⊢ (p ⟶ q) ⟷ (q ⊔ ∼p) := impl_iff_or'_p

@[simp] lemma excluded_middle {p : F} : T ⊢ p ⊔ ∼p := excluded_middle_p

@[simp] lemma equiv_symm_and (p q : F) : T ⊢ p ⊓ q ⟷ q ⊓ p := equiv_symm_and p q

@[simp] lemma equiv_symm_equiv (p q : F) : T ⊢ (p ⟷ q) ⟷ (q ⟷ p) := equiv_symm_equiv p q

@[simp] lemma equiv_or_symm (p q : F) : T ⊢ p ⊔ q ⟷ q ⊔ p := equiv_or_symm _ _

@[simp] lemma and_destruct (p q : F) : T ⊢ p ⟶ q ⟶ p ⊓ q := and_destruct p q

@[simp] lemma imply_or_left (p q : F) : T ⊢ p ⟶ p ⊔ q := imply_or_left p q

@[simp] lemma imply_or_right (p q : F) : T ⊢ q ⟶ p ⊔ q := imply_or_right p q

lemma disjunction_of {n} {p : finitary F n} (i) (h : T ⊢ p i) : T ⊢ finitary.disjunction n p :=
disjunction_of i h

@[simp] lemma imply_and (p q r : F) : T ⊢ (p ⟶ q) ⟶ (p ⟶ r) ⟶ p ⟶ q ⊓ r := imply_and p q r

@[simp] lemma neg_and_equiv_or_neg (p q : F) : T ⊢ ∼(p ⊓ q) ⟷ ∼p ⊔ ∼q := neg_and_equiv_or_neg p q

@[simp] lemma neg_conj_equiv_disj_neg {n} (p : finitary F n) : T ⊢ ∼(finitary.conjunction n p) ⟷ (⋁ i, ∼p i) :=
neg_conj_equiv_disj_neg p

@[simp] lemma neg_or_equiv_and_neg (p q : F) : T ⊢ ∼(p ⊔ q) ⟷ ∼p ⊓ ∼q := neg_or_equiv_and_neg p q

@[simp] lemma neg_disj_equiv_conj_neg {n} (p : finitary F n) : T ⊢ ∼(finitary.disjunction n p) ⟷ (⋀ i, ∼p i) :=
neg_disj_equiv_conj_neg p

@[simp] lemma or_imply (p q r : F) : T ⊢ (p ⟶ r) ⟶ (q ⟶ r) ⟶ p ⊔ q ⟶ r := or_imply p q r

lemma cases_of (p q : F) (ht : T ⊢ p ⟶ q) (hf : T ⊢ ∼p ⟶ q) : T ⊢ q :=
or_imply p (∼p) q ⨀ ht ⨀ hf ⨀ (by simp)

@[simp] lemma and_imply_equiv_imply_imply (p q r : F) : T ⊢ (p ⟶ q ⟶ r) ⟷ (p ⊓ q ⟶ r) := and_imply_equiv_imply_imply p q r

@[simp] lemma and_imply_of {p q r : F} : T ⊢ p ⊓ q ⟶ r ↔ T ⊢ p ⟶ q ⟶ r :=
and_imply_of

@[simp] lemma imply_and_equiv_or_imply (p q r : F) : T ⊢ (p ⟶ r) ⊓ (q ⟶ r) ⟷ p ⊔ q ⟶ r := imply_and_equiv_or_imply p q r

@[simp] lemma conj_imply_iff_disj_imply {n} (p : finitary F n) (q : F) : T ⊢ (⋀ i, (p i ⟶ q)) ⟷ ((⋁ i, p i) ⟶ q) := conj_imply_iff_disj_imply p q

lemma explosion {p : F} (h₁ : T ⊢ p) (h₂ : T ⊢ ∼p) {q : F} : T ⊢ q :=
explosion h₁ h₂

lemma contrapose {p q : F} : T ⊢ ∼p ⟶ ∼q ↔ T ⊢ q ⟶ p :=
contrapose

lemma and_imply_of_imply_left {p₁ p₂ q : F} (h : T ⊢ p₁ ⟶ q) : T ⊢ p₁ ⊓ p₂ ⟶ q :=
and_imply_of_imply_left h

lemma and_imply_of_imply_right {p₁ p₂ q : F} (h : T ⊢ p₂ ⟶ q) : T ⊢ p₁ ⊓ p₂ ⟶ q :=
and_imply_of_imply_right h

lemma equiv_imply_of_equiv {p₁ q₁ p₂ q₂ : F} (hp : T ⊢ p₁ ⟷ p₂) (hq : T ⊢ q₁ ⟷ q₂) : T ⊢ (p₁ ⟶ q₁) ⟷ (p₂ ⟶ q₂) :=
equiv_imply_of_equiv hp hq

lemma imply_of_equiv {p₁ q₁ p₂ q₂ : F} (h : T ⊢ p₁ ⟶ q₁) (hp : T ⊢ p₁ ⟷ p₂) (hq : T ⊢ q₁ ⟷ q₂) : T ⊢ p₂ ⟶ q₂ :=
imply_of_equiv h hp hq

lemma equiv_neg_of_equiv {p₁ p₂ : F} (hp : T ⊢ p₁ ⟷ p₂) : T ⊢ ∼p₁ ⟷ ∼p₂ :=
equiv_neg_of_equiv hp

lemma neg_of_equiv {p₁ p₂ : F} (h : T ⊢ ∼p₁) (hp : T ⊢ p₁ ⟷ p₂) : T ⊢ ∼p₂ :=
neg_of_equiv h hp

lemma equiv_and_of_equiv {p₁ q₁ p₂ q₂ : F} (hp : T ⊢ p₁ ⟷ p₂) (hq : T ⊢ q₁ ⟷ q₂) : T ⊢ p₁ ⊓ q₁ ⟷ p₂ ⊓ q₂ :=
equiv_and_of_equiv hp hq

lemma and_of_equiv {p₁ q₁ p₂ q₂: F} (h : T ⊢ p₁ ⊓ q₁) (hp : T ⊢ p₁ ⟷ p₂) (hq : T ⊢ q₁ ⟷ q₂) : T ⊢ p₂ ⊓ q₂ :=
and_of_equiv h hp hq

lemma equiv_or_of_equiv {p₁ q₁ p₂ q₂: F} (hp :  T ⊢ p₁ ⟷ p₂) (hq :  T ⊢ q₁ ⟷ q₂) : T ⊢ p₁ ⊔ q₁ ⟷ p₂ ⊔ q₂ :=
equiv_or_of_equiv hp hq

lemma or_of_equiv {p₁ q₁ p₂ q₂: F} (h : T ⊢ p₁ ⊔ q₁) (hp :  T ⊢ p₁ ⟷ p₂) (hq :  T ⊢ q₁ ⟷ q₂) : T ⊢ p₂ ⊔ q₂ :=
or_of_equiv h hp hq

lemma equiv_equiv_of_equiv {p₁ q₁ p₂ q₂: F} (hp :  T ⊢ p₁ ⟷ p₂) (hq :  T ⊢ q₁ ⟷ q₂) : T ⊢ (p₁ ⟷ q₁) ⟷ (p₂ ⟷ q₂) :=
equiv_equiv_of_equiv hp hq

lemma equiv_of_equiv {p₁ q₁ p₂ q₂: F} (h : T ⊢ p₁ ⟷ q₁) (hp :  T ⊢ p₁ ⟷ p₂) (hq :  T ⊢ q₁ ⟷ q₂) : T ⊢ p₂ ⟷ q₂ :=
equiv_of_equiv h hp hq

lemma case_of_ax {p q r : F} (hpq : T ⊢ p ⊔ q) (hpr : T ⊢ p ⟶ r) (hqr : T ⊢ q ⟶ r) : T ⊢ r :=
case_of_p hpq hpr hqr

@[simp] lemma neg_lconj_equiv_ldisj_neg (l : list F) : T ⊢ ∼l.conjunction ⟷ (l.map has_negation.neg).disjunction :=
neg_lconj_equiv_ldisj_neg l

lemma ldisj_of {l : list F} (p) (hp : p ∈ l) (h : T ⊢ p) : T ⊢ l.disjunction :=
ldisj_of hp h

lemma fdisj_of {s : finset F} (p) (hp : p ∈ s) (h : T ⊢ p) : T ⊢ s.disjunction :=
fdisj_of hp h

@[simp] lemma imply_ldisj {l : list F} {p : F} (h : p ∈ l) : T ⊢ p ⟶ l.disjunction :=
imply_ldisj h

lemma imply_fdisj {s : finset F} {p : F} (h : p ∈ s) : T ⊢ p ⟶ s.disjunction :=
imply_fdisj h

@[simp] lemma ldisj_imply_of {l : list F} {q : F} (h : ∀ p ∈ l, T ⊢ p ⟶ q) : T ⊢ l.disjunction ⟶ q :=
ldisj_imply_of h

@[simp] lemma fdisj_imply_of {s : finset F} {q : F} (h : ∀ p ∈ s, T ⊢ p ⟶ q) : T ⊢ s.disjunction ⟶ q :=
fdisj_imply_of h

lemma fdisj_insert_equiv_sup {s : finset F} {p : F} : T ⊢ (insert p s).disjunction ⟷ s.disjunction ⊔ p :=
fdisj_insert_equiv_sup

lemma fconj_imply_equiv_fdisj_neg (p : F) (s : finset F) :
  T ⊢ (s.conjunction ⟶ p) ⟷ (insert p (s.image has_negation.neg)).disjunction :=
fconj_imply_equiv_fdisj_neg p s

@[simp] lemma insert (p) : T +{ p } ⊢ p := by_axiom (by simp)

@[simp] lemma singleton (p) : (singleton p : set F) ⊢ p := by_axiom (by simp)

lemma by_axiom' {T : set F} {p : F} : T p → T ⊢ p := by_axiom

@[simp] lemma provable_not_bot_iff : T ⊢ ⊥ ⟷ ∼(⊤ : F) := by simp[@not_top_eq_bot F _ ((⊢) T) _]

@[simp] lemma provable_not_bot_iff' : T ⊢ ∼(⊤ : F) ⟷ ⊥ := by simp[@not_top_eq_bot F _ ((⊢) T) _]

@[simp] lemma neg_bot_equiv_top : T ⊢ (∼⊥ : F) ⟷ ⊤ :=
neg_bot_equiv_top

variables (T)

@[reducible] def equiv : F → F → Prop := equiv ((⊢) T)

end axiomatic_classical_logic'

namespace axiomatic_classical_logic
open axiomatic_classical_logic'
open_locale aclogic

variables {F : Type*} [has_logic_symbol F]
  (T : set F) [axiomatic_classical_logic F]

variables {T}

@[simp] lemma weakening_insert {q : F} (h : T ⊢ q) (p) : T +{ p } ⊢ q :=
weakening (show T ⊆ T +{ p }, by { intros x h, simp[h] }) h

theorem deduction {p q} : (T +{ p } ⊢ q) ↔ (T ⊢ p ⟶ q) :=
⟨deduction', λ h, by { have : T +{ p } ⊢ p ⟶ q, simp[h], exact this ⨀ (by simp) }⟩

@[simp]
lemma axiom_and {p₁ p₂ q : F} : T +{ p₁ ⊓ p₂ } ⊢ q ↔ T +{ p₁ } +{ p₂ } ⊢ q :=
⟨λ h,
 by { have lmm₁ : T +{ p₁ } +{ p₂ } ⊢ p₁ ⊓ p₂, by simp[axiomatic_classical_logic'.iff_and],
      have lmm₂ : T +{ p₁ } +{ p₂ } ⊢ p₁ ⊓ p₂ ⟶ q, simp[deduction.mp h],
      exact lmm₂ ⨀ lmm₁ },
 λ h,
 by { have lmm₁ : T +{ p₁ ⊓ p₂ } ⊢ p₁ ⟶ p₂ ⟶ q, simp[deduction.mp (deduction.mp h)],
      have lmm₂ : T +{ p₁ ⊓ p₂ } ⊢ p₁ ⊓ p₂, from insert _, simp only [axiomatic_classical_logic'.iff_and] at lmm₂,
      exact lmm₁ ⨀ lmm₂.1 ⨀ lmm₂.2 } ⟩

lemma axiom_lconj {l : list F} {q : F} : T +{ l.conjunction } ⊢ q ↔ T ∪ { p | p ∈ l } ⊢ q :=
begin
  induction l with p l IH generalizing T,
  { simp[deduction] },
  { simp[IH, show insert p T ∪ {p : F | p ∈ l} = T ∪ {r : F | r = p ∨ r ∈ l}, by ext r; simp; tauto] }
end

lemma axiom_fconj {s : finset F} {q : F} : T +{ s.conjunction } ⊢ q ↔ T ∪ ↑s ⊢ q :=
by simp[finset.conjunction, axiom_lconj]

lemma fdisj_insert {s : finset F} {p : F} : ∅ ⊢ (insert p s).disjunction ↔ has_negation.neg '' ↑s ⊢ p :=
begin
  have empty_iff : {(finset.image has_negation.neg s).conjunction} ⊢ p ↔ has_negation.neg '' ↑s ⊢ p,
  by simpa using @axiom_fconj F _ ∅ _ (s.image has_negation.neg) p,
  have : ∅ ⊢ (insert p s).disjunction ↔ ∅ ⊢ ((s.image has_negation.neg).conjunction ⟶ p),
  from iff_of_equiv (classical_logic.fdisj_insert_equiv_fconj_imply p s),
  simp[this, ←deduction], exact empty_iff
end

@[simp] lemma axiom_and' {p₁ p₂ q : F} : singleton (p₁ ⊓ p₂) ⊢ q ↔ singleton p₁ +{ p₂ } ⊢ q :=
by simpa using @axiom_and _ _ ∅ _ p₁ p₂ q

lemma raa {p : F} (q : F) (h₁ : T+{p} ⊢ q) (h₂ : T+{p} ⊢ ∼q) : T ⊢ ∼p :=
classical_logic.neg_hyp (deduction.mp (classical_logic.explosion h₁ h₂))

lemma list_conjunction_mem {P : list F} : ∀ {p}, p ∈ P → T ⊢ P.conjunction ⟶ p :=
by { induction P with p P IH; simp; intros q hq, exact hyp_right (IH hq) p }

lemma list_conjunction_weakening {P Q : list F} : 
  Q ⊆ P → T ⊢ P.conjunction ⟶ Q.conjunction :=
begin
  induction Q with q Q IH; simp,
  intros hyp_q hyp_Q,
  have lmm₁ : T+{P.conjunction} ⊢ q, from deduction.mpr (list_conjunction_mem hyp_q),  
  have lmm₂ : T+{P.conjunction} ⊢ Q.conjunction, from deduction.mpr (IH hyp_Q),
  refine deduction.mp _, simp[axiomatic_classical_logic'.iff_and, *]
end

lemma list_conjunction_provable : ∀ {P : list F} (h : ∀ p, p ∈ P → T ⊢ p), T ⊢ P.conjunction
| []       h := by simp
| (p :: P) h := by {
    have lmm₁ : T ⊢ p, { refine h _ _, simp },
    have lmm₂ : T ⊢ P.conjunction,
    { refine list_conjunction_provable (λ p hyp, h _ _), simp, right, exact hyp },
    simp, refine ⟨lmm₁, lmm₂⟩ }

/-
lemma finitary.conjunction_mem {n : ℕ} {P : finitary F n} :
  ∀ {p}, p ∈ P → T ⊢ finitary.conjunction n P ⟶ p :=
begin
  induction n with n IH; simp[finitary.conjunction],
  { simp[has_mem.mem, finitary.mem] },
  { intros p hp, rcases hp with (_ | _), }
  --simp[has_mem.mem, finitary.mem],
  --intros p mem,
  --exact and_imply_of_imply_right (IH mem)
end
-/

@[reducible] def empty_axiom (p : F) : Prop := ∅ ⊢ p

prefix `⬝⊢ `:45 := empty_axiom

section empty_axiom
variables (T)

lemma of_empty_axiom {p : F} (hp : ⬝⊢ p) : T ⊢ p := weakening (by simp) hp

end empty_axiom

variables (T)

@[reducible] def lindenbaum := classical_logic.lindenbaum ((⊢) T : F → Prop)

notation (name := classical_logic.equiv) p ` ≈[`:50 T :50 `] `:0 q:50 := classical_logic.equiv ((⊢) T) p q

namespace lindenbaum

instance : boolean_algebra (lindenbaum T) := classical_logic.lindenbaum.boolean_algebra

end lindenbaum

end axiomatic_classical_logic