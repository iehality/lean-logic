import lib

universe u

namespace classical_logic

variables {F : Type*} [has_negation F] [has_arrow F] [has_inf F] [has_sup F] [has_top F] [has_bot F]
  (P : set F) (T : set F) [CL : classical_logic P]
include CL

@[simp] lemma neg_top_eq : (⁻⊤ : F) = ⊥ := eq.symm (bot_eq P)

variables {P}

@[simp] lemma not_top_eq_bot : (⁻⊤ : F) = ⊥ := eq.symm (classical_logic.bot_eq P)

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

@[simp] lemma dne (p : F) : ⁻⁻p ⟶ p ∈ P :=
begin
  have lmm₁ : ⁻⁻p ⟶ (⁻⁻⁻⁻p ⟶ ⁻⁻p) ⟶ ⁻p ⟶ ⁻⁻⁻p ∈ P, simp,
  have lmm₂ : ⁻⁻p ⟶ ⁻⁻⁻⁻p ⟶ ⁻⁻p ∈ P, simp,
  have lmm₃ : ⁻⁻p ⟶ (⁻p ⟶ ⁻⁻⁻p) ⟶ ⁻⁻p ⟶ p ∈ P, simp,  
  have lmm₄ : ⁻⁻p ⟶ ⁻p ⟶ ⁻⁻⁻p ∈ P, from lmm₁ ⨀₁ lmm₂,
  have lmm₅ : ⁻⁻p ⟶ ⁻⁻p ⟶ p ∈ P, from lmm₃ ⨀₁ lmm₄,
  have lmm₆ : ⁻⁻p ⟶ ⁻⁻p ∈ P, simp,
  exact lmm₅ ⨀₁ lmm₆
end

@[simp] lemma dni (p : F) : p ⟶ ⁻⁻p ∈ P :=
by { have : (⁻⁻⁻p ⟶ ⁻p) ⟶ p ⟶ ⁻⁻p ∈ P, simp, exact this ⨀ (by simp) }

@[simp] lemma dn_iff {p : F} : ⁻⁻p ∈ P ↔ p ∈ P :=
⟨λ h, (show ⁻⁻p ⟶ p ∈ P, by simp) ⨀ h, λ h, (show p ⟶ ⁻⁻p ∈ P, by simp) ⨀ h⟩

@[simp] lemma dn1_iff {p q : F} : (⁻⁻p ⟶ q ∈ P) ↔ (p ⟶ q ∈ P) :=
⟨impl_trans (dni _), impl_trans (dne _)⟩

@[simp] lemma dn2_iff {p q : F} : (p ⟶ ⁻⁻q ∈ P) ↔ (p ⟶ q ∈ P) :=
⟨λ h, impl_trans h (dne _), λ h, impl_trans h (dni _)⟩

lemma explosion {p : F} (h₁ : p ∈ P) (h₂ : ⁻p ∈ P) {q : F} : q ∈ P :=
begin
  have : ⁻p ⟶ ⁻q ⟶ ⁻p ∈ P, simp,
  have : ⁻q ⟶ ⁻p ∈ P, from this ⨀ h₂,
  have : p ⟶ q ∈ P, from (show (⁻q ⟶ ⁻p) ⟶ p ⟶ q ∈ P, by simp) ⨀ this,
  exact this ⨀ h₁
end

lemma explosion_hyp {p q : F} (h₁ : p ⟶ q ∈ P) (h₂ : p ⟶ ⁻q ∈ P) {r : F} : p ⟶ r ∈ P :=
begin
  have : p ⟶ ⁻q ⟶ ⁻r ⟶ ⁻q ∈ P, simp,
  have : p ⟶ ⁻r ⟶ ⁻q ∈ P, from this ⨀₁ h₂,
  have : p ⟶ q ⟶ r ∈ P, from (show p ⟶ (⁻r ⟶ ⁻q) ⟶ q ⟶ r ∈ P, by simp) ⨀₁ this,
  exact this ⨀₁ h₁
end

lemma explosion_hyp₂ {p q r : F} (h₁ : p ⟶ q ⟶ r ∈ P) (h₂ : p ⟶ q ⟶ ⁻r ∈ P) {s : F} : p ⟶ q ⟶ s ∈ P :=
begin
  have : p ⟶ q ⟶ ⁻r ⟶ ⁻s ⟶ ⁻r ∈ P, simp,
  have : p ⟶ q ⟶ ⁻s ⟶ ⁻r ∈ P, from this ⨀₂ h₂,
  have : p ⟶ q ⟶ r ⟶ s ∈ P, from (show p ⟶ q ⟶ (⁻s ⟶ ⁻r) ⟶ r ⟶ s ∈ P, by simp) ⨀₂ this,
  exact this ⨀₂ h₁
end

@[simp] lemma hyp_bot (p : F) : ⊥ ⟶ p ∈ P :=
explosion_hyp (show (⊥ ⟶ ⊤ : F) ∈ P, by simp) (show (⊥ : F) ⟶ ⁻⊤ ∈ P, by simp[neg_top_eq P])

lemma contrapose {p q : F} : (⁻p ⟶ ⁻q ∈ P) ↔ (q ⟶ p ∈ P) :=
⟨λ h, (show (⁻p ⟶ ⁻q) ⟶ q ⟶ p ∈ P, by simp) ⨀ h, λ h,
  by { have : ⁻⁻q ⟶ p ∈ P, from impl_trans (show ⁻⁻q ⟶ q ∈ P, by simp) h,
       exact (show (⁻⁻q ⟶ ⁻⁻p) ⟶ ⁻p ⟶ ⁻q ∈ P, by simp) ⨀ (impl_trans this (show p ⟶ ⁻⁻p ∈ P, by simp)) }⟩

lemma neg_hyp {p : F} (h : p ⟶ ⁻p ∈ P) : ⁻p ∈ P :=
begin
  have : p ⟶ ⁻(p ⟶ ⁻p) ∈ P,
  { have lmm₁ : p ⟶ p ∈ P, { simp }, exact explosion_hyp lmm₁ h },
  have : (p ⟶ ⁻p) ⟶ ⁻p ∈ P, from impl_trans (dni _) (contrapose.mpr this),
  exact this ⨀ h
end

lemma raa {p : F} (q : F) (h₁ : p ⟶ q ∈ P) (h₂ : p ⟶ ⁻q ∈ P) : ⁻p ∈ P :=
neg_hyp (explosion_hyp h₁ h₂)

@[simp] lemma and_left (p q : F) : p ⊓ q ⟶ p ∈ P :=
begin
  simp[and_def P],
  have : ⁻p ⟶ p ⟶ ⁻q ∈ P, from explosion_hyp₂ (show ⁻p ⟶ p ⟶ p ∈ P, by simp) (show ⁻p ⟶ p ⟶ ⁻p ∈ P, by simp),
  have : ⁻(p ⟶ ⁻q) ⟶ ⁻⁻p ∈ P, from contrapose.mpr this,
  simp* at*
end

@[simp] lemma and_right (p q : F) : p ⊓ q ⟶ q ∈ P :=
begin
  simp[and_def P],
  have : ⁻q ⟶ p ⟶ ⁻q ∈ P, simp,
  have : ⁻(p ⟶ ⁻q) ⟶ q ∈ P, from impl_trans (contrapose.mpr this) (by simp),
  exact this
end

@[simp] lemma and_inply_left {p₁ p₂ q : F} : (p₁ ⟶ q) ⟶ p₁ ⊓ p₂ ⟶ q ∈ P :=
(show (p₁ ⟶ q) ⟶ p₁ ⊓ p₂ ⟶ p₁ ⟶ q ∈ P, by simp) ⨀₂ (show (p₁ ⟶ q) ⟶ p₁ ⊓ p₂ ⟶ p₁ ∈ P, by simp)

lemma and_inply_of_imply_left {p₁ p₂ q : F} (h : p₁ ⟶ q ∈ P) : p₁ ⊓ p₂ ⟶ q ∈ P :=
(show (p₁ ⟶ q) ⟶ p₁ ⊓ p₂ ⟶ q ∈ P, by simp) ⨀ h

@[simp] lemma and_imply_right {p₁ p₂ q : F} : (p₂ ⟶ q) ⟶ p₁ ⊓ p₂ ⟶ q ∈ P :=
(show (p₂ ⟶ q) ⟶ p₁ ⊓ p₂ ⟶ p₂ ⟶ q ∈ P, by simp) ⨀₂ (show (p₂ ⟶ q) ⟶ p₁ ⊓ p₂ ⟶ p₂ ∈ P, by simp)

lemma and_inply_of_imply_right {p₁ p₂ q : F} (h : p₂ ⟶ q ∈ P) : p₁ ⊓ p₂ ⟶ q ∈ P :=
(show (p₂ ⟶ q) ⟶ p₁ ⊓ p₂ ⟶ q ∈ P, by simp) ⨀ h

@[simp] lemma iff_and {p q : F} : (p ⊓ q ∈ P) ↔ (p ∈ P ∧ q ∈ P) :=
⟨λ h, by { split,
   { exact modus_ponens (show p ⊓ q ⟶ p ∈ P, by simp) h },
   { exact modus_ponens (show p ⊓ q ⟶ q ∈ P, by simp) h } },
 λ h, by { simp[and_def P], rcases h with ⟨h₁, h₂⟩,
   have : (p ⟶ ⁻q) ⟶ ⁻q ∈ P, from (show (p ⟶ ⁻q) ⟶ p ⟶ ⁻q ∈ P, by simp) ⨀₁ (by simp[h₁]),
   have : q ⟶ ⁻(p ⟶ ⁻q) ∈ P, from impl_trans (dni _) (contrapose.mpr this),
   exact modus_ponens this h₂ }⟩

@[simp] lemma iff_equiv {p q : F} : (p ⟷ q ∈ P) ↔ (p ⟶ q ∈ P ∧ q ⟶ p ∈ P) :=
by simp[lrarrow_def, iff_and]

lemma equiv_imply_of_equiv {p₁ q₁ p₂ q₂ : F} (hp : p₁ ⟷ p₂ ∈ P) (hq : q₁ ⟷ q₂ ∈ P) : (p₁ ⟶ q₁) ⟷ (p₂ ⟶ q₂) ∈ P :=
begin
  simp[iff_equiv] at*, split,
  { have : (p₁ ⟶ q₁) ⟶ p₂ ⟶ q₁ ∈ P, from (show (p₁ ⟶ q₁) ⟶ p₂ ⟶ p₁ ⟶ q₁ ∈ P, by simp) ⨀₂ (by simp[hp]),
    exact (show (p₁ ⟶ q₁) ⟶ p₂ ⟶ q₁ ⟶ q₂ ∈ P, by simp[hq]) ⨀₂ this },
  { have : (p₂ ⟶ q₂) ⟶ p₁ ⟶ q₂ ∈ P, from (show (p₂ ⟶ q₂) ⟶ p₁ ⟶ p₂ ⟶ q₂ ∈ P, by simp) ⨀₂ (by simp[hp]),
    exact (show (p₂ ⟶ q₂) ⟶ p₁ ⟶ q₂ ⟶ q₁ ∈ P, by simp[hq]) ⨀₂ this }
end

lemma imply_of_equiv {p₁ q₁ p₂ q₂ : F} (h : p₁ ⟶ q₁ ∈ P) (hp : p₁ ⟷ p₂ ∈ P) (hq : q₁ ⟷ q₂ ∈ P) : p₂ ⟶ q₂ ∈ P :=
by { have : (p₁ ⟶ q₁) ⟶ p₂ ⟶ q₂ ∈ P ∧ (p₂ ⟶ q₂) ⟶ p₁ ⟶ q₁ ∈ P, from iff_equiv.mp (equiv_imply_of_equiv hp hq),
     exact this.1 ⨀ h }

lemma equiv_neg_of_equiv {p₁ p₂ : F} (hp : p₁ ⟷ p₂ ∈ P) : ⁻p₁ ⟷ ⁻p₂ ∈ P :=
by simp[iff_equiv, contrapose] at*; simp[hp]

lemma neg_of_equiv {p₁ p₂ : F} (h : ⁻p₁ ∈ P) (hp : p₁ ⟷ p₂ ∈ P) : ⁻p₂ ∈ P :=
by { have : ⁻p₁ ⟶ ⁻p₂ ∈ P, from (iff_equiv.mp (equiv_neg_of_equiv hp)).1, exact this ⨀ h }

lemma equiv_and_of_equiv {p₁ q₁ p₂ q₂: F} (hp : p₁ ⟷ p₂ ∈ P) (hq : q₁ ⟷ q₂ ∈ P) : p₁ ⊓ q₁ ⟷ p₂ ⊓ q₂ ∈ P :=
by { simp only [and_def P], refine equiv_neg_of_equiv (equiv_imply_of_equiv hp (equiv_neg_of_equiv hq)) }

lemma and_of_equiv {p₁ q₁ p₂ q₂: F} (h : p₁ ⊓ q₁ ∈ P) (hp : p₁ ⟷ p₂ ∈ P) (hq : q₁ ⟷ q₂ ∈ P) : p₂ ⊓ q₂ ∈ P :=
by { have : p₁ ⊓ q₁ ⟶ p₂ ⊓ q₂ ∈ P, from (iff_equiv.mp (equiv_and_of_equiv hp hq)).1, exact this ⨀ h }

lemma equiv_or_of_equiv {p₁ q₁ p₂ q₂: F} (hp : p₁ ⟷ p₂ ∈ P) (hq : q₁ ⟷ q₂ ∈ P) : p₁ ⊔ q₁ ⟷ p₂ ⊔ q₂ ∈ P :=
by { simp only [or_def P], refine (equiv_imply_of_equiv (equiv_neg_of_equiv hp) hq) }

lemma or_of_equiv {p₁ q₁ p₂ q₂: F} (h : p₁ ⊔ q₁ ∈ P) (hp : p₁ ⟷ p₂ ∈ P) (hq : q₁ ⟷ q₂ ∈ P) : p₂ ⊔ q₂ ∈ P :=
by { have : p₁ ⊔ q₁ ⟶ p₂ ⊔ q₂ ∈ P, from (iff_equiv.mp (equiv_or_of_equiv hp hq)).1, exact this ⨀ h }

lemma equiv_equiv_of_equiv {p₁ q₁ p₂ q₂: F} (hp : p₁ ⟷ p₂ ∈ P) (hq : q₁ ⟷ q₂ ∈ P) : (p₁ ⟷ q₁) ⟷ (p₂ ⟷ q₂) ∈ P :=
by { refine (equiv_and_of_equiv (equiv_imply_of_equiv hp hq) (equiv_imply_of_equiv hq hp)) }

lemma equiv_of_equiv {p₁ q₁ p₂ q₂: F} (h : p₁ ⟷ q₁ ∈ P) (hp : p₁ ⟷ p₂ ∈ P) (hq : q₁ ⟷ q₂ ∈ P) : p₂ ⟷ q₂ ∈ P :=
by { have : (p₁ ⟷ q₁) ⟶ (p₂ ⟷ q₂) ∈ P, from (iff_equiv.mp (equiv_equiv_of_equiv hp hq)).1, exact this ⨀ h }

@[simp] lemma equiv_refl (p : F) : p ⟷ p ∈ P := by simp[iff_equiv]

lemma equiv_symm {p q : F} : p ⟷ q ∈ P → q ⟷ p ∈ P := by { simp[iff_equiv], intros, simp* }

lemma equiv_trans {p q r : F} : p ⟷ q ∈ P → q ⟷ r ∈ P → p ⟷ r ∈ P :=
by { simp[iff_equiv], intros hpq hqp hqr hrq, exact ⟨impl_trans hpq hqr, impl_trans hrq hqp⟩ }


variables (P)

@[reducible] def equiv (p q : F) : Prop := p ⟷ q ∈ P

theorem equiv_equivalence : equivalence (equiv P) :=
⟨equiv_refl, @equiv_symm _ _ _ _ _ _ _ _ _, @equiv_trans _ _ _ _ _ _ _ _ _⟩

variables {P}

@[simp] lemma iff_dn_refl_right (p : F) : p ⟷ ⁻⁻p ∈ P := by simp[iff_equiv]

@[simp] lemma iff_dn_refl_left (p : F) : ⁻⁻p ⟷ p ∈ P := by simp[iff_equiv]

@[simp] lemma contraposition_inv (p q : F) : (p ⟶ q) ⟶ (⁻q ⟶ ⁻p) ∈ P :=
by { have : (⁻⁻p ⟶ ⁻⁻q) ⟶ ⁻q ⟶ ⁻p ∈ P, simp, 
     refine imply_of_equiv this (equiv_imply_of_equiv _ _) _; simp }

@[simp] lemma contraposition_iff (p q : F) : (p ⟶ q) ⟷ (⁻q ⟶ ⁻p) ∈ P :=
by simp[iff_equiv]

@[simp] lemma contraposition_iff_inv (p q : F) : (⁻p ⟶ ⁻q) ⟷ (q ⟶ p) ∈ P :=
by simp[iff_equiv]

@[simp] lemma neg_hyp' (p : F) : (p ⟶ ⁻p) ⟶ ⁻p ∈ P :=
begin
  have : (p ⟶ ⁻p) ⟶ p ⟶ ⁻(p ⟶ ⁻p) ∈ P,
  { have lmm₁ : (p ⟶ ⁻p) ⟶ p ⟶ p ∈ P, { simp }, exact explosion_hyp₂ lmm₁ (by simp) },
  have : (p ⟶ ⁻p) ⟶ ⁻⁻(p ⟶ ⁻p) ⟶ ⁻p ∈ P,
  { refine imply_of_equiv this _ _; simp[iff_equiv] },
  exact this ⨀₁ (show (p ⟶ ⁻p) ⟶ ⁻⁻(p ⟶ ⁻p) ∈ P, by simp)
end

@[simp] lemma neg_iff (p : F) : ⁻p ⟷ (p ⟶ ⊥) ∈ P :=
begin
  simp[iff_equiv], split,
  { exact explosion_hyp₂ (show ⁻p ⟶ p ⟶ p ∈ P, by simp) (show ⁻p ⟶ p ⟶ ⁻p ∈ P, by simp) },
  { have : (p ⟶ ⊥) ⟶ p ⟶ ⁻p ∈ P,
      from explosion_hyp₂ (show (p ⟶ ⊥) ⟶ p ⟶ ⊤ ∈ P, by simp) (show (p ⟶ ⊥) ⟶ p ⟶ ⁻⊤ ∈ P, by simp[bot_eq P]),
    refine (show (p ⟶ ⊥) ⟶ (p ⟶ ⁻p) ⟶ ⁻p ∈ P, by simp) ⨀₁ this }
end

@[simp] lemma neg_impl_equiv_and (p q : F) : ⁻(p ⟶ q) ⟷ p ⊓ ⁻q ∈ P :=
by simp only [and_def P]; refine (equiv_neg_of_equiv (equiv_imply_of_equiv _ _)); simp

lemma neg_impl_iff_and {p q : F} : (⁻(p ⟶ q) ∈ P) ↔ (p ⊓ ⁻q ∈ P) :=
begin
  simp [and_def P], split; intros h,
  { refine neg_of_equiv h (equiv_imply_of_equiv _ _); simp },
  { refine neg_of_equiv h (equiv_imply_of_equiv _ _); simp }
end

@[simp] lemma equiv_symm_and (p q : F) : p ⊓ q ⟷ q ⊓ p ∈ P :=
by { simp only [and_def P], refine equiv_neg_of_equiv _,
     refine equiv_of_equiv (show p ⟶ ⁻q ⟷ ⁻⁻q ⟶ ⁻p ∈ P, by simp) _ (equiv_imply_of_equiv _ _); simp }

@[simp] lemma equiv_symm_equiv (p q : F) : (p ⟷ q) ⟷ (q ⟷ p) ∈ P := equiv_symm_and _ _

@[simp] lemma equiv_symm_or (p q : F) : p ⊔ q ⟷ q ⊔ p ∈ P :=
by { simp only [or_def P],
     refine equiv_of_equiv (show ⁻p ⟶ q ⟷ ⁻q ⟶ ⁻⁻p ∈ P, by simp) _ (equiv_imply_of_equiv _ _); simp }

@[simp] lemma and_destruct (p q : F) : p ⟶ q ⟶ p ⊓ q ∈ P :=
by { simp only [and_def P],
     have : p ⟶ (p ⟶ ⁻q) ⟶ ⁻q ∈ P, from (show p ⟶ (p ⟶ ⁻q) ⟶ p ⟶ ⁻q ∈ P, by simp) ⨀₂ (show p ⟶ (p ⟶ ⁻q) ⟶ p ∈ P, by simp),
     refine imply_of_equiv this (by simp) _,
     have : (p ⟶ ⁻q) ⟶ ⁻q ⟷ ⁻⁻q ⟶ ⁻(p ⟶ ⁻q) ∈ P, { simp }, refine equiv_of_equiv this _ (equiv_imply_of_equiv _ _); simp }

@[simp] lemma imply_or_left (p q : F) : p ⟶ p ⊔ q ∈ P :=
by simp[or_def P]; refine explosion_hyp₂ (show p ⟶ ⁻p ⟶ p ∈ P, by simp) (show p ⟶ ⁻p ⟶ ⁻p ∈ P, by simp)

@[simp] lemma imply_or_right (p q : F) : q ⟶ p ⊔ q ∈ P :=
by simp[or_def P]

@[simp] lemma imply_and (p q r : F) : (p ⟶ q) ⟶ (p ⟶ r) ⟶ p ⟶ q ⊓ r ∈ P :=
begin
  have : (p ⟶ q) ⟶ (p ⟶ r) ⟶ p ⟶ r ⟶ q ⊓ r ∈ P,
    from (show (p ⟶ q) ⟶ (p ⟶ r) ⟶ p ⟶ q ⟶ r ⟶ q ⊓ r ∈ P, by simp) ⨀₃ (show (p ⟶ q) ⟶ (p ⟶ r) ⟶ p ⟶ q ∈ P, by simp),
  exact this ⨀₃ (show (p ⟶ q) ⟶ (p ⟶ r) ⟶ p ⟶ r ∈ P, by simp),
end

@[simp] lemma neg_and_equiv_or_neg (p q : F) : ⁻(p ⊓ q) ⟷ ⁻p ⊔ ⁻q ∈ P :=
begin
  simp only [and_def P, or_def P],
  refine equiv_of_equiv (show p ⟶ ⁻q ⟷ p ⟶ ⁻q ∈ P, by simp) _ (equiv_imply_of_equiv _ _); simp
end

@[simp] lemma neg_or_equiv_and_neg (p q : F) : ⁻(p ⊔ q) ⟷ ⁻p ⊓ ⁻q ∈ P :=
begin
  simp only [and_def P, or_def P],
  refine equiv_of_equiv (show ⁻(⁻p ⟶ q) ⟷ ⁻(⁻p ⟶ q) ∈ P, by simp) _ (equiv_neg_of_equiv (equiv_imply_of_equiv _ _)); simp
end

@[simp] lemma or_imply (p q r : F) : (p ⟶ r) ⟶ (q ⟶ r) ⟶ p ⊔ q ⟶ r ∈ P :=
begin
  have : (⁻r ⟶ ⁻p) ⟶ (⁻r ⟶ ⁻q) ⟶ ⁻r ⟶ ⁻p ⊓ ⁻q ∈ P, { simp },
  refine imply_of_equiv this (by simp) (equiv_imply_of_equiv (by simp) _),
  have : ⁻r ⟶ ⁻(p ⊔ q) ⟷ p ⊔ q ⟶ r ∈ P, { simp },
  refine equiv_of_equiv (show ⁻r ⟶ ⁻(p ⊔ q) ⟷ p ⊔ q ⟶ r ∈ P, by simp) (equiv_imply_of_equiv _ _) _; simp
end

@[simp] lemma le_sup_inf (p q r : F) : (p ⊔ q) ⊓ (p ⊔ r) ⟶ p ⊔ q ⊓ r ∈ P :=
begin
  simp[or_def P],
  exact (show (⁻p ⟶ q) ⊓ (⁻p ⟶ r) ⟶ (⁻p ⟶ q) ⟶ (⁻p ⟶ r) ⟶ ⁻p ⟶ q ⊓ r ∈ P, by simp) ⨀₁
        (show (⁻p ⟶ q) ⊓ (⁻p ⟶ r) ⟶ (⁻p ⟶ q) ∈ P, by simp) ⨀₁
        (show (⁻p ⟶ q) ⊓ (⁻p ⟶ r) ⟶ (⁻p ⟶ r) ∈ P, by simp)
end

variables (P)

def lindenbaum := quotient (⟨equiv P, equiv_equivalence P⟩ : setoid F)

variables {P}

def to_quo (p : F) : lindenbaum P := quotient.mk' p

#check @to_quo _ _ _ _ _ _ _ P _

local notation `⟦` p `⟧ᶜ` := @to_quo _ _ _ _ _ _ _ P _ p

namespace lindenbaum

@[elab_as_eliminator]
protected lemma ind_on {C : lindenbaum P → Prop} (d : lindenbaum P)
  (h : ∀ p : F, C (to_quo p)) : C d := quotient.induction_on' d h

@[elab_as_eliminator, reducible]
protected def lift_on {φ : Sort*} (p : lindenbaum P) (f : F → φ)
  (h : ∀ p q : F, p ⟷ q ∈ P → f p = f q) : φ := quotient.lift_on' p f h

@[simp]
protected lemma lift_on_eq {φ : Sort*} (p : F) (f : F → φ)
  (h : ∀ p q, p ⟷ q ∈ P → f p = f q) : classical_logic.lindenbaum.lift_on ⟦p⟧ᶜ f h = f p := rfl

@[elab_as_eliminator, reducible]
protected def lift_on₂ {φ : Sort*} (p₁ p₂ : lindenbaum P) (f : F → F → φ)
  (h : ∀ p₁ p₂ q₁ q₂, p₁ ⟷ q₁ ∈ P → p₂ ⟷ q₂ ∈ P → f p₁ p₂ = f q₁ q₂) : φ :=
quotient.lift_on₂' p₁ p₂ f h

@[simp]
protected lemma lift_on₂_eq {φ : Sort*} (p₁ p₂ : F) (f : F → F → φ)
  (h : ∀ p₁ p₂ q₁ q₂, p₁ ⟷ q₁ ∈ P → p₂ ⟷ q₂ ∈ P → f p₁ p₂ = f q₁ q₂)  :
classical_logic.lindenbaum.lift_on₂ ⟦p₁⟧ᶜ ⟦p₂⟧ᶜ f h = f p₁ p₂ := rfl

@[elab_as_eliminator, reducible]
protected def lift_on_finitary {φ : Sort*} {n : ℕ} (v : finitary (lindenbaum P) n) (f : finitary F n → φ)
  (h : ∀ v₁ v₂ : finitary F n, (∀ n, v₁ n ⟷ v₂ n ∈ P) → f v₁ = f v₂) : φ :=
quotient.lift_on_finitary v f h 

@[simp]
protected lemma lift_on_finitary_eq {φ : Sort*} {n : ℕ} (v : finitary F n) (f : finitary F n → φ)
  (h : ∀ v₁ v₂ : finitary F n, (∀ n, v₁ n ⟷ v₂ n ∈ P) → f v₁ = f v₂) :
classical_logic.lindenbaum.lift_on_finitary (λ x, ⟦v x⟧ᶜ) f h = f v :=
quotient.lift_on_finitary_eq v f h

@[simp]
lemma of_eq_of {p q : F} : ⟦p⟧ᶜ = ⟦q⟧ᶜ ↔ p ⟷ q ∈ P :=
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
       simp[has_le.le], intros h₁ h₂, simp* },
  inf := λ p₁ p₂, classical_logic.lindenbaum.lift_on₂ p₁ p₂ (λ p₁ p₂, ⟦p₁ ⊓ p₂⟧ᶜ)
    (λ p₁ p₂ q₁ q₂ h₁ h₂, by { simp[-iff_equiv], exact equiv_and_of_equiv h₁ h₂ }),
  sup := λ p₁ p₂, classical_logic.lindenbaum.lift_on₂ p₁ p₂ (λ p₁ p₂, ⟦p₁ ⊔ p₂⟧ᶜ)
    (λ p₁ p₂ q₁ q₂ h₁ h₂, by { simp[-iff_equiv], exact equiv_or_of_equiv h₁ h₂ }),
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

instance : has_compl (lindenbaum P) := ⟨λ p, classical_logic.lindenbaum.lift_on p (λ p, ⟦⁻p⟧ᶜ)
    (λ p q h, by { simp[-iff_equiv], exact equiv_neg_of_equiv h })⟩

lemma neg_def (p : F) : (to_quo p)ᶜ = ⟦⁻p⟧ᶜ := rfl

lemma inf_def (p q : F) : to_quo p ⊓ to_quo q = ⟦p ⊓ q⟧ᶜ := rfl

lemma sup_def (p q : F) : to_quo p ⊔ to_quo q = ⟦p ⊔ q⟧ᶜ := rfl

--instance : bounded_order (lindenbaum P) :=


instance : boolean_algebra (lindenbaum P) :=
{ ..lindenbaum.distrib_lattice }

end lindenbaum

end classical_logic

namespace axiomatic_classical_logic'
open classical_logic
variables {F : Type*} [has_negation F] [has_arrow F] [has_inf F] [has_sup F] [has_top F] [has_bot F]
  (T : set F) [axiomatic_classical_logic' F]

instance : classical_logic ((⊢) T) := axiomatic_classical_logic'.classical

variables {T}

lemma modus_ponens {p q : F} : T ⊢ p ⟶ q → T ⊢ p → T ⊢ q := modus_ponens

local infixl ` ⨀ `:90 := axiomatic_classical_logic'.modus_ponens

@[simp] lemma mem_iff_prov (p : F) : (@has_mem.mem F (set F) _) p ((⊢) T : set F) ↔ T ⊢ p := by refl

@[simp] lemma imply₁ (p q) : T ⊢ p ⟶ q ⟶ p := imply₁

@[simp] lemma imply₂ (p q r) : T ⊢ (p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r := imply₂

@[simp] lemma contraposition (p q) : T ⊢ (⁻p ⟶ ⁻q) ⟶ q ⟶ p := contraposition

@[simp] lemma provable_top : T ⊢ (⊤ : F) := provable_top

@[simp] lemma refl (p : F) : T ⊢ p ⟶ p := classical_logic.refl p

@[simp] lemma hyp_right {p : F} (h : T ⊢ p) (q) : T ⊢ q ⟶ p := hyp_right h q

@[simp] lemma dne (p : F) : T ⊢ ⁻⁻p ⟶ p := dne p

@[simp] lemma dni (p : F) : T ⊢ p ⟶ ⁻⁻p := dni p

@[simp] lemma dn_iff {p : F} : T ⊢ ⁻⁻p ↔ T ⊢ p := dn_iff

@[simp] lemma dn1_iff {p q : F} : T ⊢ ⁻⁻p ⟶ q ↔ T ⊢ p ⟶ q := dn1_iff

@[simp] lemma dn2_iff {p q : F} : T ⊢ p ⟶ ⁻⁻q ↔ T ⊢ p ⟶ q := dn2_iff

@[simp] lemma hyp_bot (p : F) : T ⊢ ⊥ ⟶ p := hyp_bot p

@[simp] lemma and_left (p q : F) : T ⊢ p ⊓ q ⟶ p := and_left p q

@[simp] lemma and_right (p q : F) : T ⊢ p ⊓ q ⟶ q := and_right p q

@[simp] lemma iff_and {p q : F} : T ⊢ p ⊓ q ↔ (T ⊢ p ∧ T ⊢ q) := iff_and

@[simp] lemma iff_equiv {p q : F} : T ⊢ p ⟷ q ↔ (T ⊢ p ⟶ q ∧ T ⊢ q ⟶ p) := iff_equiv

@[simp] lemma equiv_refl (p : F) : T ⊢ p ⟷ p := equiv_refl p

@[simp] lemma iff_dn_refl_right (p : F) : T ⊢ p ⟷ ⁻⁻p := iff_dn_refl_right p

@[simp] lemma iff_dn_refl_left (p : F) : T ⊢ ⁻⁻p ⟷ p := iff_dn_refl_left p

@[simp] lemma contraposition_inv (p q : F) : T ⊢ (p ⟶ q) ⟶ (⁻q ⟶ ⁻p) := contraposition_inv p q

@[simp] lemma contraposition_iff (p q : F) : T ⊢ (p ⟶ q) ⟷ (⁻q ⟶ ⁻p) := contraposition_iff p q

@[simp] lemma contraposition_iff_inv (p q : F) : T ⊢ (⁻p ⟶ ⁻q) ⟷ (q ⟶ p) := contraposition_iff_inv p q

@[simp] lemma neg_hyp' (p : F) : T ⊢ (p ⟶ ⁻p) ⟶ ⁻p := neg_hyp' p

@[simp] lemma neg_iff (p : F) : T ⊢ ⁻p ⟷ (p ⟶ ⊥) := neg_iff p

@[simp] lemma neg_impl_equiv_and (p q : F) : T ⊢ ⁻(p ⟶ q) ⟷ p ⊓ ⁻q := neg_impl_equiv_and p q

lemma neg_impl_iff_and {p q : F} : T ⊢ ⁻(p ⟶ q) ↔ T ⊢ p ⊓ ⁻q := neg_impl_iff_and

@[simp] lemma equiv_symm_and (p q : F) : T ⊢ p ⊓ q ⟷ q ⊓ p := equiv_symm_and p q

@[simp] lemma equiv_symm_equiv (p q : F) : T ⊢ (p ⟷ q) ⟷ (q ⟷ p) := equiv_symm_equiv p q

@[simp] lemma and_destruct (p q : F) : T ⊢ p ⟶ q ⟶ p ⊓ q := and_destruct p q

@[simp] lemma imply_or_left (p q : F) : T ⊢ p ⟶ p ⊔ q := imply_or_left p q

@[simp] lemma imply_or_right (p q : F) : T ⊢ q ⟶ p ⊔ q := imply_or_right p q

@[simp] lemma imply_and (p q r : F) : T ⊢ (p ⟶ q) ⟶ (p ⟶ r) ⟶ p ⟶ q ⊓ r := imply_and p q r

@[simp] lemma neg_and_equiv_or_neg (p q : F) : T ⊢ ⁻(p ⊓ q) ⟷ ⁻p ⊔ ⁻q := neg_and_equiv_or_neg p q

@[simp] lemma neg_or_equiv_and_neg (p q : F) : T ⊢ ⁻(p ⊔ q) ⟷ ⁻p ⊓ ⁻q := neg_or_equiv_and_neg p q

@[simp] lemma or_imply (p q r : F) : T ⊢ (p ⟶ r) ⟶ (q ⟶ r) ⟶ p ⊔ q ⟶ r := or_imply p q r

@[simp] lemma insert (p) : T +{ p } ⊢ p := by_axiom (by simp)

variables (T)

def equiv : F → F → Prop := equiv ((⊢) T)

end axiomatic_classical_logic'

namespace axiomatic_classical_logic
open classical_logic axiomatic_classical_logic'

variables {F : Type*} [has_negation F] [has_arrow F] [has_inf F] [has_sup F] [has_top F] [has_bot F]
  (T : set F) [axiomatic_classical_logic F]

local infixl ` ⨀ `:90 := axiomatic_classical_logic'.modus_ponens

variables {T}

@[simp] lemma weakening_insert {q : F} (h : T ⊢ q) (p) : T +{ p } ⊢ q :=
weakening (show T ⊆ T +{ p }, by { intros x h, simp[h] }) h

theorem deduction {p q} : (T +{ p } ⊢ q) ↔ (T ⊢ p ⟶ q) :=
⟨deduction', λ h, by { have : T +{ p } ⊢ p ⟶ q, simp[h], exact this ⨀ (by simp) }⟩

lemma axiom_and {p₁ p₂ q : F} : T +{ p₁ ⊓ p₂ } ⊢ q ↔ T +{ p₁ } +{ p₂ } ⊢ q :=
⟨λ h,
 by { have lmm₁ : T +{ p₁ } +{ p₂ } ⊢ p₁ ⊓ p₂, by simp[axiomatic_classical_logic'.iff_and],
      have lmm₂ : T +{ p₁ } +{ p₂ } ⊢ p₁ ⊓ p₂ ⟶ q, simp[deduction.mp h],
      exact lmm₂ ⨀ lmm₁ },
 λ h,
 by { have lmm₁ : T +{ p₁ ⊓ p₂ } ⊢ p₁ ⟶ p₂ ⟶ q, simp[deduction.mp (deduction.mp h)],
      have lmm₂ : T +{ p₁ ⊓ p₂ } ⊢ p₁ ⊓ p₂, from insert _, simp only [axiomatic_classical_logic'.iff_and] at lmm₂,
      exact lmm₁ ⨀ lmm₂.1 ⨀ lmm₂.2 } ⟩

lemma raa {p} (q) (h₁ : T+{p} ⊢ q) (h₂ : T+{p} ⊢ ⁻q) : T ⊢ ⁻p :=
neg_hyp (deduction.mp (explosion h₁ h₂))

end axiomatic_classical_logic

