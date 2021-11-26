import lib

universe u

namespace classical_logic

def mk' (F : Sort*) [has_negation F] [has_arrow F] [has_top F] [has_turnstile (set F) F]
(deduction' : ∀ {T : set F} {p q : F}, T +{ p } ⊢ q → T ⊢ p ⟶ q)
(weakening : ∀ {T : set F} {U : set F} {p : F}, T ⊆ U → T ⊢ p → U ⊢ p)
(modus_ponens : ∀ {T : set F} {p q : F}, T ⊢ p ⟶ q → T ⊢ p → T ⊢ q)
(by_axiom : ∀ {T : set F} {p : F}, p ∈ T → T ⊢ p)
(imply₁ : ∀ {T : set F} {p q : F}, T ⊢ p ⟶ q ⟶ p)
(imply₂ : ∀ {T : set F} {p q r : F}, T ⊢ (p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r)
(contrapose : ∀ {T : set F} {p q : F}, T ⊢ (⁻p ⟶ ⁻q) ⟶ q ⟶ p)
(provable_top : ∀ {T : set F}, T ⊢ (⊤ : F)) : classical_logic (F : Sort*) :=
{ deduction' := @deduction',
  weakening := @weakening,
  modus_ponens := @modus_ponens,
  by_axiom := @by_axiom,
  imply₁ := @imply₁,
  imply₂ := @imply₂,
  contrapose := @contrapose,
  provable_top := @provable_top,
  bot := ⁻⊤,
  inf := λ p q, ⁻(p ⟶ ⁻q),
  sup := λ p q, ⁻p ⟶ q,
  provable_bot := by simp,  
  and_def := by simp,
  or_def := by simp }

variables {F : Type*} (T : set F) [classical_logic F]

@[simp] lemma not_top_eq_bot : (⁻⊤ : F) = ⊥ := by simp[classical_logic.provable_bot]

@[simp] lemma refl (p : F) : T ⊢ p ⟶ p :=
begin
  have l₀ : T ⊢ (p ⟶ (p ⟶ p) ⟶ p) ⟶ (p ⟶ p ⟶ p) ⟶ p ⟶ p, simp,
  have l₁ : T ⊢ p ⟶ (p ⟶ p) ⟶ p, simp,
  have l₂ : T ⊢ (p ⟶ p ⟶ p) ⟶ p ⟶ p, refine modus_ponens l₀ l₁,
  have l₃ : T ⊢ p ⟶ p ⟶ p, simp,
  refine modus_ponens l₂ l₃
end

variables {T}

@[simp] lemma insert (p) : T+{p} ⊢ p :=
by_axiom (by simp)

@[simp] lemma weakening_insert {q : F} (h : T ⊢ q) (p) : T +{ p } ⊢ q :=
weakening (show T ⊆ T +{ p }, by { intros x h, simp[h] }) h

theorem deduction {p q} : (T +{ p } ⊢ q) ↔ (T ⊢ p ⟶ q) :=
⟨deduction', λ h, by { have : T+{p} ⊢ p ⟶ q, simp[h], exact modus_ponens this (by simp) }⟩

@[simp] lemma hyp_right {p : F} (h : T ⊢ p) (q) : T ⊢ q ⟶ p :=
by { have : T ⊢ p ⟶ q ⟶ p, simp,
     exact modus_ponens this h }

lemma modus_ponens_hyp {p q r: F} (hqr : T ⊢ p ⟶ q ⟶ r) (hq : T ⊢ p ⟶ q) : T ⊢ p ⟶ r :=
by { have : T ⊢ (p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r, simp,
     exact modus_ponens (modus_ponens this hqr) hq }

lemma imp_trans {p q r : F} : (T ⊢ p ⟶ q) → (T ⊢ q ⟶ r) → (T ⊢ p ⟶ r) := λ h₁ h₂,
begin
  have l₁ : T ⊢ (p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ (p ⟶ r), simp,  
  have l₂ : T ⊢ (p ⟶ q ⟶ r), simp[h₂],
  have l₃ : T ⊢ (p ⟶ q) ⟶ (p ⟶ r), from modus_ponens l₁ l₂,
  exact modus_ponens l₃ h₁
end

@[simp] lemma dne (p : F) : T ⊢ ⁻⁻p ⟶ p :=
begin
  have lmm₁ : T ⊢ ⁻⁻p ⟶ (⁻⁻⁻⁻p ⟶ ⁻⁻p) ⟶ ⁻p ⟶ ⁻⁻⁻p, simp,
  have lmm₂ : T ⊢ ⁻⁻p ⟶ ⁻⁻⁻⁻p ⟶ ⁻⁻p, simp,
  have lmm₃ : T ⊢ ⁻⁻p ⟶ (⁻p ⟶ ⁻⁻⁻p) ⟶ ⁻⁻p ⟶ p, simp,  
  have lmm₄ : T ⊢ ⁻⁻p ⟶ ⁻p ⟶ ⁻⁻⁻p, from modus_ponens_hyp lmm₁ lmm₂,
  have lmm₅ : T ⊢ ⁻⁻p ⟶ ⁻⁻p ⟶ p, from modus_ponens_hyp lmm₃ lmm₄,
  have lmm₆ : T ⊢ ⁻⁻p ⟶ ⁻⁻p, simp,
  exact modus_ponens_hyp lmm₅ lmm₆
end

@[simp] lemma dni (p : F) : T ⊢ p ⟶ ⁻⁻p :=
by { have : T ⊢ (⁻⁻⁻p ⟶ ⁻p) ⟶ p ⟶ ⁻⁻p, simp,
     exact modus_ponens this (by simp) }

@[simp] lemma dn_iff {p : F} : T ⊢ ⁻⁻p ↔ T ⊢ p :=
⟨λ h, modus_ponens (show T ⊢ ⁻⁻p ⟶ p, by simp) h, λ h, modus_ponens (show T ⊢ p ⟶ ⁻⁻p, by simp) h⟩


@[simp] lemma dn1_iff {p q : F} : (T ⊢ ⁻⁻p ⟶ q) ↔ (T ⊢ p ⟶ q) :=
⟨imp_trans (dni _), imp_trans (dne _)⟩

@[simp] lemma dn2_iff {p q : F} : (T ⊢ p ⟶ ⁻⁻q) ↔ (T ⊢ p ⟶ q) :=
⟨λ h, imp_trans h (dne _), λ h, imp_trans h (dni _)⟩

lemma explosion {p : F} (h₁ : T ⊢ p) (h₂ : T ⊢ ⁻p) {q : F} : T ⊢ q :=
begin
  have : T ⊢ ⁻p ⟶ ⁻q ⟶ ⁻p, simp,
  have : T ⊢ ⁻q ⟶ ⁻p, from modus_ponens this h₂,
  have : T ⊢ p ⟶ q, from modus_ponens (show T ⊢ (⁻q ⟶ ⁻p) ⟶ p ⟶ q, by simp) this,
  exact modus_ponens this h₁
end

lemma explosion_hyp {p q : F} (h₁ : T ⊢ p ⟶ q) (h₂ : T ⊢ p ⟶ ⁻q) {r : F} : T ⊢ p ⟶ r :=
begin
  have : T ⊢ p ⟶ ⁻q ⟶ ⁻r ⟶ ⁻q, simp,
  have : T ⊢ p ⟶ ⁻r ⟶ ⁻q, from modus_ponens_hyp this h₂,
  have : T ⊢ p ⟶ q ⟶ r, from modus_ponens_hyp (show T ⊢ p ⟶ (⁻r ⟶ ⁻q) ⟶ q ⟶ r, by simp) this,
  exact modus_ponens_hyp this h₁
end

@[simp] lemma hyp_bot {p : F} : T ⊢ ⊥ ⟶ p :=
explosion_hyp (show T ⊢ (⊥ ⟶ ⊤ : F), by simp) (show T ⊢ (⊥ ⟶ ⁻⊤ : F), by simp)

lemma contraposition {p q : F} : (T ⊢ ⁻p ⟶ ⁻q) ↔ (T ⊢ q ⟶ p) :=
⟨λ h, modus_ponens (show T ⊢ (⁻p ⟶ ⁻q) ⟶ q ⟶ p, by simp) h, λ h,
  by { refine modus_ponens (show T ⊢ (⁻⁻q ⟶ ⁻⁻p) ⟶ ⁻p ⟶ ⁻q, by simp) _,
       have : T ⊢ ⁻⁻q ⟶ p, from imp_trans (show T ⊢ ⁻⁻q ⟶ q, by simp) h,
       exact imp_trans this (show T ⊢ p ⟶ ⁻⁻p, by simp) }⟩

lemma neg_hyp {p : F} (h : T ⊢ p ⟶ ⁻p) : T ⊢ ⁻p :=
begin
  have : T+{p} ⊢ ⁻(p ⟶ ⁻p),
  { have lmm₁ : T+{p} ⊢ p, simp,
    have lmm₂ : T+{p} ⊢ ⁻p, from modus_ponens (weakening_insert h _) lmm₁,
    exact explosion lmm₁ lmm₂ },
  have : T ⊢ p ⟶ ⁻(p ⟶ ⁻p), from deduction.mp this,
  have : T ⊢ (p ⟶ ⁻p) ⟶ ⁻p, from imp_trans (dni _) (contraposition.mpr this),
  exact modus_ponens this h
end

lemma raa {p : F} (q : F) (h₁ : T +{ p } ⊢ q) (h₂ : T +{ p } ⊢ ⁻q) : T ⊢ ⁻p :=
neg_hyp (deduction.mp (explosion h₁ h₂))

@[simp] lemma and_left (p q : F) : T ⊢ p ⊓ q ⟶ p :=
begin
  simp[and_def],
  have : T+{⁻p}+{p} ⊢ ⁻q, 
    from explosion (show T+{⁻p}+{p} ⊢ p, by simp) (show T+{⁻p}+{p} ⊢ ⁻p, by simp),
  have : T ⊢ ⁻p ⟶ p ⟶ ⁻q, from (deduction.mp (deduction.mp this)),
  exact imp_trans (contraposition.mpr this) (by simp)
end

@[simp] lemma and_right (p q : F) : T ⊢ p ⊓ q ⟶ q :=
begin
  simp[and_def],
  have : T ⊢ ⁻q ⟶ p ⟶ ⁻q, simp,
  have : T ⊢ ⁻(p ⟶ ⁻q) ⟶ q, from imp_trans (contraposition.mpr this) (by simp),
  exact this
end

@[simp] lemma and {p q : F} : (T ⊢ p ⊓ q) ↔ (T ⊢ p ∧ T ⊢ q) :=
⟨λ h, by { split,
   { exact modus_ponens (show T ⊢ p ⊓ q ⟶ p, by simp) h },
   { exact modus_ponens (show T ⊢ p ⊓ q ⟶ q, by simp) h } },
 λ h, by {simp[and_def], rcases h with ⟨h₁, h₂⟩,
   show T ⊢ ⁻(p ⟶ ⁻q),
   have : T+{p ⟶ ⁻q} ⊢ ⁻q, from modus_ponens (insert _) (by simp[h₁]),
   have : T ⊢ (p ⟶ ⁻q) ⟶ ⁻q, from deduction.mp this,
   have : T ⊢ q ⟶ ⁻(p ⟶ ⁻q), from imp_trans (dni _) (contraposition.mpr this),
   exact modus_ponens this h₂ }⟩

@[simp] lemma iff {p q : F} : (T ⊢ p ⟷ q) ↔ (T ⊢ p ⟶ q ∧ T ⊢ q ⟶ p) :=
by simp[lrarrow_def]

@[simp] lemma neg_imp {p q : F} : (T ⊢ ⁻(p ⟶ q)) ↔ (T ⊢ p ⊓ ⁻q) :=
begin
  simp only [and_def], split; intros h,
  { apply raa (p ⟶ q),
    { have : T+{p ⟶ ⁻⁻q} ⊢ p ⟶ ⁻⁻q, from insert _, simp* at * },
    { simp[h] } },
  { apply raa (p ⟶ ⁻⁻q); simp[h] }
end

lemma or_l (p q : F) : T ⊢ p ⟶ p ⊔ q :=
by simp[or_def]; refine deduction.mp (deduction.mp (explosion (show T +{ p } +{ ⁻p } ⊢ p, by simp) (by simp)))

lemma or_r (p q : F) : T ⊢ q ⟶ p ⊔ q :=
by simp[or_def]; refine deduction.mp (weakening h _)

lemma hyp_or {p₁ p₂ q : F} : (T ⊢ p₁ ⟶ q) → (T ⊢ p₂ ⟶ q) → (T ⊢ p₁ ⊔ p₂ ⟶ q) := λ h₁ h₂,
begin
  simp[or_def], apply contraposition.mp, refine deduction.mp _, simp,
  refine ⟨deduction.mpr (contraposition.mpr h₁), deduction.mpr (contraposition.mpr h₂)⟩, 
end

lemma hyp_and_left {p₁ p₂ q : F} : (T ⊢ p₁ ⟶ q) → (T ⊢ p₁ ⊓ p₂ ⟶ q) := λ h,
begin
  have : T+{p₁ ⊓ p₂} ⊢ p₁, { have : T+{p₁ ⊓ p₂} ⊢ p₁ ⊓ p₂, from insert _, simp* at * },
  refine deduction.mp (modus_ponens (show T+{p₁ ⊓ p₂} ⊢ p₁ ⟶ q, by simp[h]) this)
end

lemma hyp_and_right {p₁ p₂ q : F} : (T ⊢ p₂ ⟶ q) → (T ⊢ p₁ ⊓ p₂ ⟶ q) := λ h,
begin
  have : T+{p₁ ⊓ p₂} ⊢ p₂, { have : T+{p₁ ⊓ p₂} ⊢ p₁ ⊓ p₂, from insert _, simp* at * },
  refine deduction.mp (modus_ponens (show T+{p₁ ⊓ p₂} ⊢ p₂ ⟶ q, by simp[h]) this)
end

lemma axiom_and {p₁ p₂ q : F} : T +{ p₁ ⊓ p₂ } ⊢ q ↔ T +{ p₁ } +{ p₂ } ⊢ q :=
⟨λ h,
 by { have lmm₁ : T+{p₁}+{p₂} ⊢ p₁ ⊓ p₂, by simp,
      have lmm₂ : T+{p₁}+{p₂} ⊢ p₁ ⊓ p₂ ⟶ q, simp[deduction.mp h],
      exact modus_ponens lmm₂ lmm₁ },
 λ h,
 by { have lmm₁ : T+{p₁ ⊓ p₂} ⊢ p₁ ⟶ p₂ ⟶ q, simp[deduction.mp (deduction.mp h)],
      have lmm₂ : T+{p₁ ⊓ p₂} ⊢ p₁ ⊓ p₂, from insert _, simp at lmm₂,
      exact modus_ponens (modus_ponens lmm₁ lmm₂.1) lmm₂.2 } ⟩

end classical_logic

