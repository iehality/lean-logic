import FOL.completeness

universes u v

namespace fol
open_locale logic_symbol

variables {L : language}

namespace formula

def bfal_le [has_preceq (term L) (formula L)] (t : term L) (p : formula L) : formula L :=
∏ ((#0 ≼ (t^1)) ⟶ p)

notation `∏{≼ ` t `} `:64 p := bfal_le t p

def bex_le [has_preceq (term L) (formula L)] (t : term L) (p : formula L) : formula L :=
⁻∏{≼ t}⁻p

notation `∐{≼ ` t `} `:64 p := bex_le t p

def bfal_lt [has_prec (term L) (formula L)] (t : term L) (p : formula L) : formula L :=
∏ ((#0 ≺ t^1) ⟶ p)

notation `∏{≺ ` t `} `:64 p := bfal_lt t p

def bex_lt [has_prec (term L) (formula L)] (t : term L) (p : formula L) : formula L :=
⁻∏{≺ t}⁻p

notation `∐{≺ ` t `} `:64 p := bex_lt t p

def bfal_mem [has_elem (term L) (formula L)] (t : term L) (p : formula L) : formula L :=
∏ ((#0 ∊ t^1) ⟶ p)

notation `∏{∊ ` t `} `:64 p := bfal_mem t p

def bex_mem [has_elem (term L) (formula L)] (t : term L) (p : formula L) : formula L :=
∐ ((#0 ∊ t^1) ⊓ p)

notation `∐{∊ ` t `} `:64 p := bex_mem t p

@[simp] lemma bfal_le_rew [has_le_symbol L] (t : term L) (p : formula L) (s) :
  (∏{≼ t} p).rew s = ∏{≼ t.rew s} p.rew (s^1) :=
by simp[bfal_le, term.pow_rew_distrib]

@[simp] lemma bex_le_rew [has_le_symbol L] (t : term L) (p : formula L) (s) :
  (∐{≼ t} p).rew s = ∐{≼ t.rew s} p.rew (s^1) :=
by simp[bex_le, term.pow_rew_distrib]

@[simp] def fal_rank : formula L → ℕ
| (p ⟶ q) := max (fal_rank p) (fal_rank q)
| (⁻p)     := fal_rank p
| (∏ p)  := fal_rank p + 1
| _        := 0

@[simp] lemma fal_rank_and (p q : formula L) :
  fal_rank (p ⊓ q) = max (fal_rank p) (fal_rank q) := rfl

@[simp] lemma fal_rank_or (p q : formula L) :
  fal_rank (p ⊔ q) = max (fal_rank p) (fal_rank q) := rfl

@[simp] lemma fal_rank_ex (p : formula L) :
  fal_rank (∐ p) = fal_rank p + 1 := rfl

@[simp] lemma fal_rank_eq (t u : term L) :
  fal_rank (t ≃ u : formula L) = 0 := rfl

@[simp] lemma fal_rank_le [has_le_symbol L] (t u : term L) :
  fal_rank (t ≼ u : formula L) = 0 := rfl

@[simp] lemma fal_rank_mem [has_mem_symbol L] (t u : term L) :
  fal_rank (t ∊ u : formula L) = 0 := rfl

@[simp] def binary_inv : formula L → option (formula L × formula L)
| (p ⟶ q) := some (p, q)
| _        := none

@[simp] def unary_inv : formula L → option (formula L)
| ⁻p := some p
| ∏ p := some p
| _  := none

@[simp] def quantifier_fn_aux : ℕ → (term L → formula L) → formula L → formula L
| s f ⊤        := ⊤
| s f (p ⟶ q) := quantifier_fn_aux s (λ t, (f t).binary_inv.iget.1) p ⟶ quantifier_fn_aux s (λ t, (f t).binary_inv.iget.2) q
| s f ⁻p       := ⁻quantifier_fn_aux s (λ t, (f t).unary_inv.iget) p
| s f (∏ p)  := ∏ quantifier_fn_aux (s + 1) (λ t, (f t).unary_inv.iget) p
| s f _        := f #s

@[simp] lemma quantifier_fn_aux_imply (s) (f g : term L → formula L) (p q : formula L) :
  quantifier_fn_aux s (λ x, f x ⟶ g x) (p ⟶ q) = quantifier_fn_aux s f p ⟶ quantifier_fn_aux s g q := rfl

@[simp] lemma quantifier_fn_aux_neg (s) (f : term L → formula L) (p : formula L) :
  quantifier_fn_aux s (λ x, ⁻f x) (⁻p) = ⁻quantifier_fn_aux s f p := rfl

@[simp] lemma quantifier_fn_aux_fal (s) (f : term L → formula L) (p : formula L) :
  quantifier_fn_aux s (λ x, ∏ (f x)) (∏ p) = ∏ quantifier_fn_aux (s + 1) f p := rfl

@[simp] lemma quantifier_fn_aux_and (s) (f g : term L → formula L) (p q : formula L) :
  quantifier_fn_aux s (λ x, f x ⊓ g x) (p ⊓ q) = quantifier_fn_aux s f p ⊓ quantifier_fn_aux s g q := rfl

@[simp] lemma quantifier_fn_aux_or (s) (f g : term L → formula L) (p q : formula L) :
  quantifier_fn_aux s (λ x, f x ⊔ g x) (p ⊔ q) = quantifier_fn_aux s f p ⊔ quantifier_fn_aux s g q := rfl

@[simp] lemma quantifier_fn_aux_iff (s) (f g : term L → formula L) (p q : formula L) :
  quantifier_fn_aux s (λ x, f x ⟷ g x) (p ⟷ q) = quantifier_fn_aux s f p ⟷ quantifier_fn_aux s g q :=
by simp[lrarrow_def]

@[simp] lemma quantifier_fn_aux_ex (s) (f : term L → formula L) (p : formula L) :
  quantifier_fn_aux s (λ x, ∐ (f x)) (∐ p) = ∐ quantifier_fn_aux (s + 1) f p := rfl

@[simp] lemma quantifier_fn_aux_eq (s) (f g : term L → term L) (t u : term L) :
  quantifier_fn_aux s (λ x, f x ≃ g x) (t ≃ u) = (f #s ≃ g #s) := rfl

@[simp] lemma quantifier_fn_aux_le [has_le_symbol L] (s) (f g : term L → term L) (t u : term L) :
  quantifier_fn_aux s (λ x, f x ≼ g x) (t ≼ u) = (f #s ≼ g #s) := rfl

@[simp] lemma quantifier_fn_aux_mem [has_mem_symbol L] (s) (f g : term L → term L) (t u : term L) :
  quantifier_fn_aux s (λ x, f x ∊ g x) (t ∊ u) = (f #s ∊ g #s) := rfl

@[simp] lemma fal_fn_constant (s) (p : formula L) :
  quantifier_fn_aux s (λ x, p) p = p :=
by induction p generalizing s; simp*

end formula

def fal_fn (p : term L → formula L) : formula L := ∏ formula.quantifier_fn_aux 0 p (p #0)

def ex_fn (p : term L → formula L) : formula L := ∐ formula.quantifier_fn_aux 0 p (p #0)

notation `∀₁` binders `, ` r:(scoped p, fal_fn p) := r

notation `∃₁` binders `, ` r:(scoped p, ex_fn p) := r

def bfal_le_fn [has_preceq (term L) (formula L)] (t : term L) (p : term L → formula L) : formula L :=
∀₁ x, ((x ≼ t) ⟶ p x)

notation `∀₁` binders ` ≼ᵇ ` t `, ` r:(scoped p, bfal_le_fn t p) := r

def bex_le_fn [has_preceq (term L) (formula L)] (t : term L) (p : term L → formula L) : formula L :=
∃₁ x, ((x ≼ t) ⊓ p x)

notation `∃₁` binders ` ≼ᵇ ` t `, ` r:(scoped p, bex_le_fn t p) := r

def bfal_lt_fn [has_prec (term L) (formula L)] (t : term L) (p : term L → formula L) : formula L :=
∀₁ x, ((x ≺ t) ⟶ p x)

notation `∀₁` binders ` ≺ᵇ ` t `, ` r:(scoped p, bfal_le_fn t p) := r

def bex_lt_fn [has_prec (term L) (formula L)] (t : term L) (p : term L → formula L) : formula L :=
∃₁ x, ((x ≺ t) ⊓ p x)

notation `∃₁` binders ` ≺ᵇ ` t `, ` r:(scoped p, bex_le_fn t p) := r

def bfal_mem_fn [has_elem (term L) (formula L)] (t : term L) (p : term L → formula L) : formula L :=
∀₁ x, (x ∊ t) ⟶ p x

notation `∀₁` binders ` ∊ᵇ ` t `, ` r:(scoped p, bfal_mem_fn t p) := r

def bex_mem_fn [has_elem (term L) (formula L)] (t : term L) (p : term L → formula L) : formula L :=
∃₁ x, (x ∊ t) ⊓ p x

notation `∃₁` binders ` ∊ᵇ ` t `, ` r:(scoped p, bex_mem_fn t p) := r

#check ∀₁ x ≺ᵇ #4, x ≃ x

#check ∐{≼ #3} #4 ≃ #9

variables [has_le_symbol L]

namespace formula

section
variables {L₁ L₂ : language.{u}} [L₁.language_translation_coe L₂]

end

inductive bounded : theory L
| verum : bounded ⊤
| predicate {n} {p : L.pr n} {v} : bounded (❴p❵ v)
| equal {t u : term L} : bounded (t ≃ u)
| imply {p q} : bounded p → bounded q → bounded (p ⟶ q)
| neg {p} : bounded p → bounded (⁻p)
| bfal {t} {p} : bounded p → bounded ∏{≼ t} p

attribute [simp] bounded.verum bounded.predicate bounded.equal bounded.neg

@[simp] lemma bounded_preceq (t u : term L) : bounded (t ≼ u : formula L) :=
bounded.predicate

@[simp] lemma bounded_imply_iff (p q : formula L) : bounded (p ⟶ q) ↔ bounded p ∧ bounded q :=
⟨λ h, by { cases h, simp* }, λ ⟨hp, hq⟩, bounded.imply hp hq⟩

@[simp] lemma bounded_neg_iff (p : formula L) : bounded (⁻p) ↔ bounded p :=
⟨λ h, by { cases h, simp* }, bounded.neg⟩

lemma bounded_of_open {p : formula L} (h : p.is_open) : bounded p :=
begin
  induction p,
  case verum { simp },
  case app { simp },
  case equal { simp },
  case imply : p q IHp IHq { simp at h, exact bounded.imply (IHp h.1) (IHq h.2) },
  case neg : p IH { simp at h, exact bounded.neg (IH h) },
  case fal { simp at h, contradiction }
end

lemma bounded_of_lt {p q : formula L} (hq : bounded q) (h : p < q) : bounded p :=
begin
  induction q; try { simp at h, contradiction },
  case imply : q₁ q₂ IH₁ IH₂
  { simp at h hq, rcases h with (le | le),
    { rcases lt_or_eq_of_le le with (lt | rfl), { exact IH₁ hq.1 lt }, { exact hq.1 } },
    { rcases lt_or_eq_of_le le with (lt | rfl), { exact IH₂ hq.2 lt }, { exact hq.2 } } },
  case neg : q IH
  { simp at h hq, rcases lt_or_eq_of_le h with (lt | rfl), { refine IH hq lt }, { exact hq } },
  case fal : p IH
  { rcases hq with ⟨lo, loo⟩, simp at h,
    rcases lt_or_eq_of_le h with (lt | rfl), { refine IH (by { simp, exact hq_ᾰ}) lt }, { simp, exact hq_ᾰ } }
end

@[simp] lemma bounded_bfal_iff {p : formula L} {t : term L} : bounded (∏{≼ t} p) ↔ bounded p :=
⟨λ h, bounded_of_lt h (by { simp[bfal_le], refine le_of_lt (by simp) }), bounded.bfal⟩

lemma bounded_bex_iff {p : formula L} {t : term L} : bounded (∐{≼ t} p) ↔ bounded p :=
by simp[bex_le]

lemma bounded_rew (s : ℕ → term L) (p : formula L) (h : bounded p) : bounded (rew s p) :=
by induction h generalizing s; simp*

instance bounded_proper : proper_theory (bounded : theory L) :=
⟨λ p s mem, by { simp[set.mem_def] at mem ⊢, induction mem generalizing s; try {simp*} }⟩

mutual inductive is_sigma, is_pi
with is_sigma : ℕ → formula L → Prop
| zero : ∀ {p : formula L}, p.bounded → is_sigma 0 p
| succ : ∀ {p} {n}, is_pi n p → is_sigma (n+1) ∐ p 
with is_pi : ℕ → formula L → Prop
| zero : ∀ {p : formula L}, p.bounded → is_pi 0 p
| succ : ∀ {p} {n}, is_sigma n p → is_pi (n+1) ∏ p

notation `𝛴₀` := is_sigma 0

notation `𝛴₁` := is_sigma 1

notation `𝛱₀` := is_pi 0

notation `𝛱₁` := is_pi 1

@[simp] lemma sigma_0_iff_bounded : (𝛴₀ : theory L) = bounded :=
by funext p; simp; exact ⟨λ h, by { cases h, simp* }, is_sigma.zero⟩

@[simp] lemma pi_0_iff_bounded : (𝛱₀ : theory L) = bounded :=
by funext p; simp; exact ⟨λ h, by { cases h, simp* }, is_pi.zero⟩

private lemma sigma_pi_proper (n : ℕ) : proper_at 0 (is_sigma n : theory L) ∧ proper_at 0 (is_pi n : theory L) :=
begin
  induction n with n IH,
  { simp, refine proper_theory.proper },
  { refine ⟨λ p s hs, _, λ p s hp, _⟩,
    { cases hs with _ _ p _ hp, simp,
      have : is_pi n (p.rew (s^1)),
      { have := IH.2 p (s^1) hp, simp at this, exact this },
      refine is_sigma.succ this },
    { cases hp with _ _ p _ hs, simp,
      have : is_sigma n (p.rew (s^1)),
      { have := IH.1 p (s^1) hs, simp at this, exact this },
      refine is_pi.succ this } }
end

instance is_sigma_proper (n) : proper_theory (is_sigma n : theory L) := ⟨(sigma_pi_proper n).1⟩

instance is_pi_proper (n) : proper_theory (is_pi n : theory L) := ⟨(sigma_pi_proper n).2⟩

end formula

def arithmetical_sigma (T : theory L) (n : ℕ) : theory L :=
λ p, ∃ q, T ⊢ p ⟷ q ∧ q.is_sigma n

notation `𝜮`:60 n ` in ` T :60 := arithmetical_sigma T n

def arithmetical_pi (T : theory L) (n : ℕ) : theory L :=
λ p, ∃ q, T ⊢ p ⟷ q ∧ q.is_pi n

notation `𝜫`:60 n ` in ` T :60 := arithmetical_pi T n

def arithmetical_delta (T : theory L) (n : ℕ) : theory L :=
λ p, p ∈ 𝜮n in T ∧ p ∈ 𝜫n in T

notation `𝜟`:60 n ` in ` T :60 := arithmetical_delta T n



end fol