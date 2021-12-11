import fopl

universes u v

namespace fopl

variables {L : language}

local infix ` ≃₁ `:50 := ((≃) : term L → term L → formula L)
local prefix `∏₁ `:64 := (has_univ_quantifier.univ : formula L → formula L)
local prefix `∐₁ `:64 := (has_exists_quantifier.ex : formula L → formula L)

namespace formula

@[simp] def fal_rank : formula L → ℕ
| (p ⟶ q) := max (fal_rank p) (fal_rank q)
| (⁻p)     := fal_rank p
| (∏₁ p)  := fal_rank p + 1
| _        := 0

@[simp] lemma fal_rank_and (p q : formula L) :
  fal_rank (p ⊓ q) = max (fal_rank p) (fal_rank q) := rfl

@[simp] lemma fal_rank_or (p q : formula L) :
  fal_rank (p ⊔ q) = max (fal_rank p) (fal_rank q) := rfl

@[simp] lemma fal_rank_ex (p : formula L) :
  fal_rank (∐₁ p) = fal_rank p + 1 := rfl

@[simp] lemma fal_rank_eq (t u : term L) :
  fal_rank (t ≃₁ u) = 0 := rfl

@[simp] lemma fal_rank_le [has_le_symbol L] (t u : term L) :
  fal_rank (t ≼ u : formula L) = 0 := rfl

@[simp] lemma fal_rank_mem [has_mem_symbol L] (t u : term L) :
  fal_rank (t ∊ u : formula L) = 0 := rfl

@[simp] def binary_inv : formula L → option (formula L × formula L)
| (p ⟶ q) := some (p, q)
| _        := none

@[simp] def unary_inv : formula L → option (formula L)
| ⁻p := some p
| ∏₁p := some p
| _  := none

@[simp] def fal_fn_aux : ℕ → (term L → formula L) → formula L → formula L
| s f (p ⟶ q) := fal_fn_aux s (λ t, (f t).binary_inv.iget.1) p ⟶ fal_fn_aux s (λ t, (f t).binary_inv.iget.2) q
| s f ⁻p       := ⁻fal_fn_aux s (λ t, (f t).unary_inv.iget) p
| s f (∏₁ p)  := ∏ fal_fn_aux (s + 1) (λ t, (f t).unary_inv.iget) p
| s f _        := f #s

@[simp] lemma fal_fn_aux_imply (s) (f g : term L → formula L) (p q : formula L) :
  fal_fn_aux s (λ x, f x ⟶ g x) (p ⟶ q) = fal_fn_aux s f p ⟶ fal_fn_aux s g q := rfl

@[simp] lemma fal_fn_aux_neg (s) (f : term L → formula L) (p : formula L) :
  fal_fn_aux s (λ x, ⁻f x) (⁻p) = ⁻fal_fn_aux s f p := rfl

@[simp] lemma fal_fn_aux_fal (s) (f : term L → formula L) (p : formula L) :
  fal_fn_aux s (λ x, ∏ (f x)) (∏ p) = ∏ fal_fn_aux (s + 1) f p := rfl

@[simp] lemma fal_fn_aux_and (s) (f g : term L → formula L) (p q : formula L) :
  fal_fn_aux s (λ x, f x ⊓ g x) (p ⊓ q) = fal_fn_aux s f p ⊓ fal_fn_aux s g q := rfl

@[simp] lemma fal_fn_aux_or (s) (f g : term L → formula L) (p q : formula L) :
  fal_fn_aux s (λ x, f x ⊔ g x) (p ⊔ q) = fal_fn_aux s f p ⊔ fal_fn_aux s g q := rfl

@[simp] lemma fal_fn_aux_iff (s) (f g : term L → formula L) (p q : formula L) :
  fal_fn_aux s (λ x, f x ⟷ g x) (p ⟷ q) = fal_fn_aux s f p ⟷ fal_fn_aux s g q :=
by simp[lrarrow_def]

@[simp] lemma fal_fn_aux_ex (s) (f : term L → formula L) (p : formula L) :
  fal_fn_aux s (λ x, ∐ (f x)) (∐ p) = ∐ fal_fn_aux (s + 1) f p := rfl

@[simp] lemma fal_fn_aux_eq (s) (f g : term L → term L) (t u : term L) :
  fal_fn_aux s (λ x, f x ≃ g x) (t ≃ u) = (f #s ≃ g #s) := rfl

@[simp] lemma fal_fn_aux_le [has_le_symbol L] (s) (f g : term L → term L) (t u : term L) :
  fal_fn_aux s (λ x, f x ≼ g x) (t ≼ u) = (f #s ≼ g #s) := rfl

@[simp] lemma fal_fn_aux_mem [has_mem_symbol L] (s) (f g : term L → term L) (t u : term L) :
  fal_fn_aux s (λ x, f x ∊ g x) (t ∊ u) = (f #s ∊ g #s) := rfl

@[simp] lemma fal_fn_constant (s) (p : formula L) :
  fal_fn_aux s (λ x, p) p = p :=
by induction p generalizing s; simp*

end formula

def fal_fn (p : term L → formula L) : formula L := ∏ formula.fal_fn_aux 0 p (p #0)

def ex_fn (p : term L → formula L) : formula L := ∐ formula.fal_fn_aux 0 p (p #0)

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

notation `∀₁` binders ` ≼ᵇ ` t `, ` r:(scoped p, bfal_le_fn t p) := r

def bex_lt_fn [has_prec (term L) (formula L)] (t : term L) (p : term L → formula L) : formula L :=
∃₁ x, ((x ≺ t) ⊓ p x)

notation `∃₁` binders ` ≼ᵇ ` t `, ` r:(scoped p, bex_le_fn t p) := r

def bfal_mem_fn [has_elem (term L) (formula L)] (t : term L) (p : term L → formula L) : formula L :=
∀₁ x, (x ∊ t) ⟶ p x

notation `∀₁` binders ` ∊ᵇ ` t `, ` r:(scoped p, bfal_mem_fn t p) := r

def bex_mem_fn [has_elem (term L) (formula L)] (t : term L) (p : term L → formula L) : formula L :=
∃₁ x, (x ∊ t) ⊓ p x

notation `∃₁` binders ` ∊ᵇ ` t `, ` r:(scoped p, bex_mem_fn t p) := r

#check ∀₁ x, x ≃ x

end fopl