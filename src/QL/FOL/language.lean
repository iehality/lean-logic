import QL.FOL.deduction

universes u

namespace fol
open_locale logic_symbol
open subterm subformula logic logic.Theory
variables {L L₁ L₂ L₃ : language} {m : ℕ}

namespace language

structure translation (L₁ : language) (L₂ : language) :=
(fn : Π n, L₁.fn n → L₂.fn n)
(pr : Π n, L₁.pr n → L₂.pr n)
(fn_inj : ∀ n, function.injective (fn n))
(pr_inj : ∀ n, function.injective (pr n))

infix ` ↝ᴸ `:25 := translation

protected def translation.refl : L ↝ᴸ L :=
{ fn := λ _, id,
  pr := λ _, id,
  fn_inj := λ _, function.injective_id,
  pr_inj := λ _, function.injective_id }

protected def translation.comp (τ₁ : L₁ ↝ᴸ L₂) (τ₂ : L₂ ↝ᴸ L₃) : L₁ ↝ᴸ L₃ :=
{ fn := λ n, τ₂.fn n ∘ τ₁.fn n,
  pr := λ n, τ₂.pr n ∘ τ₁.pr n,
  fn_inj := λ n, function.injective.comp (τ₂.fn_inj n) (τ₁.fn_inj n),
  pr_inj := λ n, function.injective.comp (τ₂.pr_inj n) (τ₁.pr_inj n) }

end language


end fol