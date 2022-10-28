import PL.deduction

universes u

namespace pl
open_locale logic_symbol
open formula logic
variables (A : Type u)

structure Structure := (val : A → bool)

variables {A} (S : Structure A)

@[simp] def formula.val : formula A → bool
| (atom a) := S.val a
| ⊤        := true
| (p ⟶ q) := bnot p.val || q.val
| (⁻p)     := bnot p.val

instance : semantics (formula A) (Structure A) := ⟨λ S p, p.val S⟩

lemma models_def (S : Structure A) (p : formula A) : S ⊧ p ↔ p.val S = tt :=
by refl 

variables {T : theory A} {p : formula A}

lemma soundness (b : T ⊢ p) : T ⊧[Structure A] p :=
begin
  apply rec'_on b,
  { intros p q hpq hp IHpq IHp S h, 
    have l₁ : p.val S = ff ∨ q.val S = tt, by simpa[models_def] using IHpq h,
    have l₂ : p.val S = tt, by simpa[models_def] using IHp h,
    simpa[l₂, models_def] using l₁ },
  { intros p hp S h, exact h hp },
  { intros S hS, simp[models_def] },
  { intros p q S hS, simp[models_def], cases p.val S; simp },
  { intros p q r S hS, simp[models_def], cases p.val S; cases q.val S; cases r.val S; simp },
  { intros p q S hS, simp[models_def], cases p.val S; cases q.val S; simp }
end

end pl