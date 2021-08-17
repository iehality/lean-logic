
import 
  computability.primrec
  computability.partrec
  computability.partrec_code
  computability.halting
  data.pfun
  deduction semantics cltheory arithmetic

open encodable denumerable roption

namespace fopl

namespace LC


inductive langf : ℕ → Type
| fn₁ : nat.partrec.code → langf 1
| pair : langf 2
notation `*fn₁` n := langf.fn₁ n
notation `*fn₂` n := langf.fn₂ n

inductive langp : ℕ → Type

end LC

def LC : language := ⟨LC.langf, LC.langp⟩

namespace LC
open nat.partrec

@[reducible] def symbol.fn₁ (c : nat.partrec.code) : term (LA + LC) → term (LA + LC) := λ x, vecterm.app (sum.inr (*fn₁ c)) x
prefix `Ḟ₁ `:max := symbol.fn₁

@[reducible] def symbol.pair : term (LA + LC) → term (LA + LC) → term (LA + LC) :=
λ x y, vecterm.app (sum.inr langf.pair) (x ::: y)

inductive computation : theory (LA + LC)
| zero : computation (∀̇ ((Ḟ₁ code.zero) #0 =̇ Ż))
| succ : computation (∀̇ ((Ḟ₁ code.succ) #0 =̇ Ṡ #0))
| pair : ∀ (c₁ c₂ : code), computation (∀̇ ((Ḟ₁ (code.pair c₁ c₂)) #0 =̇ symbol.pair (Ḟ₁ c₁ $ #0) (Ḟ₁ c₂ $ #0)))
| prec : 


notation `𝐐` := robinson

end LC

end fopl