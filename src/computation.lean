
import 
  computability.primrec
  computability.partrec
  computability.partrec_code
  computability.halting
  data.pfun
  deduction semantics cltheory

open encodable denumerable roption

namespace fopl

namespace LC
inductive langf : ℕ → Type
| fn₁ : ℕ → langf 1
| fn₂ : ℕ → langf 2
notation `*fn₁` n := langf.fn₁ n
notation `*fn₂` n := langf.fn₂ n

inductive langp : ℕ → Type

end LC

def LC : language := ⟨LC.langf, LC.langp⟩

namespace LC

@[reducible] def symbol.fn₁ (n : ℕ) : term LC → term LC := λ x, vecterm.app (*fn₁ n) x
prefix `Ṡ `:max := symbol.fn₁

end LC

end fopl