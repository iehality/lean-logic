
import fopl lindenbaum

universes u v

namespace sopl

variables (L : fopl.language.{u})
open fopl

inductive formula : Type u
| app   : ∀ {n : ℕ}, L.pr n → (fin n → term L) → formula
| mem   : ℕ → term L → formula 
| equal : term L → term L → formula
| imply : formula → formula → formula
| neg   : formula → formula
| fal   : formula → formula

end sopl





