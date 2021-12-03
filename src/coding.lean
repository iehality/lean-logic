import deduction data.equiv.denumerable
import data.nat.sqrt
import data.set.lattice
open encodable denumerable 

universes u

namespace fopl
variables {L : language.{u}} [∀ n, encodable (L.fn n)] [∀ n, encodable (L.pr n)]

def term_encode : term L → ℕ
| (#x) := bit0 x
| (@term.app _ n f v) :=
    bit1 (nat.mkpair n (nat.mkpair (encode f) (encode (λ x, term_encode (v x)))))

-- TODO: これらを証明する
instance : primcodable (term L) := by sorry

instance : primcodable (formula L) := by sorry

variables {α : Type*} {β : Type*}
  [primcodable α] [primcodable β]

lemma primrec.term_rew {f : α → term L} {s : α → ℕ → term L}
  (hf : primrec f) (hs : primrec₂ s) :
  primrec (λ x, term.rew (s x) (f x)) := by sorry

lemma primrec.formula_rew {f : α → formula L} {s : α → ℕ → term L}
  (hf : primrec f) (hs : primrec₂ s) :
  primrec (λ x, formula.rew (s x) (f x)) := by sorry

end fopl