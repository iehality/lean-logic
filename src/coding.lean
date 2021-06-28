import deduction data.equiv.denumerable
universes u
namespace fopl
variables {L : language.{u}}
/- inductive vecterm (L : language.{u}) : ℕ → Type u
| nil {} : vecterm 0
| cons   : ∀ {n : ℕ}, vecterm 1 → vecterm n → vecterm (n+1)
| var {} : ℕ → vecterm 1
| app    : ∀ {n : ℕ}, L.fn n → vecterm n → vecterm 1 -/

--def vecterm.encode [∀ n, denumerable (L.fn n)] : ∀ {n}, vecterm L n → ℕ
--| _ vecterm.nil        := 0
--| _ (vecterm.cons a v) := (bit0 $ bit0 $ nat.mkpair a.encode v.encode) + 1
--| _ (#n)               := (bit0 $ bit1 n) + 1
--| _ (vecterm.app f v)  := (bit1 $ nat.mkpair (encodable.encode f) v.encode) + 1

def term.encode [∀ n, denumerable (L.fn n)] : term L → ℕ
| (vecterm.cons a vecterm.nil) := term.encode a
| (#n)                         := (bit0 $ bit1 n) + 1
| (vecterm.app f v)            := 1

def of_nat_vecterm [∀ n, denumerable (L.fn n)] : ℕ → ∀ {n}, 

end fopl