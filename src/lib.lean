import tactic

universe u

inductive dvector (α : Type u) : ℕ → Type u
| nil {} : dvector 0
| cons   : ∀ {n}, α → dvector n → dvector (n+1)

notation a :: b  := dvector.cons a b

namespace dvector
variables {α : Type u}

@[simp] def unary (a : α) : dvector α 1 := a :: nil

@[simp] def extract : dvector α 1 → α
| (a :: nil) := a

@[simp] lemma extract_nil : ∀ (v : dvector α 1), v.extract :: nil = v
| (a :: nil) := rfl

@[simp] protected def append : ∀ {n}, dvector α n → ∀ {m}, dvector α m → dvector α (m + n)
| _ nil      _ l := l
| _ (a :: l) _ k := a :: (append l k)


end dvector