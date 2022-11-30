import QL.FOL.fol provability consistency

universes u v

namespace fol
open_locale logic_symbol
variables {L : language.{u}} {m n : ℕ}

namespace subterm

section encode
variables (L m n)

def label := fin m ⊕ fin n ⊕ Σ n, L.fn n

def arity : label L m n → Type
| (sum.inl n)                := empty
| (sum.inr $ sum.inl n)      := empty
| (sum.inr $ sum.inr ⟨k, f⟩) := fin k

variables {L m n}

@[reducible] def W_to_subterm : W_type (arity L m n) → subterm L m n
| ⟨sum.inl x, _⟩                := &x
| ⟨sum.inr $ sum.inl x, _⟩      := #x
| ⟨sum.inr $ sum.inr ⟨k, f⟩, F⟩ := function f (λ x, W_to_subterm (F x))

def subterm_to_W : subterm L m n → W_type (arity L m n)
| &x             := ⟨sum.inl x, empty.rec _⟩
| #x             := ⟨sum.inr $ sum.inl x, empty.rec _⟩
| (function f v) := ⟨sum.inr $ sum.inr ⟨_, f⟩, λ i, subterm_to_W (v i)⟩

def formula_equiv_W : subterm L m n ≃ W_type (arity L m n) :=
{ to_fun := subterm_to_W,
  inv_fun := W_to_subterm,
  left_inv := by intros p; induction p; simp[subterm_to_W, W_to_subterm, *],
  right_inv := by { intros w, induction w with a f IH, rcases a with (_ | _ | ⟨k, f⟩),
    { simp[subterm_to_W, W_to_subterm, *], exact funext (by rintros ⟨⟩) },
    { rcases a, simp[subterm_to_W, W_to_subterm], exact funext (by rintros ⟨⟩) },
    { simp[subterm_to_W, W_to_subterm, IH] } } }

instance : Π i, fintype (arity L m n i)
| (sum.inl a)                := show fintype empty, from fintype.of_is_empty
| (sum.inr $ sum.inl x)      := show fintype empty, from fintype.of_is_empty
| (sum.inr $ sum.inr ⟨k, f⟩) := fin.fintype k

instance : Π i, encodable (arity L m n i)
| (sum.inl a)                := show encodable empty, from is_empty.to_encodable
| (sum.inr $ sum.inl x)      := show encodable empty, from is_empty.to_encodable
| (sum.inr $ sum.inr ⟨k, f⟩) := fin.encodable k

variables [∀ k, encodable (L.fn k)]

instance : encodable (label L m n) := sum.encodable

instance : encodable (subterm L m n) := encodable.of_equiv (W_type (arity L m n)) formula_equiv_W

instance : encodable (Σ m n, subterm L m n) := sigma.encodable

end encode

end subterm

end fol