import QL.FOL.Tait.tait provability consistency

universes u v

namespace fol
open_locale logic_symbol
variables {L : language.{u}} {m n : ℕ}

namespace Tait

namespace subformula

section encode
variables (L m n)

def label :=
  unit ⊕ unit ⊕
  (Σ k, L.pr k × (fin k → subterm L m n)) ⊕ (Σ k, L.pr k × (fin k → subterm L m n)) ⊕
  unit ⊕ unit ⊕
  unit ⊕ unit

def arity : label L m n → Type
| (sum.inl _)                                                             := empty
| (sum.inr $ sum.inl _)                                                   := empty
| (sum.inr $ sum.inr $ sum.inl _)                                         := empty
| (sum.inr $ sum.inr $ sum.inr $ sum.inl _)                               := empty
| (sum.inr $ sum.inr $ sum.inr $ sum.inr $ sum.inl _)                     := bool
| (sum.inr $ sum.inr $ sum.inr $ sum.inr $ sum.inr $ sum.inl _)           := bool
| (sum.inr $ sum.inr $ sum.inr $ sum.inr $ sum.inr $ sum.inr $ sum.inl _) := unit
| (sum.inr $ sum.inr $ sum.inr $ sum.inr $ sum.inr $ sum.inr $ sum.inr _) := unit

variables {L m n}

@[reducible] def W_to_subformula : W_type (arity L m n) → subformula L m n
| ⟨sum.inl x, _⟩                := ⊤
| ⟨sum.inr $ sum.inl ⟨k, r, v⟩, _⟩ := relation r v
| ⟨sum.inr $ sum.inr $ sum.inl _, F⟩ := (W_to_subformula (F ff)) ⟶ (W_to_subformula (F tt))
| ⟨sum.inr $ sum.inr $ sum.inr $ sum.inl _, F⟩ := ∼W_to_subformula (F ())
| ⟨sum.inr $ sum.inr $ sum.inr $ sum.inr _, F⟩ := by {  }

#check Tait.subformula

def subformula_to_W : (Σ n, subformula L m n) → (Σ n, W_type (arity L m n))
| ⟨n, verum⟩            := ⟨n, sum.inl (), empty.rec _⟩
| ⟨n, falsum⟩           := ⟨n, sum.inr $ sum.inl (), empty.rec _⟩
| ⟨n, relation r v⟩     := ⟨n, sum.inr $ sum.inr $ sum.inl ⟨_, r, v⟩, empty.rec _⟩
| ⟨n, neg_relation r v⟩ := ⟨n, sum.inr $ sum.inr $ sum.inr $ sum.inl ⟨_, r, v⟩, empty.rec _⟩
| ⟨n, and p q⟩          := ⟨n, sum.inr $ sum.inr $ sum.inr $ sum.inr $ sum.inl (), λ b, bool.cases_on b (subformula_to_W p) (subformula_to_W q)⟩
| ⟨n, or p q⟩           := ⟨n, sum.inr $ sum.inr $ sum.inr $ sum.inr $ sum.inr $ sum.inl (), λ b, bool.cases_on b (subformula_to_W p) (subformula_to_W q)⟩
| ⟨n, fal p⟩            := ⟨n + 1, sum.inr $ sum.inr $ sum.inr $ sum.inr $ sum.inr $ sum.inr $ sum.inl (), λ _, subformula_to_W p⟩
| ⟨n, ex p⟩             := ⟨n + 1, sum.inr $ sum.inr $ sum.inr $ sum.inr $ sum.inr $ sum.inr $ sum.inr (), λ _, subformula_to_W p⟩
--using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.complexity)⟩]}



end encode

end subformula

end Tait
end fol