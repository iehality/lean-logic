import QL.FOL.fol provability consistency

universes u v

namespace fol
open_locale logic_symbol
variables (L : language.{u}) {μ : Type v} {m m₁ m₂ n : ℕ}

namespace subterm
variables {L μ n}

section encode
variables (L n)

def label := ℕ ⊕ fin n ⊕ Σ n, L.fn n

def label_type : label L n → Type
| (sum.inl n)                := empty
| (sum.inr $ sum.inl n)      := empty
| (sum.inr $ sum.inr ⟨k, f⟩) := fin k

variables {L n}

@[reducible] def W_to_subterm : W_type (label_type L n) → subterm L ℕ n
| ⟨sum.inl x, _⟩                := &x
| ⟨sum.inr $ sum.inl x, _⟩      := #x
| ⟨sum.inr $ sum.inr ⟨k, f⟩, F⟩ := function f (λ x, W_to_subterm (F x))

def subterm_to_W : subterm L ℕ n → W_type (label_type L n)
| &x             := ⟨sum.inl x, empty.rec _⟩
| #x             := ⟨sum.inr $ sum.inl x, empty.rec _⟩
| (function f v) := ⟨sum.inr $ sum.inr ⟨_, f⟩, λ i, subterm_to_W (v i)⟩

def formula_equiv_W : subterm L ℕ n ≃ W_type (label_type L n) :=
{ to_fun := subterm_to_W,
  inv_fun := W_to_subterm,
  left_inv := by intros p; induction p; simp[subterm_to_W, W_to_subterm, *],
  right_inv := by { intros w, induction w with a f IH, rcases a with (_ | _ | ⟨k, f⟩),
    { simp[subterm_to_W, W_to_subterm, *], exact funext (by rintros ⟨⟩) },
    { rcases a, simp[subterm_to_W, W_to_subterm], exact funext (by rintros ⟨⟩) },
    { simp[subterm_to_W, W_to_subterm, IH] } } }

instance : Π i, fintype (label_type L n i)
| (sum.inl a)                := show fintype empty, from fintype.of_is_empty
| (sum.inr $ sum.inl x)      := show fintype empty, from fintype.of_is_empty
| (sum.inr $ sum.inr ⟨k, f⟩) := fin.fintype k

instance : Π i, encodable (label_type L n i)
| (sum.inl a)                := show encodable empty, from is_empty.to_encodable
| (sum.inr $ sum.inl x)      := show encodable empty, from is_empty.to_encodable
| (sum.inr $ sum.inr ⟨k, f⟩) := fin.encodable k

instance [∀ k, encodable (L.fn k)] : encodable (label L n) := sum.encodable

@[irreducible]
instance [∀ k, encodable (L.fn k)] : encodable (subterm L ℕ n) := encodable.of_equiv (W_type (label_type L n)) formula_equiv_W

--variables [encodable μ]

@[simp] def arity : subterm L ℕ n → ℕ
| &x             := x + 1
| #x             := 0
| (function f v) := ⨆ᶠ i, (v i).arity

@[simp] def to_bterm {m} : Π t : subterm L ℕ n, t.arity ≤ m → bounded_subterm L m n
| &x             h := &⟨x, h⟩
| #x             h := #x
| (function f v) h := function f (λ i, (v i).to_bterm (by simp at h; refine h i))

def uniform : bounded_subterm L m n → subterm L ℕ n := map coe

def to_nat [∀ k, encodable (L.fn k)] : bounded_subterm L m n → ℕ := λ t, encodable.encode t.uniform

@[simp] lemma map_val_mlift (t : bounded_subterm L m n) : t.mlift.uniform = t.uniform :=
by simp[uniform, mlift, (∘)]

@[simp] lemma uniform_cast_le (h : m₁ ≤ m₂) (t : bounded_subterm L m₁ n) : (cast_le h t).uniform = t.uniform :=
by simp[cast_le, uniform, (∘)]

@[simp] lemma uniform_to_bform (t : bounded_subterm L m n) (h) : t.uniform.to_bterm h = t :=
by induction t; simp[uniform, *]; case function : k f v IH { funext i, simp[uniform] at h, exact IH i (h i) }

@[simp] lemma to_subterm_uniform (t : subterm L ℕ n) (h : t.arity ≤ m) : (t.to_bterm h).uniform = t :=
by induction t; simp[uniform, *]; case function : k f v IH { funext i, simp[uniform] at h, exact IH i (h i) }

@[simp] lemma subterm_arity (t : bounded_subterm L m n) : t.uniform.arity ≤ m :=
by { induction t; simp[*, uniform], case metavar : i { exact nat.succ_le_iff.mpr i.property },
     case function : k f v IH { simpa using IH } }

@[simp] lemma uniform_push (t : bounded_subterm L m (n + 1)) :
  (push t).uniform = subst &m t.uniform :=
by { induction t; simp[*, uniform],
     case var : x { refine fin.last_cases _ _ x; simp },
     case function : k f v IH { funext i, exact IH i } }

variables (L m n) [∀ k, encodable (L.fn k)]

def of_nat : ℕ → option (bounded_subterm L m n) := λ i,
  (encodable.decode (subterm L ℕ n) i).bind (λ t, if h : t.arity ≤ m then some (t.to_bterm h) else none)

variables {L m m₁ m₂ n}

@[simp] lemma to_nat_of_nat (t : bounded_subterm L m n) : of_nat L m n t.to_nat = some t :=
by simp[to_nat, of_nat]

@[simp] lemma of_nat_mlift (t : bounded_subterm L m n) : to_nat t.mlift = to_nat t :=
by simp[to_nat]

@[simp] lemma of_nat_cast_le (h : m₁ ≤ m₂) (t : bounded_subterm L m₁ n) : to_nat (cast_le h t) = to_nat t :=
by simp[to_nat]

@[simp] lemma to_nat_to_subterm (t : subterm L ℕ n) {m} (h : t.arity ≤ m) :
  (t.to_bterm h).to_nat = encodable.encode t :=
by simp[subterm.to_nat]

end encode

end subterm

end fol