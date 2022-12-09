import QL.FOL.uniform provability consistency

universes u v

namespace fol
open_locale logic_symbol
variables (L : language.{u}) {m n : ℕ}

namespace uniform_subterm
variables {L n}

section encode
variables (L n)

def label := ℕ ⊕ fin n ⊕ Σ n, L.fn n

def label_type : label L n → Type
| (sum.inl n)                := empty
| (sum.inr $ sum.inl n)      := empty
| (sum.inr $ sum.inr ⟨k, f⟩) := fin k

variables {L n}

@[reducible] def W_to_subterm : W_type (label_type L n) → uniform_subterm L n
| ⟨sum.inl x, _⟩                := uvar x
| ⟨sum.inr $ sum.inl x, _⟩      := var x
| ⟨sum.inr $ sum.inr ⟨k, f⟩, F⟩ := function f (λ x, W_to_subterm (F x))

def subterm_to_W : uniform_subterm L n → W_type (label_type L n)
| &&x       := ⟨sum.inl x, empty.rec _⟩
| (var x)        := ⟨sum.inr $ sum.inl x, empty.rec _⟩
| (function f v) := ⟨sum.inr $ sum.inr ⟨_, f⟩, λ i, subterm_to_W (v i)⟩

def formula_equiv_W : uniform_subterm L n ≃ W_type (label_type L n) :=
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

variables [∀ k, encodable (L.fn k)]

instance : encodable (label L n) := sum.encodable

@[irreducible]
instance : encodable (uniform_subterm L n) := encodable.of_equiv (W_type (label_type L n)) formula_equiv_W

end encode

end uniform_subterm

namespace subterm
open uniform_subterm
variables {L m n}

section encode

variables [∀ k, encodable (L.fn k)]

def to_nat : subterm L m n → ℕ := λ t, encodable.encode t.uniform

variables (L m n)

def of_nat : ℕ → option (subterm L m n) := λ i,
  let t := encodable.decode (uniform_subterm L n) i in
  t.bind (λ t, if h : t.arity ≤ m then some (t.to_subterm h) else none)

variables {L m n}

@[simp] lemma to_nat_of_nat (t : subterm L m n) : of_nat L m n t.to_nat = some t :=
by simp[to_nat, of_nat]

@[simp] lemma of_nat_to_nat (t : subterm L m n) : to_nat t.mlift = to_nat t :=
by simp[to_nat]

end encode

end subterm

namespace uniform_subterm
variables {L n} [∀ k, encodable (L.fn k)]

@[simp] lemma to_nat_to_subterm (t : uniform_subterm L n) {m} (h : t.arity ≤ m) :
  (t.to_subterm h).to_nat = encodable.encode t :=
by simp[subterm.to_nat]

end uniform_subterm

namespace uniform_subformula
variables {L n}

section encode
open encodable nat
variables {L n} [∀ k, encodable (L.pr k)] [∀ k, encodable (L.fn k)]

@[simp] def to_nat : Π {n}, uniform_subformula L n → ℕ
| n verum                 := 0
| n (@relation L _ k r v) := (bit0 $ bit0 $ mkpair k $ mkpair (encode r) (encode v)) + 1
| n (imply p q)           := (bit0 $ bit1 $ mkpair p.to_nat q.to_nat) + 1
| n (neg p)               := (bit1 $ bit0 p.to_nat) + 1
| n (fal p)               := (bit1 $ bit1 p.to_nat) + 1

variables (L n)

@[simp] def of_nat : Π n, ℕ → option (uniform_subformula L n)
| n 0 := some verum
| n (e + 1) :=
    let i := e.div2.div2 in
    have div8 : i ≤ e := by simp[i, nat.div2_val]; exact le_trans (nat.div_le_self (e/2) 2) (nat.div_le_self e 2),
    have hi : i < e + 1, from lt_succ_iff.mpr div8,
    have hi1 : i.unpair.1 < e + 1, from nat.lt_succ_iff.mpr (le_trans (nat.unpair_left_le _) div8),
    have hi2 : i.unpair.2 < e + 1, from nat.lt_succ_iff.mpr (le_trans (nat.unpair_right_le _) div8),
    match e.bodd, e.div2.bodd with
    | ff, ff :=
        let k := i.unpair.1,
            r := decode (L.pr k) i.unpair.2.unpair.1,
            v := decode (fin k → uniform_subterm L n) i.unpair.2.unpair.2 in
      r.bind (λ r, v.map (relation r))
    | ff, tt := (of_nat n i.unpair.1).bind (λ p, (of_nat n i.unpair.2).map (imply p))
    | tt, ff := (of_nat n i).map neg
    | tt, tt := (of_nat (n + 1) i).map fal
    end
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2)⟩]}

@[simp] lemma of_nat_to_nat : ∀ {n} (p : uniform_subformula L n), of_nat L n p.to_nat = some p
| n verum                 := by simp
| n (@relation L _ k r v) :=
    begin
      simp only [to_nat, of_nat, of_nat._match_1, nat.bodd_bit0, nat.div2_bit0, nat.unpair_mkpair, encodek],
      rw[show (unpair (mkpair k (mkpair (encode r) (encode v)))).fst = k, by simp],
      simp only [encodek, option.some_bind', option.map_some', heq.refl], simp
    end
| n (imply p q)           := by simp; refine ⟨of_nat_to_nat p, of_nat_to_nat q⟩
| n (neg p)               := by simp; refine (of_nat_to_nat p)
| n (fal p)               := by simp; refine (of_nat_to_nat p)

instance (n) : encodable (uniform_subformula L n) :=
{ encode := to_nat,
  decode := of_nat L n,
  encodek := by simp }

end encode

end uniform_subformula

namespace subformula
open uniform_subformula
variables {L m n}

section encode
variables [∀ k, encodable (L.fn k)] [∀ k, encodable (L.pr k)]

def to_nat : subformula L m n → ℕ := λ p, encodable.encode p.uniform

variables (L m n)

def of_nat : ℕ → option (subformula L m n) := λ i,
  let p := encodable.decode₂ (uniform_subformula L n) i in
  p.bind (λ p, if h : p.arity ≤ m then some (p.to_subformula h) else none)

variables {L m n}

@[simp] lemma subformula_arity (p : subformula L m n) : p.uniform.arity ≤ m :=
by induction p; simp*

@[simp] lemma to_nat_of_nat (p : subformula L m n) : of_nat L m n p.to_nat = some p :=
by simp[to_nat, of_nat]

lemma of_nat_eq_some {e} {p : subformula L m n} : of_nat L m n e = some p ↔ p.to_nat = e :=
by { simp[of_nat, to_nat, encodable.decode₂_eq_some, dite_eq_iff], split,
  { simp, rintros _ rfl h rfl, simp },
  { rintros rfl, refine ⟨p.uniform, rfl, by simp⟩ } }

@[simp] lemma of_nat_to_nat (p : subformula L m n) : to_nat p.mlift = to_nat p :=
by simp[to_nat]

end encode

end subformula

end fol