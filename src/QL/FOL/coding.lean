import QL.FOL.fol provability consistency

universes u v

namespace fol
open_locale logic_symbol
variables (L : language.{u}) {m n : ℕ}

inductive uniform_subterm (n : ℕ) : Type u
| uvar  {} : ℕ → uniform_subterm
| var   {} : fin n → uniform_subterm
| function : ∀ {k}, L.fn k → (fin k → uniform_subterm) → uniform_subterm

inductive uniform_subformula : ℕ → Type u
| verum    {n} : uniform_subformula n
| relation {n} : ∀ {p}, L.pr p → (fin p → uniform_subterm L n) → uniform_subformula n
| imply    {n} : uniform_subformula n → uniform_subformula n → uniform_subformula n
| neg      {n} : uniform_subformula n → uniform_subformula n
| fal      {n} : uniform_subformula (n + 1) → uniform_subformula n

namespace uniform_subterm
variables {L n}

@[simp] def uvars : uniform_subterm L n → ℕ
| (uvar x)       := x + 1
| (var x)        := 0
| (function f v) := ⨆ᶠ i, (v i).uvars

@[simp] def to_subterm : ∀ t : uniform_subterm L n, t.uvars ≤ m → subterm L m n
| (uvar x)       h := &⟨x, h⟩
| (var x)        h := #x 
| (@function L n k f v) h := subterm.function f (λ i, to_subterm (v i) (by { haveI: inhabited (fin k) := ⟨i⟩, simp at h, exact h i}))

section encode
variables (L n)

def label := ℕ ⊕ fin n ⊕ Σ n, L.fn n

def arity : label L n → Type
| (sum.inl n)                := empty
| (sum.inr $ sum.inl n)      := empty
| (sum.inr $ sum.inr ⟨k, f⟩) := fin k

variables {L n}

@[reducible] def W_to_subterm : W_type (arity L n) → uniform_subterm L n
| ⟨sum.inl x, _⟩                := uvar x
| ⟨sum.inr $ sum.inl x, _⟩      := var x
| ⟨sum.inr $ sum.inr ⟨k, f⟩, F⟩ := function f (λ x, W_to_subterm (F x))

def subterm_to_W : uniform_subterm L n → W_type (arity L n)
| (uvar x)       := ⟨sum.inl x, empty.rec _⟩
| (var x)        := ⟨sum.inr $ sum.inl x, empty.rec _⟩
| (function f v) := ⟨sum.inr $ sum.inr ⟨_, f⟩, λ i, subterm_to_W (v i)⟩

def formula_equiv_W : uniform_subterm L n ≃ W_type (arity L n) :=
{ to_fun := subterm_to_W,
  inv_fun := W_to_subterm,
  left_inv := by intros p; induction p; simp[subterm_to_W, W_to_subterm, *],
  right_inv := by { intros w, induction w with a f IH, rcases a with (_ | _ | ⟨k, f⟩),
    { simp[subterm_to_W, W_to_subterm, *], exact funext (by rintros ⟨⟩) },
    { rcases a, simp[subterm_to_W, W_to_subterm], exact funext (by rintros ⟨⟩) },
    { simp[subterm_to_W, W_to_subterm, IH] } } }

instance : Π i, fintype (arity L n i)
| (sum.inl a)                := show fintype empty, from fintype.of_is_empty
| (sum.inr $ sum.inl x)      := show fintype empty, from fintype.of_is_empty
| (sum.inr $ sum.inr ⟨k, f⟩) := fin.fintype k

instance : Π i, encodable (arity L n i)
| (sum.inl a)                := show encodable empty, from is_empty.to_encodable
| (sum.inr $ sum.inl x)      := show encodable empty, from is_empty.to_encodable
| (sum.inr $ sum.inr ⟨k, f⟩) := fin.encodable k

variables [∀ k, encodable (L.fn k)]

instance : encodable (label L n) := sum.encodable

instance : encodable (uniform_subterm L n) := encodable.of_equiv (W_type (arity L n)) formula_equiv_W

end encode

end uniform_subterm

namespace subterm
open uniform_subterm
variables {L m n}

@[simp] def to_uniform : subterm L m n → uniform_subterm L n
| &x             := uniform_subterm.uvar x 
| #x             := uniform_subterm.var x 
| (function f v) := uniform_subterm.function f (λ i, (v i).to_uniform)

@[simp] lemma to_uniform_mlift (t : subterm L m n) : t.mlift.to_uniform = t.to_uniform :=
by induction t; simp*

@[simp] lemma to_uniform_to_subterm (t : subterm L m n) (h) : t.to_uniform.to_subterm h = t :=
by induction t; simp*

@[simp] lemma to_subterm_to_uniform (t : uniform_subterm L n) (h : t.uvars ≤ m) : (t.to_subterm h).to_uniform = t :=
by induction t; simp*

section encode

variables [∀ k, encodable (L.fn k)]

def to_nat : subterm L m n → ℕ := λ t, encodable.encode t.to_uniform

variables (L m n)

def of_nat : ℕ → option (subterm L m n) := λ i,
  let t := encodable.decode (uniform_subterm L n) i in
  t.bind (λ t, if h : t.uvars ≤ m then some (t.to_subterm h) else none)

variables {L m n}

@[simp] lemma subterm_uvars (t : subterm L m n) : t.to_uniform.uvars ≤ m :=
by { induction t; simp*, case metavar : i { exact nat.succ_le_iff.mpr i.property } }

@[simp] lemma to_nat_of_nat (t : subterm L m n) : of_nat L m n t.to_nat = some t :=
by simp[to_nat, of_nat]

@[simp] lemma of_nat_to_nat (t : subterm L m n) : to_nat t.mlift = to_nat t :=
by simp[to_nat]

end encode

end subterm

namespace uniform_subformula
variables {L n}

@[simp] def uvars : Π {n}, uniform_subformula L n → ℕ
| n verum          := 0
| n (relation r v) := ⨆ᶠ i, (v i).uvars
| n (imply p q)    := max p.uvars q.uvars
| n (neg p)        := p.uvars
| n (fal p)        := p.uvars

@[simp] def to_subformula : ∀ {n} (p : uniform_subformula L n), p.uvars ≤ m → subformula L m n
| n verum          h := ⊤
| n (relation r v) h := subformula.relation r (λ i, (v i).to_subterm (by show (v i).uvars ≤ m; simp at h; exact h i))
| n (imply p q)    h := have h : p.uvars ≤ m ∧ q.uvars ≤ m, by simpa using h, p.to_subformula h.1 ⟶ q.to_subformula h.2
| n (neg p)        h := ∼p.to_subformula (by simpa using h)
| n (fal p)        h := ∀'p.to_subformula (by simpa using h)

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

@[simp] def to_uniform : Π {n}, subformula L m n → uniform_subformula L n
| n verum          := uniform_subformula.verum
| n (relation r v) := uniform_subformula.relation r (subterm.to_uniform ∘ v)
| n (imply p q)    := uniform_subformula.imply p.to_uniform q.to_uniform
| n (neg p)        := uniform_subformula.neg p.to_uniform
| n (fal p)        := uniform_subformula.fal p.to_uniform

@[simp] lemma to_uniform_mlift (p : subformula L m n) : p.mlift.to_uniform = p.to_uniform :=
by simp[mlift]; induction p; simp[mlift', ←fal_eq, ←neg_eq, ←top_eq, ←imply_eq, (∘), *]

@[simp] lemma to_uniform_to_subterm (p : subformula L m n) (h) : p.to_uniform.to_subformula h = p :=
by induction p; simp*; refl

@[simp] lemma to_subterm_to_uniform (p : uniform_subformula L n) (h : p.uvars ≤ m) : (p.to_subformula h).to_uniform = p :=
by induction p; simp[←fal_eq, ←neg_eq, ←top_eq, ←imply_eq, (∘), *]

section encode

variables [∀ k, encodable (L.fn k)] [∀ k, encodable (L.pr k)]

def to_nat : subformula L m n → ℕ := λ p, encodable.encode p.to_uniform

variables (L m n)

def of_nat : ℕ → option (subformula L m n) := λ i,
  let p := encodable.decode (uniform_subformula L n) i in
  p.bind (λ p, if h : p.uvars ≤ m then some (p.to_subformula h) else none)

variables {L m n}

@[simp] lemma subformula_uvars (p : subformula L m n) : p.to_uniform.uvars ≤ m :=
by induction p; simp*

@[simp] lemma to_nat_of_nat (p : subformula L m n) : of_nat L m n p.to_nat = some p :=
by simp[to_nat, of_nat]

@[simp] lemma of_nat_to_nat (p : subformula L m n) : to_nat p.mlift = to_nat p :=
by simp[to_nat]

end encode

end subformula

end fol