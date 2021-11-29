import deduction data.equiv.denumerable
import data.nat.sqrt
import data.set.lattice
open encodable denumerable 

universes u

#eval nat.unpair 1

#check nat.div_le_self
namespace nat

theorem unpair_lt2 {n : ℕ} (n1 : 1 < n) : (nat.unpair n).2 < n :=
let s := nat.sqrt n in begin
  simp [nat.unpair], change nat.sqrt n with s,
  by_cases h : n - s * s < s; simp [h],
  { refine nat.sqrt_lt_self n1 },
  { have : 1 ≤ s, simp[nat.le_sqrt'], exact le_of_lt n1,
    have : 0 < s * s, exact one_le_mul this this,
    have lmm₁ : n - s * s < n, refine nat.sub_lt (pos_of_gt n1) this,
    have lmm₂ : n - s * s - s ≤ n - s * s, exact (n - s * s).sub_le s,
    exact lt_of_le_of_lt lmm₂ lmm₁ }
end

lemma div2_lt (n : ℕ) : (n + 1).div2 < (n + 1) :=
by { simp[nat.div2_val], exact div_lt_self' n 0 }  

end nat


namespace fopl
variables {L : language.{u}} [∀ n, encodable (L.fn n)] [∀ n, encodable (L.pr n)]
/- 
inductive term (L : language.{u}) : Type u
| var {} : ℕ → term
| app    : ∀ {n : ℕ}, L.fn n → (fin n → term) → term

-/


def term.encode : term L → ℕ
| (#x) := bit0 x
| (@term.app _ n r v) := nat.mkpair (encode r) (encode (λ x, term.encode (v x)))



def vecterm.encode : ∀ {n}, vecterm L n → ℕ
| _ (vecterm.cons a v)     := (a.encode.mkpair v.encode)
| _ #0                     := 0
| _ #1                     := 1
| _ #(n+2)                 := (bit0 n) + 2
| _ (vecterm.const c)      := (bit1 $ bit0 (encode c)) + 2
| _ (@vecterm.app _ n f v) := (bit1 $ bit1 $ n.mkpair ((encode f).mkpair v.encode)) + 2

@[simp] def iterate0  (L) : ∀ n, vecterm L n
| 0     := #0
| (n+1) := vecterm.cons #0 (iterate0 n)

@[simp] def iterate01  (L) : ∀ n, vecterm L n
| 0     := #1
| (n+1) := vecterm.cons #0 (iterate01 n)

def vecterm.decode (L : language.{u}) [∀ n, encodable (L.fn n)] : ℕ → ∀ n, option (vecterm L n)
| 0     n     := iterate0 L n
| 1     n     := iterate01 L n
| (e+2) 0     :=
    have div2222 : e.div2.div2.unpair.2.unpair.2 ≤ e :=
    by { simp[nat.div2_val], 
         refine (le_trans _ (le_trans (nat.div_le_self (e/2) 2) (nat.div_le_self e 2))), 
         refine le_trans (nat.unpair_right_le _) (nat.unpair_right_le _) },
    have e.div2.div2.unpair.2.unpair.2 < e + 2 :=  nat.lt_succ_iff.mpr (le_add_right div2222),
    match e.bodd, e.div2.bodd with
    | ff, _  := some (#(e.div2+2))
    | tt, ff := (decode (L.fn 0) (e.div2.div2)).map vecterm.const
    | tt, tt := do
        f ← decode (L.fn (e.div2.div2.unpair.1 + 1)) e.div2.div2.unpair.2.unpair.1,
        v ← vecterm.decode (e.div2.div2.unpair.2.unpair.2) e.div2.div2.unpair.1,
      vecterm.app f v
    end
| (e+2) (n+1) := 
  have (e+2).unpair.1 < e + 2 := nat.unpair_lt (sup_eq_left.mp rfl),
  have (e+2).unpair.2 < e + 2 := nat.unpair_lt2 ((cmp_eq_lt_iff 1 (e + 2)).mp rfl),
  do a ← vecterm.decode ((e+2).unpair.1) 0,
     v ← vecterm.decode ((e+2).unpair.2) n,
    vecterm.cons a v

@[simp] private lemma iterate0_encode : ∀ n, vecterm.encode (iterate0 L n) = 0
| 0     := rfl
| (n+1) := by {simp[iterate0, vecterm.encode, iterate0_encode n], refl }

@[simp] private lemma iterate01_encode : ∀ n, vecterm.encode (iterate01 L n) = 1
| 0     := rfl
| (n+1) := by {simp[iterate01, vecterm.encode, iterate01_encode n], refl }

private lemma encode0_eq : ∀ {n} {v : vecterm L n}, v.encode = 0 → v = iterate0 L n
| _ (vecterm.cons a v) e :=
  by { simp[vecterm.encode, nat.mkpair_eq_iff] at e ⊢, simp[encode0_eq e.1, encode0_eq e.2] }
| _ #0     _ := by simp
| _ #1     e := by { simp[vecterm.encode] at e ⊢, exact e } 
| _ #(n+2) e := by { simp[vecterm.encode] at e ⊢, exact e } 
| _ (vecterm.const c) e := by { simp[vecterm.encode] at e ⊢, exact e }
| _ (@vecterm.app _ n f v) e := by { simp[vecterm.encode] at e ⊢, exact e }

private lemma encode1_eq : ∀ {n} {v : vecterm L n}, v.encode = 1 → v = iterate01 L n
| _ (vecterm.cons a v) e :=
  by { simp[vecterm.encode, nat.mkpair_eq_iff] at e ⊢, simp[encode0_eq e.1, encode1_eq e.2] }
| _ #0     e := by { simp[vecterm.encode] at e ⊢, exact e  }
| _ #1     e := by simp 
| _ #(n+2) e := by { simp[vecterm.encode] at e ⊢, exact e } 
| _ (vecterm.const c) e := by { simp[vecterm.encode] at e ⊢, exact e }
| _ (@vecterm.app _ n f v) e := by { simp[vecterm.encode] at e ⊢, exact e }

private lemma vecterm.decode_encode : ∀ {n} (t : vecterm L n), vecterm.decode L (vecterm.encode t) n = some t
| (n+1) (vecterm.cons a v) := by {
  simp[vecterm.decode, vecterm.encode],
  cases C₁ : a.encode.mkpair v.encode with m,
  { simp[vecterm.decode, iterate0, nat.mkpair_eq_iff] at C₁ ⊢, simp[encode0_eq C₁.1, encode0_eq C₁.2], refl },
  cases m,
  { simp[vecterm.decode, iterate01, nat.mkpair_eq_iff] at C₁ ⊢, simp[encode0_eq C₁.1, encode1_eq C₁.2], refl },
  { simp[vecterm.decode, iterate01, nat.mkpair_eq_iff, show m + 2 = a.encode.mkpair v.encode, by simp[C₁]],
    refine ⟨a, _, v, _⟩; simp[vecterm.decode_encode a, vecterm.decode_encode v], refl } }
| _ #0                     := by simp[vecterm.decode, vecterm.encode, iterate0]; refl
| _ #1                     := by simp[vecterm.decode, vecterm.encode, iterate01]; refl
| _ #(n+2)                 := by simp[vecterm.decode, vecterm.encode]
| _ (vecterm.const c)      := by simp[vecterm.decode, vecterm.encode]
| _ (@vecterm.app _ n f v) := by { simp[vecterm.decode, vecterm.encode, vecterm.decode_encode v],
  rw [nat.div2_bit1, nat.div2_bit1, nat.unpair_mkpair], simp*, refl }

instance (n) : encodable (vecterm L n) :=
⟨vecterm.encode, (λ e, vecterm.decode L e n), vecterm.decode_encode⟩

instance : encodable (term L) := ⟨vecterm.encode, (λ e, vecterm.decode L e 0), vecterm.decode_encode⟩

def formula.encode : formula L → ℕ
| (formula.const c)      := (bit0 $ bit0 (encode c))
| (@formula.app _ n p v) := (bit0 $ bit1 n.mkpair ((encode p).mkpair v.encode))
| (t ≃ u)                := (bit1 $ bit0 $ bit0 (t.encode.mkpair u.encode))
| (p ⟶ q)               := (bit1 $ bit0 $ bit1 (p.encode.mkpair q.encode))
| (⁻p)                   := (bit1 $ bit1 $ bit0 p.encode)
| (∏ p)                  := (bit1 $ bit1 $ bit1 p.encode)

def of_nat_form (L : language.{u}) [∀ n, encodable (L.fn n)] [∀ n, encodable (L.pr n)] : ℕ → option (formula L)
| 0     := (decode _ 0).map formula.const
| (e+1) := 

def of_nat_form (L : language.{u}) [∀ n, encodable (L.fn n)] [∀ n, encodable (L.pr n)] : ℕ → option (formula L)
| e :=
  match e.bodd, e.div2.bodd, e.div2.div2.bodd with
  | ff, ff, _  := (decode _ e.div2.div2).map formula.const
  | ff, tt, _  := formula.app <$> (decode (L.pr $ e.div2.div2.unpair.1 + 1) e.div2.div2.unpair.2.unpair.1) <*>
      (decode (vecterm L _) e.div2.div2.unpair.2.unpair.2)
  | tt, ff, ff := (≃) <$> (decode (vecterm L 0) e.div2.div2.div2.unpair.1) <*> (decode (vecterm L 0) e.div2.div2.div2.unpair.2)
  | tt, ff, tt := (⟶) <$> (of_nat_form e.div2.div2.div2.unpair.1) <*> (of_nat_form e.div2.div2.div2.unpair.2)
  | tt, tt, ff := (of_nat_form e.div2.div2.div2) >>= (λ p, ⁻p)
  | tt, tt, tt := (of_nat_form e.div2.div2.div2) >>= (λ p, ∏ p)
  end
  using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x+1)⟩]}

end fopl