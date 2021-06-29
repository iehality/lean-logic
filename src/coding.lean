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
variables {L : language.{u}} [∀ n, denumerable (L.fn n)] [∀ n, denumerable (L.pr n)]
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

def vecterm.encode : ∀ {n}, vecterm L n → ℕ
| _ (vecterm.cons a v)     := (a.encode.mkpair v.encode)
| _ #0                     := 0
| _ #1                     := 1
| _ #(n+2)                   := (bit0 n) + 2
| _ (vecterm.const c)      := (bit1 $ bit0 (encode c)) + 2
| _ (@vecterm.app _ n f v) := (bit1 $ bit1 $ n.mkpair ((encode f).mkpair v.encode)) + 2

def iterate0  (L) : ∀ n, vecterm L n
| 0     := #0
| (n+1) := vecterm.cons #0 (iterate0 n)

def iterate01  (L) : ∀ n, vecterm L n
| 0     := #1
| (n+1) := vecterm.cons #0 (iterate01 n)

def of_nat_vecterm (L : language.{u}) [∀ n, denumerable (L.fn n)] : ℕ → ∀ n, vecterm L n
| 0     n     := iterate0 L n
| 1     n     := iterate01 L n
| (e+2) 0     :=
    have div2222 : e.div2.div2.unpair.2.unpair.2 ≤ e :=
    by { simp[nat.div2_val], 
         refine (le_trans _ (le_trans (nat.div_le_self (e/2) 2) (nat.div_le_self e 2))), 
         refine le_trans (nat.unpair_right_le _) (nat.unpair_right_le _) },
    have e.div2.div2.unpair.2.unpair.2 < e + 2 :=  nat.lt_succ_iff.mpr (le_add_right div2222),
    match e.bodd, e.div2.bodd with
    | ff, _  := #(e.div2+2)
    | tt, ff := vecterm.const (of_nat (L.fn 0) (e.div2.div2))
    | tt, tt := vecterm.app (of_nat (L.fn (e.div2.div2.unpair.1 + 1)) e.div2.div2.unpair.2.unpair.1)
      (of_nat_vecterm (e.div2.div2.unpair.2.unpair.2) e.div2.div2.unpair.1)
    end
| (e+2) (n+1) := 
  have (e+2).unpair.1 < e + 2 := nat.unpair_lt (sup_eq_left.mp rfl),
  have (e+2).unpair.2 < e + 2 := nat.unpair_lt2 ((cmp_eq_lt_iff 1 (e + 2)).mp rfl),
    vecterm.cons (of_nat_vecterm ((e+2).unpair.1) 0) (of_nat_vecterm ((e+2).unpair.2) n) 
using_well_founded { rel_tac := λ _ _, `[exact ⟨_, measure_wf psigma.fst⟩]  }


@[simp] private lemma iterate0_encode : ∀ n, vecterm.encode (iterate0 L n) = 0
| 0     := rfl
| (n+1) := by {simp[iterate0, vecterm.encode, iterate0_encode n], refl }

@[simp] private lemma iterate01_encode : ∀ n, vecterm.encode (iterate01 L n) = 1
| 0     := rfl
| (n+1) := by {simp[iterate01, vecterm.encode, iterate01_encode n], refl }

private lemma encode_of_nat_vecterm : ∀ e n : ℕ, vecterm.encode (of_nat_vecterm L e n) = e
| 0     n     := by simp[of_nat_vecterm, vecterm.encode, iterate0_encode]
| 1     n     := by simp[of_nat_vecterm, vecterm.encode, iterate01_encode]
| (e+2) 0     := 
    have div2222 : e.div2.div2.unpair.2.unpair.2 ≤ e :=
    by { simp[nat.div2_val], 
         refine (le_trans _ (le_trans (nat.div_le_self (e/2) 2) (nat.div_le_self e 2))), 
         refine le_trans (nat.unpair_right_le _) (nat.unpair_right_le _) },
    have e.div2.div2.unpair.2.unpair.2 < e + 2 :=  nat.lt_succ_iff.mpr (le_add_right div2222),
    have IH : _ := encode_of_nat_vecterm e.div2.div2.unpair.2.unpair.2,
    by { suffices : (of_nat_vecterm L (e + 2) 0).encode = nat.bit e.bodd e.div2 + 2,
         { simp[nat.bit_decomp, this] },
         cases C₁ : e.bodd,
         { simp [of_nat_vecterm, vecterm.encode, nat.bit, C₁] },
         suffices : (of_nat_vecterm L (e + 2) 0).encode = nat.bit tt (nat.bit e.div2.bodd e.div2.div2) + 2,
         { simp[nat.bit_decomp, this] },
         cases C₂ : e.div2.bodd; simp [of_nat_vecterm, vecterm.encode, nat.bit, C₁, C₂, IH, bit1] }
| (e+2) (n+1) :=
    have (e+2).unpair.1 < e + 2 := nat.unpair_lt (sup_eq_left.mp rfl),
    have (e+2).unpair.2 < e + 2 := nat.unpair_lt2 ((cmp_eq_lt_iff 1 (e + 2)).mp rfl),
    have IH₁ : _ := encode_of_nat_vecterm (e+2).unpair.1,
    have IH₂ : _ := encode_of_nat_vecterm (e+2).unpair.2,
  by { simp [of_nat_vecterm, vecterm.encode, IH₁, IH₂] }

private lemma of_nat_vecterm_encode : ∀ {n} (t : vecterm L n), of_nat_vecterm L (vecterm.encode t) n = t
| (n+1) (vecterm.cons a v)     := by {
    simp[of_nat_vecterm, vecterm.encode],
    cases C₁ : a.encode.mkpair v.encode, simp[of_nat_vecterm, iterate0], simp at C₁,
    have := of_nat_vecterm_encode v, }
| _ #0                     := by simp[of_nat_vecterm, vecterm.encode, iterate0]
| _ #1                     := by simp[of_nat_vecterm, vecterm.encode, iterate01]
| _ #(n+2)                 := by simp[of_nat_vecterm, vecterm.encode]
| _ (vecterm.const c)      := by simp[of_nat_vecterm, vecterm.encode]
| _ (@vecterm.app _ n f v) := by { simp[of_nat_vecterm, vecterm.encode, of_nat_vecterm_encode v],
      rw [nat.div2_bit1, nat.div2_bit1, nat.unpair_mkpair], simp* }

instance (n) : denumerable (vecterm L n) :=
mk' ⟨vecterm.encode, (λ e, of_nat_vecterm L e n),
     of_nat_vecterm_encode,
     (λ e, encode_of_nat_vecterm e n)⟩

def form.encode : form L → ℕ
| (form.const c)      := (bit0 $ bit0 (encode c))
| (@form.app _ n p v) := (bit0 $ bit1 n.mkpair ((encode p).mkpair v.encode))
| (t =̇ u)             := (bit1 $ bit0 $ bit0 (t.encode.mkpair u.encode))
| (p →̇ q)            := (bit1 $ bit0 $ bit1 (p.encode.mkpair q.encode))
| (¬̇p)                := (bit1 $ bit1 $ bit0 p.encode)
| (Ȧp)                := (bit1 $ bit1 $ bit1 p.encode)

def of_nat_form (L : language.{u}) [∀ n, denumerable (L.fn n)] [∀ n, denumerable (L.pr n)] : ℕ → form L
| e :=
  match e.bodd, e.div2.bodd, e.div2.div2.bodd with
  | ff, ff, _  := form.const (of_nat _ e.div2.div2)
  | ff, tt, _  := form.app (of_nat (L.pr $ e.div2.div2.unpair.1 + 1) e.div2.div2.unpair.2.unpair.1)
      (of_nat (vecterm L _) e.div2.div2.unpair.2.unpair.2)
  | tt, ff, ff := (of_nat (vecterm L 1) e.div2.div2.div2.unpair.1) =̇ (of_nat (vecterm L 1) e.div2.div2.div2.unpair.2)
  | tt, ff, tt := (of_nat_form e.div2.div2.div2.unpair.1) →̇ (of_nat_form e.div2.div2.div2.unpair.2)
  | tt, tt, ff := ¬̇(of_nat_form e.div2.div2.div2)
  | tt, tt, tt := Ȧ(of_nat_form e.div2.div2.div2)
  end

end fopl