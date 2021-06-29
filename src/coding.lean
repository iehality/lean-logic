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
variables {L : language.{u}} [∀ n, denumerable (L.fn n)]
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
| _ #(n)                   := (bit0 n)
| _ (vecterm.const c)      := (bit1 $ bit0 (encode c))
| _ (@vecterm.app _ n f v) := (bit1 $ bit1 $ n.mkpair ((encode f).mkpair v.encode))

def iterate0  (L) : ∀ n, vecterm L n
| 0     := #0
| (n+1) := vecterm.cons #0 (iterate0 n)



def of_nat_vecterm (L : language.{u}) [∀ n, denumerable (L.fn n)] : ℕ → ∀ n, vecterm L n
| 0     n     := iterate0 L n
| (e+1) 0     :=
  have (cond e.bodd e.div2.succ e.div2).div2.unpair.2.unpair.2 < e + 1 := 
  by { suffices : (e+1).div2.div2.unpair.2.unpair.2 < e + 1, { simp* at* },
       refine lt_of_le_of_lt (le_trans (nat.unpair_right_le _) $ le_trans (nat.unpair_right_le _) _) (nat.div2_lt e),
       simp[nat.div2_val], refine nat.div_le_self _ _ },
  match e.bodd, (e + 1).div2.bodd with
  | tt, _  := #((e+1).div2)
  | ff, ff := vecterm.const (of_nat (L.fn 0) ((e + 1).div2.div2))
  | ff, tt := vecterm.app (of_nat (L.fn ((e + 1).div2.div2.unpair.1 + 1)) (e+ 1).div2.div2.unpair.2.unpair.1)
    (of_nat_vecterm ((e + 1).div2.div2.unpair.2.unpair.2) (e + 1).div2.div2.unpair.1)
  end
| 1     (n+1) := vecterm.cons #0 
| (e+1) (n+1) := 
  have e.unpair.1 < e + 1 := nat.lt_succ_iff.mpr (nat.unpair_left_le _),
  have e.unpair.2 < e + 1 := nat.lt_succ_iff.mpr (nat.unpair_right_le _),
    vecterm.cons (of_nat_vecterm (e.unpair.1) 0) (of_nat_vecterm (e.unpair.2) n) 
using_well_founded { rel_tac := λ _ _, `[exact ⟨_, measure_wf psigma.fst⟩]  }

private lemma iterate0_encode : ∀ n, vecterm.encode (iterate0 L n) = 0
| 0     := rfl
| (n+1) := by {simp[iterate0, vecterm.encode, iterate0_encode n], refl }

private lemma encode_of_nat_vecterm : ∀ e n : ℕ, vecterm.encode (of_nat_vecterm L e n) = e
| 0     n     := by simp[of_nat_vecterm, vecterm.encode, iterate0_encode]
| (e+1) 0     := 
  have (cond e.bodd e.div2.succ e.div2).div2.unpair.2.unpair.2 < e + 1 := 
  by { suffices : (e+1).div2.div2.unpair.2.unpair.2 < e + 1, { simp* at* },
       refine lt_of_le_of_lt (le_trans (nat.unpair_right_le _) $ le_trans (nat.unpair_right_le _) _) (nat.div2_lt e),
       simp[nat.div2_val], refine nat.div_le_self _ _ },
    have IH : _ := encode_of_nat_vecterm (e + 1).div2.div2.unpair.2.unpair.2,
    by { suffices : (of_nat_vecterm L (e + 1) 0).encode = nat.bit e.bodd e.div2 + 1,
         { simp[nat.bit_decomp, this] },
         cases C₁ : e.bodd,
         suffices : (of_nat_vecterm L (e + 1) 0).encode = nat.bit ff (nat.bit e.div2.bodd e.div2.div2) + 1,
         { simp[nat.bit_decomp, this] },
         cases C₂ : e.div2.bodd; simp[C₁, C₂] at IH; simp [of_nat_vecterm, vecterm.encode, nat.bit, C₁, C₂, IH, bit1],
         simp [of_nat_vecterm, vecterm.encode, nat.bit, C₁], sorry }
| (e+1) (n+1) :=
    have e.unpair.1 < e + 1 := nat.lt_succ_iff.mpr (nat.unpair_left_le _),
    have e.unpair.2 < e + 1 := nat.lt_succ_iff.mpr (nat.unpair_right_le _),
    have IH₁ : _ := encode_of_nat_vecterm e.unpair.1,
    have IH₂ : _ := encode_of_nat_vecterm e.unpair.2,
  by { simp [of_nat_vecterm, vecterm.encode, IH₁, IH₂], }

private lemma encode_of_nat_vecterm : ∀ e n : ℕ, vecterm.encode (of_nat_vecterm L e n) = e
| 0     0     := by simp[of_nat_vecterm, vecterm.encode]
| (e+1) 0     := 
    have div8 : e.div2.div2 ≤ e :=
      by { simp[nat.div2_val], exact le_trans (nat.div_le_self (e/2) 2) (nat.div_le_self e 2) },
    have e.div2.div2.unpair.2.unpair.2 < e + 1 := nat.lt_succ_iff.mpr
      (le_trans (by { refine le_trans (nat.unpair_right_le _) (le_trans (nat.unpair_right_le _) div8) }) (by refl)),
    have IH : _ := encode_of_nat_vecterm e.div2.div2.unpair.2.unpair.2,
    by { suffices : (of_nat_vecterm L (e + 1) 0).encode = nat.bit e.bodd e.div2 + 1,
         { simp[nat.bit_decomp, this] },
         cases C₁ : e.bodd, { simp[of_nat_vecterm, vecterm.encode, nat.bit, C₁] },
         suffices : (of_nat_vecterm L (e + 1) 0).encode = nat.bit tt (nat.bit e.div2.bodd e.div2.div2) + 1,
         { simp[nat.bit_decomp, this] },
         cases C₂ : e.div2.bodd; simp [of_nat_vecterm, vecterm.encode, nat.bit, C₁, C₂, IH] }
| 0     (n+1) := by { simp [of_nat_vecterm, vecterm.encode, encode_of_nat_vecterm 0 n], refl }
| (e+1) (n+1) :=
    have e.unpair.1 < e + 1 := nat.lt_succ_iff.mpr (nat.unpair_left_le _),
    have e.unpair.2 < e + 1 := nat.lt_succ_iff.mpr (nat.unpair_right_le _),
    have IH₁ : _ := encode_of_nat_vecterm e.unpair.1,
    have IH₂ : _ := encode_of_nat_vecterm e.unpair.2,
  by { simp [of_nat_vecterm, vecterm.encode, IH₁, IH₂], }


private lemma encode_of_nat_code [∀ n, denumerable (L.fn n)] : ∀ e : ℕ, vecterm.encode (of_nat_vecterm L e 0) = e
| 0     := by simp[of_nat_vecterm, vecterm.encode]
| (e+1) := by {
    suffices : (of_nat_vecterm L (e + 1) 0).encode = nat.bit e.bodd e.div2 + 1,
    { simp[nat.bit_decomp, this] },
    cases C₁ : e.bodd, { simp[of_nat_vecterm, vecterm.encode, nat.bit, C₁] },
    suffices : (of_nat_vecterm L (e + 1) 0).encode = nat.bit tt (nat.bit e.div2.bodd e.div2.div2) + 1,
    { simp[nat.bit_decomp, this] },
    cases C₂ : e.div2.bodd; simp [of_nat_vecterm, vecterm.encode, nat.bit, C₁, C₂],
    {  }
     }


end fopl