import 
  computability.primrec
  computability.partrec
  computability.partrec_code
  computability.halting
  data.pfun
  deduction semantics lindenbaum arithmetic

open encodable denumerable roption

namespace nat.primrec
open vector

#check @nat.rec

inductive pcode : ℕ → Type
| zero : pcode 0
| succ : pcode 1
| nth {n} (i : fin n) : pcode n
| comp {m n} : pcode n → (fin n → pcode m) → pcode m
| prec {n} : pcode n → pcode (n + 2) → pcode (n + 1)

namespace pcode

def eval : ∀ {n}, pcode n → vector ℕ n → ℕ
| _ zero            := λ _, 0
| _ succ            := λ v, nat.succ v.head
| _ (nth i)         := λ v, v.nth i
| _ (comp cf cg)    := λ a, eval cf (of_fn (λ i, eval (cg i) a))
| _ (@prec n cf cg) := λ v : vector ℕ (n+1),
    v.head.elim (eval cf v.tail) (λ y IH, eval cg (y ::ᵥ IH ::ᵥ v.tail))

theorem exists_pcode {n f} : @nat.primrec' n f ↔ ∃ c : pcode n, eval c = f := ⟨λ h,
begin
  induction h,
  case zero { exact ⟨zero, rfl⟩ },
  case succ { exact ⟨succ, rfl⟩ },
  case nth  : n i { exact ⟨nth i, rfl⟩ },
  case comp : ar_gs ar_f f gs pf pgs IH_f IH_gs {
    rcases IH_f with ⟨cf, rfl⟩,
    rcases classical.skolem.mp IH_gs with ⟨cgs, cgs_eqn⟩,
    refine ⟨comp cf cgs, _⟩, simp[eval, cgs_eqn] },
  case prec : n f g pf pg hf hg {
    rcases hf with ⟨cf, rfl⟩, rcases hg with ⟨cg, rfl⟩,
    exact ⟨prec cf cg, rfl⟩ }
end, λ h,
begin
  rcases h with ⟨c, rfl⟩, induction c,
  case pcode.zero { exact nat.primrec'.zero },
  case pcode.succ { exact nat.primrec'.succ },
  case pcode.nth : n i { exact nat.primrec'.nth _ },
  case pcode.comp : _ _ cf cgs pf pgs { refine nat.primrec'.comp _ pf pgs },
  case pcode.prec : _ cf cg pf pg { exact nat.primrec'.prec pf pg },
end⟩

end pcode

end nat.primrec

namespace fopl

namespace arithmetic

namespace LC

inductive langf : ℕ → Type
| fn₁ {n} : nat.primrec.pcode n → langf n

notation `*fn ` n := langf.fn₁ n

inductive langp : ℕ → Type

end LC

def LC : language := ⟨LC.langf, LC.langp⟩

open nat.primrec vector

@[reducible] def symbol.const (c : nat.primrec.pcode 0) : term (LA + LC) :=
vecterm.const (sum.inr (*fn c))
prefix `Ċ `:max := symbol.const

@[reducible] def symbol.fn₁ {n} (c : nat.primrec.pcode n) : vector (term (LA + LC)) n → term (LA + LC) :=
λ x, vecterm.app' (sum.inr (*fn c)) x

prefix `Ḟ `:max := symbol.fn₁
#check @symbol.const

inductive Prim : theory (LA + LC)
| zero   : Prim (Ḟ pcode.zero nil =̇ Ż)
| succ   : Prim ∀̇ (Ḟ pcode.succ (#0 ::ᵥ nil) =̇ Ṡ #0)
| nth {n} (i : fin n) : Prim ∀̇[n+1] (Ḟ (pcode.nth i) ## =̇ #i)
| comp {m n} : ∀ (c : pcode n) (cs : fin n → pcode m),
    Prim ∀̇[m+1] (Ḟ (pcode.comp c cs) ## =̇ Ḟ c (of_fn $ λ i, Ḟ (cs i) ##))
| prec_z {n} : ∀ (c₀ : pcode n) (c₁ : pcode (n + 2)),
    Prim ∀̇[n+1] (Ḟ (pcode.prec c₀ c₁) (Ż ::ᵥ ##) =̇ Ḟ c₀ ##)
| prec_s {n} : ∀ (c₀ : pcode n) (c₁ : pcode (n + 2)),
    Prim ∀̇[n+2] (Ḟ (pcode.prec c₀ c₁) (Ṡ #0 ::ᵥ (of_fn $ λ i, #(i + 1))) =̇ Ḟ c₁ (Ḟ (pcode.prec c₀ c₁) ## ::ᵥ ##))

#check @Prim.prec_z
theorem complete (T : theory LA) [extend 𝐐 T] {i} (f : vector ℕ i → ℕ) (h : primrec f) : ∃ c : pcode i, ∀ n m,
  f n = m → Prim ⊢ Ḟ c (n.map ↑numeral) =̇ (numeral m) :=
begin
  suffices :
    ∀ c : pcode, ∀ n m : ℕ, c.eval n = m → Prim ⊢ Ḟ c (numeral n) =̇ (numeral m),
  { rcases pcode.exists_pcode.mp (primrec.nat_iff.mp h) with ⟨c, rfl⟩,
    refine ⟨c, this c⟩ },
  intros c, induction c,
  case pcode.zero { simp[pcode.eval], rintros n m rfl, refine (provable.AX Prim.zero).fal_subst (numeral n) },
  case pcode.succ { simp[pcode.eval], rintros n m rfl, refine (provable.AX Prim.succ).fal_subst (numeral n) },
  case pcode.comp : cf cg hf hg { simp[pcode.eval], rintros n m rfl,
    have : Prim ⊢ Ḟ (cf.comp cg) (numeral n) =̇ Ḟ cf (Ḟ cg (numeral n)), from (provable.AX $ Prim.comp cf cg).fal_subst (numeral n),
    sorry }, sorry,
  --rcases pcode.exists_pcode.mp (primrec.nat_iff.mp h) with ⟨c, rfl⟩,
  --use c,
end

end arithmetic

end fopl