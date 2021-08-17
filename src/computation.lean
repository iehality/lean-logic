
import 
  computability.primrec
  computability.partrec
  computability.partrec_code
  computability.halting
  data.pfun
  deduction semantics lindenbaum arithmetic

open encodable denumerable roption

namespace nat.primrec

inductive code : Type
| zero : code
| succ : code
| left : code
| right : code
| pair : code → code → code
| comp : code → code → code
| prec : code → code → code

namespace code

def eval : code → ℕ → ℕ
| zero         := λ x, 0
| succ         := nat.succ
| left         := λ n : ℕ, n.unpair.1
| right        := λ n : ℕ, n.unpair.2
| (pair cf cg) := λ n, nat.mkpair (eval cf n) (eval cg n)
| (comp cf cg) := λ n, eval cf (eval cg n)
| (prec cf cg) := nat.unpaired (λ a n : ℕ, n.elim (eval cf a) (λ y i, eval cg (a.mkpair (y.mkpair i))))

theorem exists_code {f : ℕ → ℕ} : nat.primrec f ↔ ∃ c : code, eval c = f := ⟨λ h,
begin
  induction h,
  case nat.primrec.zero { refine ⟨zero, rfl⟩ },
  case nat.primrec.succ { exact ⟨succ, rfl⟩ },
  case nat.primrec.left { exact ⟨left, rfl⟩ },
  case nat.primrec.right { exact ⟨right, rfl⟩ },  
  case nat.primrec.pair : f g pf pg hf hg 
  { rcases hf with ⟨cf, rfl⟩, rcases hg with ⟨cg, rfl⟩, refine ⟨pair cf cg, rfl⟩ },
  case nat.primrec.comp : f g pf pg hf hg {
    rcases hf with ⟨cf, rfl⟩, rcases hg with ⟨cg, rfl⟩,
    exact ⟨comp cf cg, rfl⟩ },
  case nat.primrec.prec : f g pf pg hf hg {
    rcases hf with ⟨cf, rfl⟩, rcases hg with ⟨cg, rfl⟩,
    exact ⟨prec cf cg, rfl⟩ }
end, λ h,
begin
  rcases h with ⟨c, rfl⟩, induction c,
  case nat.primrec.code.zero { exact nat.primrec.zero },
  case nat.primrec.code.succ { exact nat.primrec.succ },
  case nat.primrec.code.left { exact nat.primrec.left },
  case nat.primrec.code.right { exact nat.primrec.right },
  case nat.primrec.code.pair : cf cg pf pg { exact pf.pair pg },
  case nat.primrec.code.comp : cf cg pf pg { exact pf.comp pg },
  case nat.primrec.code.prec : cf cg pf pg { exact pf.prec pg },
end⟩

end code

end nat.primrec

namespace fopl

namespace arithmetic

namespace LC

inductive langf : ℕ → Type
| fn₁ : nat.primrec.code → langf 1
| pair : langf 2
notation `*fn₁` n := langf.fn₁ n
notation `*fn₂` n := langf.fn₂ n

inductive langp : ℕ → Type

end LC

def LC : language := ⟨LC.langf, LC.langp⟩

open nat.primrec

@[reducible] def symbol.fn₁ (c : nat.primrec.code) : term (LA + LC) → term (LA + LC) := λ x, vecterm.app (sum.inr (*fn₁ c)) x
prefix `Ḟ `:max := symbol.fn₁

@[reducible] def pair : term (LA + LC) → term (LA + LC) → term (LA + LC) :=
λ x y, vecterm.app (sum.inr LC.langf.pair) (x ::: y)

inductive Prim : theory (LA + LC)
| zero   : Prim ∀̇ (Ḟ code.zero #0 =̇ Ż)
| succ   : Prim ∀̇ (Ḟ code.succ #0 =̇ Ṡ #0)
| right  : Prim ∀̇ (Ḟ code.right (pair #0 #1) =̇ #0)
| left   : Prim ∀̇ (Ḟ code.left (pair #0 #1) =̇ #1)
| pair   : ∀ (c₁ c₂ : code), Prim ∀̇ (Ḟ (code.pair c₁ c₂) #0 =̇ pair (Ḟ c₁ $ #0) (Ḟ c₂ $ #0))
| comp   : ∀ (c₁ c₂ : code), Prim ∀̇ (Ḟ (code.comp c₁ c₂) #0 =̇ Ḟ c₁ (Ḟ c₂ $ #0))
| prec_z : ∀ (c₁ c₂ : code), Prim ∀̇ (Ḟ (code.prec c₁ c₂) (pair #0 Ż) =̇ Ḟ c₁ #0)
| prec_s : ∀ (c₁ c₂ : code),
    Prim ∀̇ ∀̇ (Ḟ (code.prec c₁ c₂) (pair #0 (Ṡ #1)) =̇ Ḟ c₂ (pair #0 (Ḟ (code.prec c₁ c₂) (pair #0 #1))))

theorem complete (T : theory LA) [extend 𝐐 T] (f : ℕ → ℕ) (h : primrec f) : ∃ c : code, ∀ n m : ℕ,
  f n = m → Prim ⊢ Ḟ c (numeral n) =̇ (numeral m) :=
begin
  suffices :
    ∀ c : code, ∀ n m : ℕ, c.eval n = m → Prim ⊢ Ḟ c (numeral n) =̇ (numeral m),
  { rcases code.exists_code.mp (primrec.nat_iff.mp h) with ⟨c, rfl⟩,
    refine ⟨c, this c⟩ },
  intros c, induction c,
  case code.zero { simp[code.eval], rintros n m rfl, refine (provable.AX Prim.zero).fal_subst (numeral n) },
  case code.succ { simp[code.eval], rintros n m rfl, refine (provable.AX Prim.succ).fal_subst (numeral n) },
  case code.comp : cf cg hf hg { simp[code.eval], rintros n m rfl,
    have : Prim ⊢ Ḟ (cf.comp cg) (numeral n) =̇ Ḟ cf (Ḟ cg (numeral n)), from (provable.AX $ Prim.comp cf cg).fal_subst (numeral n),
    sorry }, sorry,
  --rcases code.exists_code.mp (primrec.nat_iff.mp h) with ⟨c, rfl⟩,
  --use c,
end

end arithmetic

end fopl