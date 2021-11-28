import 
  computability.primrec
  computability.partrec
  computability.partrec_code
  computability.halting
  data.pfun
  deduction semantics lindenbaum arithmetic

open encodable denumerable part classical_logic axiomatic_classical_logic axiomatic_classical_logic'

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

def eval : ∀ {n}, pcode n → finitary ℕ n → ℕ
| _ zero            := λ _, 0
| _ succ            := λ v, nat.succ v.head
| _ (nth i)         := λ v, v i
| _ (comp cf cg)    := λ a, eval cf (λ i, eval (cg i) a)
| _ (@prec n cf cg) := λ v : finitary ℕ (n+1),
    v.head.elim (eval cf v.tail) (λ y IH, eval cg (v.tail ::ᶠ IH ::ᶠ y))

theorem exists_pcode {n f} : @nat.primrec' n f ↔ ∃ c : pcode n, (λ v : vector ℕ n, eval c v.nth) = f := ⟨λ h,
begin
  induction h,
  case zero { exact ⟨zero, rfl⟩ },
  case succ { exact ⟨succ, by { funext x, simp[eval],  }⟩ },
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

local infix ` ≃₁ `:80 := ((≃) : term (LA + LC) → term (LA + LC) → formula (LA + LC))
local prefix `∏₁ `:64 := (has_univ_quantifier.univ : formula (LA + LC) → formula (LA + LC))
local prefix `∐₁ `:64 := (has_exists_quantifier.ex : formula (LA + LC) → formula (LA + LC))

namespace prec
open nat.primrec vector

@[reducible] def symbol.fn₁ {n} (c : nat.primrec.pcode n) : finitary (term (LA + LC)) n → term (LA + LC) :=
λ x, term.app (sum.inr (*fn c)) x

prefix `Ḟ `:max := symbol.fn₁

inductive Prim : theory (LA + LC)
| zero   : Prim (Ḟ pcode.zero ∅ ≃ Ż)
| succ   : Prim ∏ (Ḟ pcode.succ fin[#0] ≃₁ Ṡ #0)
| nth {n} (i : fin n) : Prim ∏[n] (Ḟ (pcode.nth i) (λ j, #j) ≃ #i)
| comp {m n} : ∀ (c : pcode n) (cs : fin n → pcode m),
    Prim ∏[m] (Ḟ (pcode.comp c cs) (λ j, #j) ≃ Ḟ c (λ i, Ḟ (cs i) (λ j, #j)))
| prec_z {n} : ∀ (c₀ : pcode n) (c₁ : pcode (n + 2)),
    Prim ∏[n] (Ḟ (pcode.prec c₀ c₁) ((λ j, #j) ::ᶠ Ż) ≃ Ḟ c₀ (λ j, #j))
| prec_s {n} : ∀ (c₀ : pcode n) (c₁ : pcode (n + 2)),
    Prim ∏[n+2] (Ḟ (pcode.prec c₀ c₁) ((λ i, #(i + 1)) ::ᶠ Ṡ #0) ≃ Ḟ c₁ ((λ j, #j) ::ᶠ Ḟ (pcode.prec c₀ c₁) (λ j, #j)))

theorem complete' (T : theory LA) [extend 𝐐 T] {i} (f : vector ℕ i → ℕ) (h : nat.primrec' f) :
∃ c : pcode i, ∀ n : vector ℕ i, Prim ⊢ Ḟ c (λ i, numeral (n.nth i)) ≃ (numeral (f n)) :=
begin
  induction h,
  case nat.primrec'.zero { simp[pcode.eval], refine ⟨pcode.zero, _⟩,
    rintros n,
    simp[show (λ (i : fin 0), ↑(numeral (n.nth i))) = (∅ : finitary (term (LA + LC)) 0), by simp,
         show numeral 0 = Ż, by refl],
    refine by_axiom Prim.zero },
  case nat.primrec'.succ { sorry
    /-
    simp[pcode.eval], refine ⟨pcode.succ, _⟩,
    rintros n,
    have : Prim ⊢ formula.rew ι[0 ⇝ numeral n.head] (Ḟ pcode.succ fin[#0] ≃ Ṡ #0),
      from (by_axiom Prim.succ) ⊚ (numeral n.head), simp[symbol.succ, term.rew] at this, 
    simp[show ∀ i, n.nth i = n.head, by intros i; { simp[show i = 0, by simp] }], exact this },
  case nat.primrec'.nth : m i { simp[pcode.eval], refine ⟨pcode.nth i, _⟩,
    rintros n,
    have := provable.nfal_subst'_finitary (by_axiom (Prim.nth i)) (λ i, numeral (n.nth i)),
     simp[symbol.fn₁, show ∀ i : fin m, ↑i < m, by intros i; exact i.property] at this,
    exact this
    -/ },
  case nat.primrec'.comp : m n g G pg pG IHg IHG { sorry
    /-
    simp at*,
    rcases IHg with ⟨cg, IHg⟩,
    rcases classical.skolem.mp IHG with ⟨cG, IHG⟩,
    refine ⟨pcode.comp cg cG, _⟩, rintros v,
    have eqn₁ : ∀ i : fin n, Prim ⊢ Ḟ (cG i) (λ i, numeral (v.nth i)) ≃ numeral (G i v),
    { intros i, exact IHG i v },
    have eqn₂ : Prim ⊢ Ḟ cg (λ i, numeral (G i v)) ≃ numeral (g (of_fn (λ i, G i v))),
    { have := IHg (of_fn (λ (i : fin n), G i v)), simp at this, exact this },
    have eqn₃ : Prim ⊢ Ḟ (cg.comp cG) (λ i, numeral (v.nth i)) ≃ Ḟ cg (λ i, Ḟ (cG i) (λ i, numeral (v.nth i))),
    { have := provable.nfal_subst'_finitary (by_axiom (Prim.comp cg cG)) (λ (i : fin m), ↑(numeral (v.nth i))),
      simp[symbol.fn₁, show ∀ i : fin m, ↑i < m, by intros i; exact i.property] at this, exact this },    
    calc Ḟ (cg.comp cG) (λ i, numeral (v.nth i))
             ≃[Prim] Ḟ cg (λ i, Ḟ (cG i) (λ i, numeral (v.nth i))) : eqn₃
         ... ≃[Prim] Ḟ cg (λ i, numeral (G i v))                   : (provable.function_ext' _ _ _) ⨀ (provable.conjunction' eqn₁)
         ... ≃[Prim] (numeral (g (of_fn (λ i, G i v))))            : eqn₂
         
      -/   
         },
  case nat.primrec'.prec : n f g pf pg IHf IHg { 
    rcases IHf with ⟨cf, IHf⟩,
    rcases IHg with ⟨cg, IHg⟩,
    refine ⟨pcode.prec cf cg, _⟩, intros v, 
    simp at*,
    cases C : v.head with n; simp[C],
    { have := provable.nfal_subst'_finitary (by_axiom (Prim.prec_z cf cg)),
      have := provable.nfal_subst'_finitary (by_axiom (Prim.prec_z cf cg))  (λ i, numeral (v.nth i)),
      simp[symbol.fn₁, show ∀ i : fin n, ↑i < n, by intros i; exact i.property,
           show ∀ i : fin n, ↑i < n + 1, by intros i; exact nat.lt.step i.property, finitary.cons] at this,
          
      have : (λ (i : fin (n + 1)),
  term.rew (λ (x : ℕ), dite (x < n) (λ (h : x < n), (numeral (v.nth ⟨x, _⟩))) (λ (h : ¬x < n), #(x - n)))
    (ite (↑i < n) #↑i Ż)) = (λ (i : fin (n + 1)), (numeral (v.nth i))),
      { ext i, have C₂ : ↑i < n ∨ ↑i = n, from lt_or_eq_of_le (nat.lt_succ_iff.mp i.property),
      cases C₂; simp[C₂] , { rcases i with ⟨i, _⟩, simp at C₂, rcases C₂ with rfl, simp[show v.nth ⟨i, i_property⟩ = v.head, by refl]  }  }

       }
   }
end



end prec
end arithmetic

end fopl