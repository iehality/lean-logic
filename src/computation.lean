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

 def symbol.fn₁ {n} (c : nat.primrec.pcode n) : finitary (term (LA + LC)) n → term (LA + LC) :=
λ x, term.app (sum.inr (*fn c)) x

prefix `Ḟ `:max := symbol.fn₁

def symbol.zero : term (LA + LC) := term.app (sum.inl *Z) finitary.nil
notation `Ż` := symbol.zero

def symbol.succ : term (LA + LC) → term (LA + LC) := λ x, term.app (sum.inl *S) fin[x]
prefix `Ṡ `:max := symbol.succ

@[simp] lemma zero_eq : ((Ż : term LA) : term (LA + LC)) = Ż :=
by unfold_coes; simp[(symbol.zero), arithmetic.symbol.zero]

@[simp] lemma succ_eq (t : term LA) : ((Ṡ t : term LA) : term (LA + LC)) = Ṡ t :=
by unfold_coes; simp[(symbol.succ), arithmetic.symbol.succ]; refl

@[simp] lemma zero_rew (s : ℕ → term (LA + LC)) : term.rew s Ż = Ż := by simp[symbol.zero]

@[simp] lemma succ_rew (t : term (LA + LC)) (s : ℕ → term (LA + LC)) : term.rew s (Ṡ t) = Ṡ (t.rew s) :=
by simp[symbol.succ]

@[simp] lemma fn_rew {n} (c : pcode n) (v : finitary (term (LA + LC)) n) (s : ℕ → term (LA + LC)) :
  term.rew s (Ḟ c v) = Ḟ c (λ i, term.rew s (v i)) :=
by simp[symbol.fn₁]
@[simp] lemma numeral0 : (numeral 0 : term (LA + LC)) = Ż :=
by { simp[numeral] }

def numeral' : ℕ → term (LA + LC) := λ n, numeral n

local notation n`˙`:1200 := numeral' n

@[simp] lemma numeral_eq (n) : (numeral n : term (LA + LC)) = n˙ := rfl

@[simp] lemma numeral0_eq : 0˙ = Ż := by { simp [numeral', symbol.zero, -numeral_eq, numeral] }

@[simp] lemma numeral_succ_eq (n : ℕ) : (n + 1)˙ = Ṡ n˙ := by { simp [numeral', symbol.succ, -numeral_eq, numeral], refl }


inductive Prim : theory (LA + LC)
| zero   : Prim (Ḟ pcode.zero ∅ ≃ Ż)
| succ   : Prim ∏ (Ḟ pcode.succ fin[#0] ≃₁ Ṡ #0)
| nth {n} (i : fin n) : Prim ∏[n] (Ḟ (pcode.nth i) (λ j, #j) ≃ #i)
| comp {m n} : ∀ (c : pcode n) (cs : fin n → pcode m),
    Prim ∏[m] (Ḟ (pcode.comp c cs) (λ j, #j) ≃ Ḟ c (λ i, Ḟ (cs i) (λ j, #j)))
| prec_z {n} : ∀ (c₀ : pcode n) (c₁ : pcode (n + 2)),
    Prim ∏[n] (Ḟ (pcode.prec c₀ c₁) (Ż ᶠ:: (λ j, #j)) ≃ Ḟ c₀ (λ j, #j))
| prec_s {n} : ∀ (c₀ : pcode n) (c₁ : pcode (n + 2)),
    Prim ∏[n+1] (Ḟ (pcode.prec c₀ c₁) (Ṡ #0 ᶠ:: (λ i, #(i + 1))) ≃
    Ḟ c₁ (#0 ᶠ:: Ḟ (pcode.prec c₀ c₁) (λ j, #j) ᶠ:: (λ j, #(j+1))))

theorem Plim_complete (T : theory LA) [extend 𝐐 T] {i} (f : vector ℕ i → ℕ) (h : nat.primrec' f) :
∃ c : pcode i, ∀ n : vector ℕ i, Prim ⊢ Ḟ c (λ i, (n.nth i)˙) ≃ (f n)˙ :=
begin
  induction h,
  case nat.primrec'.zero { simp[pcode.eval], refine ⟨pcode.zero, _⟩,
    rintros n,
    simp[show (λ (i : fin 0), (n.nth i)˙) = (∅ : finitary (term (LA + LC)) 0), by simp],
    refine by_axiom Prim.zero },
  case nat.primrec'.succ { 
    simp[pcode.eval], refine ⟨pcode.succ, _⟩,
    rintros n,
    have : Prim ⊢ formula.rew ι[0 ⇝ numeral n.head] (Ḟ pcode.succ fin[#0] ≃ Ṡ #0),
      from (by_axiom Prim.succ) ⊚ (numeral n.head), simp[symbol.succ, term.rew] at this, 
    simp[show ∀ i, n.nth i = n.head, by intros i; { simp[show i = 0, by simp] }], exact this },
  case nat.primrec'.nth : m i { simp[pcode.eval], refine ⟨pcode.nth i, _⟩,
    rintros n,
    have := provable.nfal_subst'_finitary (by_axiom (Prim.nth i)) (λ i, numeral (n.nth i)),
     simp at this, exact this },
  case nat.primrec'.comp : m n g G pg pG IHg IHG { 
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
         ... ≃[Prim] (numeral (g (of_fn (λ i, G i v))))            : eqn₂ },
  case nat.primrec'.prec : n f g pf pg IHf IHg { 
    rcases IHf with ⟨cf, IHf⟩,
    rcases IHg with ⟨cg, IHg⟩,
    refine ⟨pcode.prec cf cg, _⟩, intros v, 
    simp at*,
    induction C : v.head with s IH generalizing v; simp[C],
    { have := provable.nfal_subst'_finitary (by_axiom (Prim.prec_z cf cg))  (λ i, numeral (v.tail.nth i)),
      simp at this,
      calc Ḟ (cf.prec cg) (λ i, numeral (v.nth i)) ≃[Prim] Ḟ cf (λ i, numeral (v.tail.nth i)) :
      by { refine cast _ this, congr, { funext i, rcases i with ⟨i, h⟩, cases i;
           simp[C]}, { funext i, simp[tail_nth] } }
                                               ... ≃[Prim] numeral (f v.tail) : IHf v.tail },
    { let I : ℕ := nat.elim (f v.tail) (λ y IH, g (y::ᵥ IH::ᵥ v.tail)) s,
      have IH' : Prim ⊢ Ḟ (cf.prec cg) (s˙ ᶠ:: λ i, (v.nth i.succ)˙) ≃ I˙,
      { have := IH (s ::ᵥ v.tail) (by simp), simp at this,
        from cast (by { congr, funext i, rcases i with ⟨i, h⟩,cases i; simp }) this },
      
      have lmm₁ : Prim ⊢ Ḟ (cf.prec cg) (Ṡ s˙ ᶠ:: λ i, (v.nth i.succ)˙) ≃ 
        Ḟ cg (s˙ ᶠ:: Ḟ (cf.prec cg) (s˙ ᶠ:: λ i, (v.nth i.succ)˙) ᶠ:: λ i, (v.nth i.succ)˙),
      { have := provable.nfal_subst'_finitary (by_axiom (Prim.prec_s cf cg))
        (s˙ ᶠ:: (λ i, (v.tail.nth i)˙)), simp[succ_rew] at this, exact this },
      
      calc        Ḟ (cf.prec cg) (λ i, (v.nth i)˙)
      
          =       Ḟ (cf.prec cg) (Ṡ s˙ ᶠ:: λ i, (v.nth i.succ)˙) :
      by { congr, funext i, rcases i with ⟨i, h⟩, cases i; simp[C] }
      
      ... ≃[Prim] Ḟ cg (s˙ ᶠ:: Ḟ (cf.prec cg) (s˙ ᶠ:: λ i, (v.nth i.succ)˙) ᶠ:: λ i, (v.nth i.succ)˙) : lmm₁
      
      ... ≃[Prim] Ḟ cg (s˙ ᶠ:: I˙ ᶠ:: λ i, (v.nth i.succ)˙) :
      by { refine (provable.function_ext' _ _ _) ⨀ (provable.conjunction' _), intros i,
           rcases i with ⟨i, lt_i⟩, cases i with i; cases i with i; simp, exact IH' }

      ... ≃[Prim] (g (s::ᵥ I ::ᵥ v.tail))˙ : 
      by { refine cast _ (IHg (s ::ᵥ I ::ᵥ v.tail)), congr, funext i, rcases i with ⟨i, h⟩,
           cases i with i; cases i with i; simp } } }
end

example {n i : ℕ} : i + 1 < n + 1 → i < n := by { exact nat.succ_lt_succ_iff.mp }

end prec
end arithmetic

end fopl