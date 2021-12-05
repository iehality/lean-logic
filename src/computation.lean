import 
  computability.primrec
  computability.partrec
  computability.partrec_code
  computability.halting
  data.pfun
  deduction semantics lindenbaum arithmetic
  proof
  coding

open encodable denumerable part classical_logic axiomatic_classical_logic axiomatic_classical_logic'

open vector

namespace fopl

namespace arithmetic

namespace LC

inductive pcode : ℕ → Type
| zero : pcode 0
| succ : pcode 1
| nth {n} (i : fin n) : pcode n
| comp {m n} : pcode n → (fin n → pcode m) → pcode m
| prec {n} : pcode n → pcode (n + 2) → pcode (n + 1)

namespace pcode

--lemma finitary_vec_head {α : Type*} {n} (v :vector α n)

def eval : ∀ {n}, pcode n → vector ℕ n → ℕ
| _ zero            := λ _, 0
| _ succ            := λ v, nat.succ v.head
| _ (nth i)         := λ v, v.nth i
| _ (comp cf cg)    := λ a, eval cf (of_fn (λ i, eval (cg i) a))
| _ (@prec n cf cg) := λ v : vector ℕ (n+1),
    v.head.elim (eval cf v.tail) (λ y IH, eval cg (y ::ᵥ IH ::ᵥ v.tail))

theorem exists_pcode {n : ℕ} {f : vector ℕ n → ℕ} :
  nat.primrec' f ↔ ∃ c : pcode n, eval c = f := ⟨λ h,
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

def eval_fin {n} (c : pcode n) (f : finitary ℕ n) : ℕ := eval c (of_fn f)

@[simp] lemma eval_fin_zero : eval_fin pcode.zero = (λ _, 0) := rfl

@[simp] lemma eval_fin_succ : eval_fin pcode.succ = (λ n, n 0 + 1) := rfl

@[simp] lemma eval_fin_nth {n} (i : fin n) : eval_fin (pcode.nth i) = (λ f, f i) :=
by funext f; simp[eval_fin, eval]

@[simp] lemma eval_fin_comp {n m} (cf : pcode n) (cF : finitary (pcode m) n) :
  eval_fin (pcode.comp cf cF) = (λ f, eval_fin cf (λ i, eval_fin (cF i) f)) :=
by funext f; simp[eval_fin, eval]

@[simp] lemma eval_fin_prec {n} (cf : pcode n) (cg : pcode (n + 2)) :
  eval_fin (pcode.prec cf cg) =
  (λ f, (f 0).elim (eval_fin cf f.tail) (λ y IH, eval_fin cg (y ::ᶠ IH ::ᶠ f.tail))) :=
by {funext f; simp[eval_fin, eval], congr }

end pcode

inductive langp : ℕ → Type

end LC

def LC : language := ⟨LC.pcode, LC.langp⟩

local infix ` ≃₁ `:50 := ((≃) : term (LA + LC) → term (LA + LC) → formula (LA + LC))
local prefix `∏₁ `:64 := (has_univ_quantifier.univ : formula (LA + LC) → formula (LA + LC))
local prefix `∐₁ `:64 := (has_exists_quantifier.ex : formula (LA + LC) → formula (LA + LC))

namespace prim
open LC vector

 def symbol.fn₁ {n} (c : pcode n) : finitary (term (LA + LC)) n → term (LA + LC) :=
λ x, term.app (sum.inr (c)) x

prefix `Ḟ `:max := symbol.fn₁

@[simp] lemma fn_rew {n} (c : pcode n) (v : finitary (term (LA + LC)) n) (s : ℕ → term (LA + LC)) :
  term.rew s (Ḟ c v) = Ḟ c (λ i, term.rew s (v i)) :=
by simp[symbol.fn₁]

def numeral' : ℕ → term (LA + LC) := λ n, numeral n

inductive Prim : theory (LA + LC)
| zero                : Prim (Ḟ pcode.zero ∅ ≃ 0)
| succ                : Prim ∏₁ (Ḟ pcode.succ ‹#0› ≃₁ Succ #0)
| nth {n} (i : fin n) : Prim ∏[n] (Ḟ (pcode.nth i) (λ j, #j) ≃ #i)
| comp {m n}          : ∀ (c : pcode n) (cs : fin n → pcode m),
    Prim ∏[m] (Ḟ (pcode.comp c cs) (λ j, #j) ≃ Ḟ c (λ i, Ḟ (cs i) (λ j, #j)))
| prec_z {n}          : ∀ (c₀ : pcode n) (c₁ : pcode (n + 2)),
    Prim ∏[n] (Ḟ (pcode.prec c₀ c₁) (0 ::ᶠ (λ j, #j)) ≃ Ḟ c₀ (λ j, #j))
| prec_s {n}          : ∀ (c₀ : pcode n) (c₁ : pcode (n + 2)),
    Prim ∏[n+1] (Ḟ (pcode.prec c₀ c₁) (Succ #0 ::ᶠ (λ i, #(i + 1))) ≃
      Ḟ c₁ (#0 ::ᶠ Ḟ (pcode.prec c₀ c₁) (λ j, #j) ::ᶠ (λ j, #(j+1))))

theorem Prim_complete {i} (c : pcode i) :
  ∀ n : finitary ℕ i, Prim ⊢ Ḟ c (λ i, (n i)˙) ≃ (c.eval_fin n)˙ := λ v,
begin
  induction c generalizing v,
  case zero { simp[pcode.eval],
    simp[show (λ (i : fin 0), (v i)˙) = (∅ : finitary (term (LA + LC)) 0), by simp],
    refine by_axiom Prim.zero },
  case succ { 
    simp[pcode.eval], 
    have : Prim ⊢ formula.rew ι[0 ⇝ (v 0)˙] (Ḟ pcode.succ ‹#0› ≃ Succ #0),
      from (by_axiom Prim.succ) ⊚ (v 0)˙, simp at this, 
    simp[show ∀ i, v i = v 0, by intros i; { simp[show i = 0, by simp] }], exact this },
  case nth : m i { simp[pcode.eval],
    have := provable.nfal_subst'_finitary (by_axiom (Prim.nth i)) (λ i, (v i)˙),
     simp at this, exact this },
  case comp : m n cf cF IHf IHF { 
    simp at*,
    calc Ḟ (cf.comp cF) (λ i, (v i)˙) ≃[Prim] Ḟ cf (λ i, Ḟ (cF i) (λ i, (v i)˙))
    : by { have := provable.nfal_subst'_finitary (by_axiom (Prim.comp cf cF)) (λ i, (v i)˙), simp at this, exact this }
                                  ... ≃[Prim] Ḟ cf (λ i, ((cF i).eval_fin v)˙) 
    : (provable.function_ext' _ _ _) ⨀ (provable.conjunction' (λ i, IHF i v))
                                  ... ≃[Prim] (cf.eval_fin (λ i, (cF i).eval_fin v))˙
    : IHf _ },
  case prec : n cf cg IHf IHg { 
    simp at*,
    induction C : (v 0) with s IH generalizing v; simp[C],
    { have := provable.nfal_subst'_finitary (by_axiom (Prim.prec_z cf cg))  (λ i, numeral (v.tail i)),
      simp at this,
      calc
        Ḟ (cf.prec cg) (λ i, (v i)˙) ≃[Prim] Ḟ cf (λ i, (v.tail i)˙)
      : by { refine cast _ this, congr, { funext i, rcases i with ⟨i, h⟩, cases i; simp[C, finitary.tail, numeral], } }

                                 ... ≃[Prim] (cf.eval_fin v.tail)˙
      : IHf v.tail },
    { let I : ℕ := nat.elim (cf.eval_fin v.tail) (λ (y IH : ℕ), cg.eval_fin (y ::ᶠ IH ::ᶠ v.tail)) s,
      have IH' : Prim ⊢ Ḟ (cf.prec cg) (s˙ ::ᶠ λ i, (v.tail i)˙) ≃ I˙,
      { have := IH (s ::ᶠ v.tail) (by simp), simp at this, exact this },

      calc          Ḟ (cf.prec cg) (λ i, (v i)˙)
                  = Ḟ (cf.prec cg) (Succ s˙ ::ᶠ λ i, (v.tail i)˙) 
      : by { congr, rw [←finitary.app_0_cons_tail_refl (λ i, (v i)˙)], simp[C, finitary.tail, numeral] }
      
        ... ≃[Prim] Ḟ cg (s˙ ::ᶠ Ḟ (cf.prec cg) (s˙ ::ᶠ λ i, (v.tail i)˙) ::ᶠ λ i, (v.tail i)˙)
      : by { have := provable.nfal_subst'_finitary (by_axiom (Prim.prec_s cf cg))
             (s˙ ::ᶠ (λ i, (v.tail i)˙)), simp at this, exact this }
      
        ... ≃[Prim] Ḟ cg (s˙ ::ᶠ I˙ ::ᶠ λ i, (v.tail i)˙)
      : by { refine (provable.function_ext' _ _ _) ⨀ (provable.conjunction' _), intros i,
             rcases i with ⟨i, lt_i⟩, cases i with i; cases i with i; simp, exact IH' }

        ... ≃[Prim] (cg.eval_fin (s ::ᶠ I ::ᶠ v.tail))˙ 
      : by { refine cast _ (IHg (s ::ᶠ I ::ᶠ v.tail)), congr, funext i, rcases i with ⟨i, h⟩,
             cases i with i; cases i with i; simp } } }
end

@[simp] def prim_fn : ∀ {n}, (LA + LC).fn n → finitary ℕ n → ℕ
| _ (sum.inl langf.zero) v := 0
| _ (sum.inl langf.succ) v := v 0 + 1
| _ (sum.inl langf.add)  v := v 0 + v 1
| _ (sum.inl langf.mul)  v := v 0 * v 1
| _ (sum.inr c)          v := pcode.eval_fin c v

def prim_standard : model (LA + LC) := {
  dom := ℕ,
  inhabited := nat.inhabited,
  fn := @prim_fn,
  pr := λ n l v,
    match n, l, v with
    | 2, (sum.inl langp.le), v := v 0 ≤ v 1
    end }

notation `ℙ` := prim_standard

namespace prim_standard

@[simp] lemma dom_eq : |ℙ| = ℕ := rfl

@[simp] lemma zero_eq (v : finitary ℕ 0) : prim_standard.fn has_zero_symbol.zero v = (0 : ℕ) := rfl

@[simp] lemma succ_eq (v : finitary ℕ 1) : prim_standard.fn has_succ_symbol.succ v = (v 0 + 1 : ℕ) := rfl

@[simp] lemma add_eq (v : finitary ℕ 2) : prim_standard.fn has_add_symbol.add v = (v 0 + v 1 : ℕ) := rfl

@[simp] lemma mul_eq (v : finitary ℕ 2) : prim_standard.fn has_mul_symbol.mul v = (v 0 * v 1 : ℕ) := rfl

@[simp] lemma le_eq (v : finitary ℕ 2) : prim_standard.pr has_le_symbol.le v ↔ (v 0 : ℕ) ≤ v 1 := by refl

lemma prim_standard.fn_eq : prim_standard.fn = @prim_fn := rfl

@[simp] lemma fun_eq {n} (c : pcode n) (v : finitary ℕ n) :
  prim_standard.fn (sum.inr c) v = pcode.eval_fin c v := by { cases c; simp[*, prim_standard.fn_eq] }

theorem models_Prim : ℙ ⊧ₜₕ Prim := λ p h e,
by {cases h; simp[symbol.fn₁, models_univs],
     { intros, congr; simp[finitary.tail] } }

@[simp] lemma numeral_eval (n : ℕ) (e : ℕ → |ℙ|) : term.val e (n˙) = n :=
by { induction n with n IH; simp[numeral, *] }

end prim_standard

theorem Prim_consistent : theory.consistent Prim := model_consistent prim_standard.models_Prim

variables {L : language.{0}} [primcodable (formula L)] [primcodable (proof L)]
  
@[reducible] def goedel_number (p : formula L) : ℕ := encode p

notation `⌜` p `⌝` := goedel_number p

variables {P : theory (LA + LC)} [extend Prim P] [theory_of_model ℙ P]
  {T : theory L} [primrec_theory T]

theorem Prim_complete_provability : ∃ c : pcode 2, ∀ p,
  T ⊢ p ↔ P ⊢ ∐ (Ḟ c ‹⌜p⌝˙, #0› ≃₁ 2˙) :=
begin
  let pr : vector ℕ 2 → ℕ := λ v, proof.of_n T (v.nth 0) (v.nth 1),
  have : primrec pr,
    from primrec_theory.prim.comp (primrec.vector_nth.comp primrec.id (primrec.const 0))
      (primrec.vector_nth.comp primrec.id (primrec.const 1)),
  rcases pcode.exists_pcode.mp (nat.primrec'.of_prim this) with ⟨c, c_eval_eq_pr⟩,
  refine ⟨c, λ p, _⟩,
  have pr_iff : T ⊢ p ↔ ∃ s, pr (⌜p⌝ ::ᵥ s ::ᵥ vector.nil) = 2,
  { simp [proof.of_n_complete, pr], refl },
  split,
  { intros h,
    suffices : Prim ⊢ ∐ (Ḟ c ‹⌜p⌝˙, #0› ≃ 2˙), { exact provable.extend this },
    rcases pr_iff.mp h with ⟨s, pr_eq⟩, 
    have : Prim ⊢ Ḟ c ‹⌜p⌝˙, s˙› ≃ Succ Succ 0,
    { have := Prim_complete c ‹⌜p⌝, s›,
      simp[pcode.eval_fin, c_eval_eq_pr, pr_eq] at this,
      exact cast (by { congr, ext; simp }) this },
    refine provable.use (s˙) _, simp,
    refine cast (by { congr; ext; simp }) this },
  { intros h, 
    have : ℙ ⊧ ∐ (Ḟ c ‹⌜p⌝˙, #0› ≃ 2˙), from soundness h theory_of_model.models,
    have : ∃ s : ℕ, c.eval_fin ‹⌜p⌝, s› = 2,
    { have := this (default _),
      simp[symbol.fn₁, show 1 + 1 = 2, by simp] at this, 
      refine cast _ this, congr },
    rcases this with ⟨s, hs⟩,
    refine pr_iff.mpr ⟨s, _⟩, simp[pr, pcode.eval_fin, c_eval_eq_pr] at hs ⊢, exact hs }
end

variables (P) (T)

noncomputable def prov_index : pcode 2 :=
classical.some (@Prim_complete_provability _ _ _ P _ _ T _)

noncomputable def Prov (t : term (LA + LC)) : formula (LA + LC) :=
∐ (Ḟ (prov_index P T) ‹t, #0› ≃₁ 2˙)

variables {P} {T}

lemma prov_index_spec : ∀ p : formula L,
  T ⊢ p ↔ P ⊢ ∐ (Ḟ (prov_index P T) ‹⌜p⌝˙, #0› ≃₁ 2˙) :=
classical.some_spec (@Prim_complete_provability _ _ _ P _ _ T _)

lemma Prov_spec : ∀ p : formula L,
  T ⊢ p ↔ P ⊢ Prov P T (⌜p⌝˙) :=
prov_index_spec

end prim

namespace prim_incompleteness
variables {L : language.{0}} [primcodable (formula L)] [primcodable (proof L)]

def Γ (p : formula L) (t : term L) : formula L := p.rew ι[0 ⇝ t]


end prim_incompleteness

end arithmetic

end fopl