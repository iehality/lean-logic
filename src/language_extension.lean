import translation

universes u v

namespace fopl
open term formula

variables {L L₁ L₂ L₃ : language.{u}}
local infix ` ≃₀ `:50 := ((≃) : term L → term L → formula L)
local infix ` ≃₁ `:50 := ((≃) : term L₁ → term L₁ → formula L₁)
local infix ` ≃₂ `:50 := ((≃) : term L₂ → term L₂ → formula L₂)

namespace language

namespace add_consts
open language_translation language_translation_coe extension
  proof provable axiomatic_classical_logic' axiomatic_classical_logic
variables {C : Type u} [decidable_eq C]

@[simp] def symbols_aux : term (L + consts C) → list C
| (#n)                      := []
| (@term.app _ n f v)       :=
  have h : ∀ i, (v i).complexity < (⨆ᶠ i, (v i).complexity) + 1, from λ i,  nat.lt_succ_iff.mpr (le_fintype_sup (λ i, (v i).complexity) i),
  by { cases f, { exact list.Sup (λ i, symbols_aux (v i)) }, { cases n, exact [f], rcases f, } }

def symbols (t : term (L + consts C)) : list C := (symbols_aux t).dedup

def symbols' {n} (v : fin n → term (L + consts C)) : list C := (list.Sup (λ i, symbols (v i))).dedup

@[simp] lemma symbols_var_eq_nil (n : ℕ) : symbols (#n : term (L + consts C)) = [] :=
by simp[symbols]

variables (Γ : list C) (b : ℕ) 

def consts_to_var : C → ℕ := λ c, (list.index_of c Γ)

lemma consts_to_var_lt_Γ_of_mem {Γ : list C} {c : C} (mem : c ∈ Γ) : consts_to_var Γ c < Γ.length :=
by { simp[consts_to_var], exact list.index_of_lt_length.mpr mem }

@[simp] def elim_aux : term (L + consts C) → term L
| (#n)                      := if n < b then #n else #(Γ.length + n)
| (@term.app _ n f v)       :=
    by { cases f, { exact app f (λ i, elim_aux (v i)) },
         { rcases n, { exact #(consts_to_var Γ f + b) }, { rcases f } } }

@[simp] def formula_elim_aux : ℕ → formula (L + consts C) → formula L
| b (app r v)                          := by { rcases r, { refine app r (λ i, elim_aux Γ b (v i)) }, { rcases r } }
| b ((t₁ : term (L + consts C)) ≃ t₂)  := elim_aux Γ b t₁ ≃ elim_aux Γ b t₂
| b ⊤                                  := ⊤
| b (p ⟶ q)                            := formula_elim_aux b p ⟶ formula_elim_aux b q
| b (⁻p)                               := ⁻formula_elim_aux b p
| b (∏ p)                              := ∏ formula_elim_aux (b + 1) p

def var_to_consts : ℕ → term (consts C) := λ n, if h : n < Γ.length then Γ.nth_le n h else #(n - Γ.length)

def formula_elim : formula (L + consts C) → formula L := λ p, ∏[Γ.length] formula_elim_aux Γ 0 p

@[simp] lemma term_elim_coe : ∀ (t : term L),
  elim_aux Γ b (t : term (L + consts C)) = t.rew (λ x, if x < b then #x else #(Γ.length + x))
| (#n)                      := by simp
| (@term.app _ n f v) := by { simp[coe_fn₁], funext i, exact term_elim_coe (v i) }

lemma formula_elim_coe : ∀ (b : ℕ) (p : formula L),
  formula_elim_aux Γ b (p : formula (L + consts C)) = p.rew (λ x, if x < b then #x else #(Γ.length + x))
| b (app r v) := by simp[coe_pr₁]
| b (equal t u) := by simp
| b ⊤ := by simp
| b (p ⟶ q) := by simp[formula_elim_coe b p, formula_elim_coe b q]
| b (⁻p) := by simp[formula_elim_coe b p]
| b (∏ p) := by { simp[formula_elim_coe (b + 1) p], 
    have : (λ x, ite (x < b) #x #(Γ.length + x) : ℕ → term L)^1 = (λ x, ite (x < b + 1) #x #(Γ.length + x)),
    { funext x, simp[rewriting_sf_itr.pow_eq'],
      rcases x; simp[←nat.add_one], by_cases C : x < b; simp[C, add_assoc] },
    simp[this] }

@[simp] lemma formula_elim_coe_0 (p : formula L) :
  formula_elim_aux Γ 0 (p : formula (L + consts C)) = p^Γ.length :=
by simp[formula_elim_coe, formula.pow_eq, show ∀ x, Γ.length + x = x + Γ.length, from λ x, add_comm (list.length Γ) x]

@[reducible] def shifting : ℕ → term L :=
λ x, if x ≤ Γ.length + b then if x = Γ.length + b then #b else if b ≤ x then #(x + 1) else #x else #x

variables {Γ}

lemma term_elim_rew (b : ℕ) (t : term (L + consts C)) (hΓ : symbols_aux t ⊆ Γ) :
  (elim_aux Γ b t).rew (shifting Γ b) = elim_aux Γ (b + 1) t :=
begin
  induction t,
  case var : n
  { simp, have C : n < b ∨ n = b ∨ b < n, exact trichotomous n b,
    rcases C with (lt | rfl | lt),
    { simp[lt, nat.lt.step lt, show ¬b ≤ n, from not_le.mpr lt], rintros h rfl, simp at lt, contradiction  },
    { simp[shifting] },
    { simp[lt, show ¬n < b + 1, by simp[nat.lt_succ_iff.symm, ←nat.add_one, lt], show ¬ n < b, from asymm lt, show ¬ n ≤ b, from not_le.mpr lt] } },
  case app : n f v IH
  { rcases f,
    { simp at hΓ ⊢, ext i, refine IH i (set.subset.trans (list.ss_Sup _ i) hΓ) },
    { rcases n,
      { simp[shifting] at hΓ ⊢,
        have : consts_to_var Γ f < Γ.length, from consts_to_var_lt_Γ_of_mem hΓ,
        simp[le_of_lt this, ne_of_lt this, add_assoc] },  { rcases f } } }
end

lemma formula_elim_rew (b : ℕ) (p : formula (L + consts C)) (hΓ : ∀ t ∈ p, symbols_aux t ⊆ Γ):
  (formula_elim_aux Γ b p).rew (shifting Γ b) = formula_elim_aux Γ (b + 1) p :=
begin
  induction p generalizing b,
  case verum { simp },
  case app : n r v { rcases r; simp, { funext i, exact term_elim_rew b (v i) (hΓ (v i) (by {simp, refine ⟨i, by simp⟩ })) }, { rcases r } },
  case equal : t u { simp, refine ⟨term_elim_rew b t (hΓ t (by simp)), term_elim_rew b u (hΓ u (by simp))⟩ },
  case imply : p q IHp IHq { simp, refine ⟨IHp (λ t mem, hΓ t (by simp[mem])) b, IHq (λ t mem, hΓ t (by simp[mem])) b⟩ },
  case neg : p IH { simp, exact IH (λ t mem, hΓ t (by simp[mem])) b },
  case fal : p IH
  { have : (shifting Γ b : ℕ → term L)^1 = shifting Γ (b + 1),
    { funext x, simp[rewriting_sf_itr.pow_eq', shifting], rcases x; simp[←nat.add_one, ←add_assoc, show 0 ≠ Γ.length + b + 1, by omega] },
    simp[this], 
    exact IH (λ t mem, hΓ t (by simp[mem])) (b + 1) }
end

lemma formula_elim_equiv_self (T) (p : formula L) : T ⊢ formula_elim Γ ↑p ⟷ p :=
by simp[formula_elim]

def prf' (L : language) := Σ (T : theory L) (k : ℕ) (p : formula L), T^k ⟹ p

variables (Γ)

private lemma term_elim_aux_rew (t u : term (L + consts C)) (s : ℕ) :
  elim_aux Γ s (t.rew ı[s ⇝ u]) = (elim_aux Γ (s + 1) t).rew ı[s ⇝ elim_aux Γ s u] :=
begin
  induction t,
  case var : n { simp, have : n < s ∨ n = s ∨ s < n, exact trichotomous n s,
    rcases this with (lt | rfl | lt),
    { simp[lt, show n < s + 1, from nat.lt.step lt] },
    { simp },
    { cases n, { simp at lt, contradiction },
      simp[←nat.add_one, lt, show ¬n < s, by omega, show s < Γ.length + (n + 1), by omega] } },
  case app : n f v IH
  { rcases f,
    { simp, funext i, exact IH i },
    { rcases n,
      { simp[←add_assoc, show s < consts_to_var Γ f + s + 1, by omega] }, { rcases f } } }
end

private lemma elim_aux_succ_pow (t : term (L + consts C)) (s : ℕ) (k : ℕ) :
  (elim_aux Γ s t)^k =  elim_aux Γ (s + k) (t^k) :=
begin
  induction t,
  case var : n { simp[add_assoc] },
  case app : n f v IH
  { rcases f,
    { simp, funext i, exact IH i },
    { rcases n, { simp[add_assoc] }, { rcases f } } }
end

private lemma elim_aux_succ_pow' (t : term (L + consts C)) (s : ℕ) (k : ℕ) :
  (elim_aux Γ s t)^k =  elim_aux Γ (s + k) (t^k) :=
begin
  induction t,
  case var : n { simp[add_assoc] },
  case app : n f v IH
  { rcases f,
    { simp, funext i, exact IH i },
    { rcases n, { simp[add_assoc] }, { rcases f } } }
end

private lemma  formula_elim_aux_rew (p : formula (L + consts C)) (u : term (L + consts C)) (s : ℕ) :
  formula_elim_aux Γ s (p.rew ı[s ⇝ u]) = (formula_elim_aux Γ (s + 1) p).rew ı[s ⇝ elim_aux Γ s u] :=
begin
  induction p generalizing s u,
  case verum { simp },
  case app : n r v { rcases r, { simp[term_elim_aux_rew] }, { rcases r } },
  case equal : t u { simp[term_elim_aux_rew] },
  case imply : p q IH_p IH_q { simp, exact ⟨IH_p s u, IH_q s u⟩ },
  case neg : p IH { simp, exact IH s u },
  case fal : p IH { simp[subst_pow, elim_aux_succ_pow], exact IH (s + 1) (u^1) },  
end

private lemma term_elim_aux_succ_pow_aux (t : term (L + consts C)) (s k : ℕ) :
  (elim_aux Γ s t).rew ((λ x, #(x + k))^s) =  elim_aux Γ (s + k) (t.rew ((λ x, #(x + k))^s)) :=
begin
  induction t generalizing s k,
  case var : n
  { simp, have : n < s ∨ s ≤ n, exact lt_or_ge n s, 
    rcases this; simp[this],
    { simp[show n < s + k, from nat.lt_add_right n s k this] },
    { simp[show ¬n < s, from not_lt.mpr this, show n - s + k + s = n + k, by omega, show s ≤ Γ.length + n, from le_add_left this],
      show Γ.length + n - s + k + s = Γ.length + (n + k), omega } },
  case app : n f v IH
  { rcases f,
    { simp, funext i, exact IH i s k },
    { rcases n, { simp, omega }, { rcases f } } }
end

private lemma formula_elim_aux_succ_pow_aux (p : formula (L + consts C)) (s k : ℕ) :
  (formula_elim_aux Γ s p).rew ((λ x, #(x + k))^s) =  formula_elim_aux Γ (s + k) (p.rew ((λ x, #(x + k))^s)) :=
begin
  induction p generalizing s k,
  case app : n r v
  { rcases r, { simp, funext i, exact term_elim_aux_succ_pow_aux Γ (v i) s k }, { rcases r } },
  case equal : t u { simp, exact ⟨term_elim_aux_succ_pow_aux Γ t s k, term_elim_aux_succ_pow_aux Γ u s k⟩ },
  case verum { simp },
  case imply : p q IH_p IH_q { simp* },  
  case neg : p IH { simp* },
  case fal : p IH { simp, simp[rewriting_sf_itr.pow_add, IH (s + 1) k, show s + 1 + k = s + k + 1, by omega] },
end

private lemma formula_elim_aux_succ_pow (p : formula (L + consts C)) (k : ℕ) :
  (formula_elim_aux Γ 0 p)^k =  formula_elim_aux Γ k (p^k) :=
begin
  simp[formula.pow_eq],
  have := formula_elim_aux_succ_pow_aux Γ p 0 k, simp at this, exact this,
end

variables {Γ}

def prf'_to_prf (b : prf' L) : prf L := by { rcases b with ⟨T, k, p, b⟩, refine ⟨T^k, p, b⟩ }

lemma sum_inl_eq_coe_fn {n} (f : L.fn n) : sum.inl f = (↑f : (L + consts C).fn n) := rfl

lemma sum_inl_eq_coe_pr {n} (r : L.pr n) : sum.inl r = (↑r : (L + consts C).pr n) := rfl

private lemma  eq_axiom4_coe {n} (f : L.fn n) : eq_axiom4 (↑f : (L + consts C).fn n) = ↑(eq_axiom4 f) :=
by simp[eq_axiom4]

private lemma  eq_axiom5_coe {n} (r : L.pr n) : eq_axiom5 (↑r : (L + consts C).pr n) = ↑(eq_axiom5 r) :=
by simp[eq_axiom5]

lemma provable_formula_elim_of_proof_aux : ∀ {T : theory L} {p : formula (L + consts C)} (B : ↑T ⟹ p)
  (hΓ : ∀ (t : term (L + consts C)) (h : t ∈ᵗ B), symbols_aux t ⊆ Γ), T ⊢ formula_elim Γ p :=
begin
  suffices : ∀ (T : theory (L + consts C)) (p : formula (L + consts C)) (k : ℕ) (B : T^k ⟹ p)
    (hΓ : ∀ (t : term (L + consts C)) (h : t ∈ᵗ B), symbols_aux t ⊆ Γ) (T₀ : theory L) (eqn : ↑T₀ = T),
    T₀^k ⊢ formula_elim Γ p,
  { intros T p B hΓ, exact this ↑T p 0 B hΓ T rfl },
  intros T' p' k' B',
  let C : Π (k : ℕ) (p : formula (L + consts C)) (b : T'^k ⟹ p), Prop :=
    (λ k p b, (∀ (t : term (L + consts C)), t ∈ᵗ b → symbols_aux t ⊆ Γ) →
      Π T₀, ↑T₀ = T' → T₀ ^ k ⊢ formula_elim Γ p), 
  refine proof.rec''_on C k' p' B' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  { rintros k p B IH hΓ T rfl,
    simp[formula_elim] at IH ⊢,
    have : T^k ⊢ ∏ formula_elim Γ p, from (generalize (IH (λ t h, hΓ t (by simp[h])) T rfl)),
    have : T^k ⊢ ∏[Γ.length + 1] formula_elim_aux Γ 0 p, from this,
    have : T^k ⊢ ∏[Γ.length + 1] (formula_elim_aux Γ 0 p).rew (shifting Γ 0),
    { have := provable.nfal_rew (λ x, if x = Γ.length + 0 then #0 else if 0 ≤ x then #(x + 1) else #x) ⨀ this,
      simp only [nat.lt_succ_iff] at this, exact this },
    simp[formula_elim_rew 0 p (λ t h, hΓ t (by { simp, exact proof.mem_trans h (by simp) }))] at this,
    exact this },
  { rintros k p q B₁ B₂ IH₁ IH₂ hΓ T rfl,
    have IH₁ : T^k ⊢ formula_elim Γ (p ⟶ q), from IH₁ (λ t h, hΓ t (by simp[h])) T rfl,
    have IH₂ : T^k ⊢ formula_elim Γ p, from IH₂ (λ t h, hΓ t (by simp[h])) T rfl,
    simp[formula_elim] at IH₁ IH₂ ⊢,
    exact (provable.nfal_K _ _ _ ⨀ IH₁ ⨀ IH₂) },
  { rintros k p mem hΓ T rfl, simp[formula_elim] at mem ⊢, 
    have : T^k ⊢ ∏[Γ.length] formula_elim_aux Γ 0 p,
    { have : ∃ (p' ∈ T), p = ↑p' ^ k, from theory_mem_coe_pow_iff.mp mem, rcases this with ⟨p, p_mem, rfl⟩,
      rw ← coe_pow_formula, simp[-coe_pow_formula],
      show T^k ⊢ ∏[Γ.length] (p ^ k) ^ Γ.length,
      have lmm₁ : T^k ⊢ p^k ⟶ (∏[Γ.length] (p^k)^Γ.length), from (axiomatic_classical_logic'.iff_equiv.mp nfal_pow_equiv_self).2, 
      have lmm₂ : T^k ⊢ p^k, exact sf_itr_sf_itr.mpr (by_axiom' p_mem),
      exact lmm₁ ⨀ lmm₂ },
    exact this },
  { rintros,  refine generalize_itr _, simp[formula_elim] },
  { rintros, refine generalize_itr _, simp[formula_elim] },
  { rintros, refine generalize_itr _, simp[formula_elim] },
  { rintros, refine generalize_itr _, simp[formula_elim] },
  { rintros, refine generalize_itr _, simp[formula_elim, formula_elim_aux_rew] },
  { rintros, refine generalize_itr _, simp[formula_elim] },
  { rintros, refine generalize_itr _, simp[formula_elim, ←formula_elim_aux_succ_pow] },
  { rintros, refine generalize_itr _, simp[formula_elim] },
  { rintros, refine generalize_itr _, simp[formula_elim] },
  { rintros, refine generalize_itr _, simp[formula_elim] },
  { rintros k m f hΓ T rfl, refine generalize_itr _, simp[formula_elim],
    rcases f,
    { simp[sum_inl_eq_coe_fn, eq_axiom4_coe] },
    { cases m, { simp[eq_axiom4] }, { rcases f } } },
  { rintros k m r hΓ T rfl, refine generalize_itr _, simp[formula_elim],
    rcases r,
    { simp[sum_inl_eq_coe_pr, eq_axiom5_coe] },
    { rcases r } }
end

noncomputable def consts_of {T : theory (L + consts C)} {p : formula (L + consts C)} (b : T ⟹ p) : list C :=
(list.map symbols_aux ((proof.term_mem_finite b).to_finset.to_list)).join.dedup

lemma consts_list_spec {T : theory (L + consts C)} {p : formula (L + consts C)}
  (b : T ⟹ p) (t : term (L + consts C)) (h : t ∈ᵗ b) : symbols_aux t ⊆ consts_of b := λ c mem,
by simp[consts_of]; refine ⟨t, h, mem⟩

theorem provable_formula_elim_of_proof {T : theory L} {p : formula (L + consts C)} (b : ↑T ⟹ p) :
  T ⊢ formula_elim (consts_of b) p :=
provable_formula_elim_of_proof_aux b (consts_list_spec b)

theorem provable_iff {T : theory L} {p : formula L} :
  ↑T ⊢ (↑p : formula (L + consts C)) ↔ T ⊢ p:=
⟨begin
  rintros ⟨b⟩,
  have lmm₁ : T ⊢ ∏[(consts_of b).length] p^(consts_of b).length,
  { have := provable_formula_elim_of_proof b, 
    simp[formula_elim] at this, exact this },
  have lmm₂ : T ⊢ (∏[(consts_of b).length] p^(consts_of b).length) ⟶ p, from (axiomatic_classical_logic'.iff_equiv.mp nfal_pow_equiv_self).1,
  exact lmm₂ ⨀ lmm₁
end, provability⟩

end add_consts

end language

end fopl

