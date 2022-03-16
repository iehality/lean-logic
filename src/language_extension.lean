import translation

universes u v

namespace fopl
open term formula

variables {L L₁ L₂ L₃ : language.{u}}
local infix ` ≃₀ `:50 := ((≃) : term L → term L → formula L)
local infix ` ≃₁ `:50 := ((≃) : term L₁ → term L₁ → formula L₁)
local infix ` ≃₂ `:50 := ((≃) : term L₂ → term L₂ → formula L₂)

namespace language
variables {C : Type u} [decidable_eq C]

namespace extension

lemma sum_inl_eq_coe_fn {n} (f : L.fn n) : sum.inl f = (↑f : (L + consts C).fn n) := rfl

lemma sum_inl_eq_coe_pr {n} (r : L.pr n) : sum.inl r = (↑r : (L + consts C).pr n) := rfl

lemma term.exists_of_le_coe {t : term (L + consts C)} {u : term L} (le : t ≤ (↑u : term (L + consts C))) :
  ∃ t₀ : term L, t = ↑t₀ :=
begin
  induction u generalizing t,
  case var : n
  { rcases eq_or_lt_of_le le with (rfl | lt), { refine ⟨#n, rfl⟩ }, simp at lt, contradiction },
  case app : n f v IH
  { rcases eq_or_lt_of_le le with (rfl | lt),
    { refine ⟨app f v, rfl⟩ },
    { simp at lt, rcases lt with ⟨i, le⟩, exact IH i le } }
end

lemma formula.exists_of_mem_coe {t : term (L + consts C)} {p : formula L} (mem : t ∈ (↑p : formula (L + consts C))) :
  ∃ t₀ : term L, t = ↑t₀ :=
begin
  induction p generalizing t,
  case app : n r v { simp at mem, rcases mem with ⟨i, le⟩, exact term.exists_of_le_coe le },
  case equal : t₁ t₂ { simp at mem, rcases mem with (le | le), { exact term.exists_of_le_coe le }, { exact term.exists_of_le_coe le } },
  case verum { simp at mem, contradiction },
  case imply : p q IH_p IH_q { simp at mem, rcases mem, { exact IH_p mem }, { exact IH_q mem } },
  case neg : p IH { simp at mem, exact IH mem },
  case fal : p IH { simp at mem, exact IH mem }
end

end extension

@[simp] def consts_of_t : term (L + consts C) → list C
| (#n)                      := []
| (@term.app _ n f v)       :=
  have h : ∀ i, (v i).complexity < (⨆ᶠ i, (v i).complexity) + 1, from λ i, nat.lt_succ_iff.mpr (le_fintype_sup (λ i, (v i).complexity) i),
  by { cases f, { exact list.Sup (λ i, consts_of_t (v i)) }, { cases n, exact [f], rcases f, } }

noncomputable def consts_of_p (p : formula (L + consts C)) : list C :=
(list.map consts_of_t ((formula.mem_finite p).to_finset.to_list)).join.dedup

@[simp] lemma consts_of_t_coe_eq_nil (t : term L) : consts_of_t (↑t : term (L + consts C)) = [] :=
by { simp[list.eq_nil_iff_forall_not_mem], induction t,
     case var { simp },
     case app : n f v IH
     { simp[←extension.sum_inl_eq_coe_fn, list.eq_nil_iff_forall_not_mem], intros c i, exact IH i c } }

@[simp] lemma consts_of_p_coe_eq_nil (p : formula L) : consts_of_p (↑p : formula (L + consts C)) = [] :=
by { simp[list.eq_nil_iff_forall_not_mem, consts_of_p], intros c t mem, rcases extension.formula.exists_of_mem_coe mem with ⟨t, rfl⟩, simp }


namespace add_consts
open language_translation language_translation_coe extension
  proof provable axiomatic_classical_logic' axiomatic_classical_logic


variables (Γ : list C) (b : ℕ) 

def consts_to_var : C → ℕ := λ c, (list.index_of c Γ)

lemma consts_to_var_lt_Γ_of_mem {Γ : list C} {c : C} (mem : c ∈ Γ) : consts_to_var Γ c < Γ.length :=
by { simp[consts_to_var], exact list.index_of_lt_length.mpr mem }

@[simp] def elim_aux_t : term (L + consts C) → term L
| (#n)                      := if n < b then #n else #(Γ.length + n)
| (@term.app _ n f v)       :=
    by { cases f, { exact app f (λ i, elim_aux_t (v i)) },
         { rcases n, { exact #(consts_to_var Γ f + b) }, { rcases f } } }

@[simp] def elim_aux_f : ℕ → formula (L + consts C) → formula L
| b (app r v)                          := by { rcases r, { refine app r (λ i, elim_aux_t Γ b (v i)) }, { rcases r } }
| b ((t₁ : term (L + consts C)) ≃ t₂)  := elim_aux_t Γ b t₁ ≃ elim_aux_t Γ b t₂
| b ⊤                                  := ⊤
| b (p ⟶ q)                            := elim_aux_f b p ⟶ elim_aux_f b q
| b (⁻p)                               := ⁻elim_aux_f b p
| b (∏ p)                              := ∏ elim_aux_f (b + 1) p

def var_to_consts : ℕ → term (consts C) := λ n, if h : n < Γ.length then Γ.nth_le n h else #(n - Γ.length)

def formula_elim : formula (L + consts C) → formula L := λ p, ∏[Γ.length] elim_aux_f Γ 0 p

@[simp] lemma term_elim_coe : ∀ (t : term L),
  elim_aux_t Γ b (t : term (L + consts C)) = t.rew (λ x, if x < b then #x else #(Γ.length + x))
| (#n)                      := by simp
| (@term.app _ n f v) := by { simp[coe_fn₁], funext i, exact term_elim_coe (v i) }

lemma formula_elim_coe : ∀ (b : ℕ) (p : formula L),
  elim_aux_f Γ b (p : formula (L + consts C)) = p.rew (λ x, if x < b then #x else #(Γ.length + x))
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
  elim_aux_f Γ 0 (p : formula (L + consts C)) = p^Γ.length :=
by simp[formula_elim_coe, formula.pow_eq, show ∀ x, Γ.length + x = x + Γ.length, from λ x, add_comm (list.length Γ) x]

@[reducible] def shifting : ℕ → term L :=
λ x, if x ≤ Γ.length + b then if x = Γ.length + b then #b else if b ≤ x then #(x + 1) else #x else #x

variables {Γ}

lemma elim_aux_t_rew (b : ℕ) (t : term (L + consts C)) (hΓ : consts_of_t t ⊆ Γ) :
  (elim_aux_t Γ b t).rew (shifting Γ b) = elim_aux_t Γ (b + 1) t :=
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

lemma elim_aux_f_rew (b : ℕ) (p : formula (L + consts C)) (hΓ : ∀ t ∈ p, consts_of_t t ⊆ Γ):
  (elim_aux_f Γ b p).rew (shifting Γ b) = elim_aux_f Γ (b + 1) p :=
begin
  induction p generalizing b,
  case verum { simp },
  case app : n r v { rcases r; simp, { funext i, exact elim_aux_t_rew b (v i) (hΓ (v i) (by {simp, refine ⟨i, by simp⟩ })) }, { rcases r } },
  case equal : t u { simp, refine ⟨elim_aux_t_rew b t (hΓ t (by simp)), elim_aux_t_rew b u (hΓ u (by simp))⟩ },
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

private lemma elim_aux_t_subst (t u : term (L + consts C)) (s : ℕ) :
  elim_aux_t Γ s (t.rew ı[s ⇝ u]) = (elim_aux_t Γ (s + 1) t).rew ı[s ⇝ elim_aux_t Γ s u] :=
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

private lemma elim_aux_t_succ_pow (t : term (L + consts C)) (s : ℕ) (k : ℕ) :
  (elim_aux_t Γ s t)^k =  elim_aux_t Γ (s + k) (t^k) :=
begin
  induction t,
  case var : n { simp[add_assoc] },
  case app : n f v IH
  { rcases f,
    { simp, funext i, exact IH i },
    { rcases n, { simp[add_assoc] }, { rcases f } } }
end

private lemma elim_aux_t_succ_pow' (t : term (L + consts C)) (s : ℕ) (k : ℕ) :
  (elim_aux_t Γ s t)^k =  elim_aux_t Γ (s + k) (t^k) :=
begin
  induction t,
  case var : n { simp[add_assoc] },
  case app : n f v IH
  { rcases f,
    { simp, funext i, exact IH i },
    { rcases n, { simp[add_assoc] }, { rcases f } } }
end

private lemma  elim_aux_f_subst (p : formula (L + consts C)) (u : term (L + consts C)) (s : ℕ) :
  elim_aux_f Γ s (p.rew ı[s ⇝ u]) = (elim_aux_f Γ (s + 1) p).rew ı[s ⇝ elim_aux_t Γ s u] :=
begin
  induction p generalizing s u,
  case verum { simp },
  case app : n r v { rcases r, { simp[elim_aux_t_subst] }, { rcases r } },
  case equal : t u { simp[elim_aux_t_subst] },
  case imply : p q IH_p IH_q { simp, exact ⟨IH_p s u, IH_q s u⟩ },
  case neg : p IH { simp, exact IH s u },
  case fal : p IH { simp[subst_pow, elim_aux_t_succ_pow], exact IH (s + 1) (u^1) },  
end

private lemma elim_aux_t_succ_pow_aux (t : term (L + consts C)) (s k : ℕ) :
  (elim_aux_t Γ s t).rew ((λ x, #(x + k))^s) =  elim_aux_t Γ (s + k) (t.rew ((λ x, #(x + k))^s)) :=
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

private lemma elim_aux_f_succ_pow_aux (p : formula (L + consts C)) (s k : ℕ) :
  (elim_aux_f Γ s p).rew ((λ x, #(x + k))^s) =  elim_aux_f Γ (s + k) (p.rew ((λ x, #(x + k))^s)) :=
begin
  induction p generalizing s k,
  case app : n r v
  { rcases r, { simp, funext i, exact elim_aux_t_succ_pow_aux Γ (v i) s k }, { rcases r } },
  case equal : t u { simp, exact ⟨elim_aux_t_succ_pow_aux Γ t s k, elim_aux_t_succ_pow_aux Γ u s k⟩ },
  case verum { simp },
  case imply : p q IH_p IH_q { simp* },  
  case neg : p IH { simp* },
  case fal : p IH { simp, simp[rewriting_sf_itr.pow_add, IH (s + 1) k, show s + 1 + k = s + k + 1, by omega] },
end

private lemma elim_aux_f_succ_pow (p : formula (L + consts C)) (k : ℕ) :
  (elim_aux_f Γ 0 p)^k =  elim_aux_f Γ k (p^k) :=
begin
  simp[formula.pow_eq],
  have := elim_aux_f_succ_pow_aux Γ p 0 k, simp at this, exact this,
end

variables {Γ}

def prf'_to_prf (b : prf' L) : prf L := by { rcases b with ⟨T, k, p, b⟩, refine ⟨T^k, p, b⟩ }

private lemma  eq_axiom4_coe {n} (f : L.fn n) : eq_axiom4 (↑f : (L + consts C).fn n) = ↑(eq_axiom4 f) :=
by simp[eq_axiom4]

private lemma  eq_axiom5_coe {n} (r : L.pr n) : eq_axiom5 (↑r : (L + consts C).pr n) = ↑(eq_axiom5 r) :=
by simp[eq_axiom5]

lemma provable_formula_elim_of_proof_aux : ∀ {T : theory L} {p : formula (L + consts C)} (B : ↑T ⟹ p)
  (hΓ : ∀ (t : term (L + consts C)) (h : t ∈ᵗ B), consts_of_t t ⊆ Γ), T ⊢ formula_elim Γ p :=
begin
  suffices : ∀ (T : theory (L + consts C)) (p : formula (L + consts C)) (k : ℕ) (B : T^k ⟹ p)
    (hΓ : ∀ (t : term (L + consts C)) (h : t ∈ᵗ B), consts_of_t t ⊆ Γ) (T₀ : theory L) (eqn : ↑T₀ = T),
    T₀^k ⊢ formula_elim Γ p,
  { intros T p B hΓ, exact this ↑T p 0 B hΓ T rfl },
  intros T' p' k' B',
  let C : Π (k : ℕ) (p : formula (L + consts C)) (b : T'^k ⟹ p), Prop :=
    (λ k p b, (∀ (t : term (L + consts C)), t ∈ᵗ b → consts_of_t t ⊆ Γ) →
      Π T₀, ↑T₀ = T' → T₀ ^ k ⊢ formula_elim Γ p), 
  refine proof.rec''_on C k' p' B' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  { rintros k p B IH hΓ T rfl,
    simp[formula_elim] at IH ⊢,
    have : T^k ⊢ ∏ formula_elim Γ p, from (generalize (IH (λ t h, hΓ t (by simp[h])) T rfl)),
    have : T^k ⊢ ∏[Γ.length + 1] elim_aux_f Γ 0 p, from this,
    have : T^k ⊢ ∏[Γ.length + 1] (elim_aux_f Γ 0 p).rew (shifting Γ 0),
    { have := provable.nfal_rew (λ x, if x = Γ.length + 0 then #0 else if 0 ≤ x then #(x + 1) else #x) ⨀ this,
      simp only [nat.lt_succ_iff] at this, exact this },
    simp[elim_aux_f_rew 0 p (λ t h, hΓ t (by { simp, exact proof.mem_trans h (by simp) }))] at this,
    exact this },
  { rintros k p q B₁ B₂ IH₁ IH₂ hΓ T rfl,
    have IH₁ : T^k ⊢ formula_elim Γ (p ⟶ q), from IH₁ (λ t h, hΓ t (by simp[h])) T rfl,
    have IH₂ : T^k ⊢ formula_elim Γ p, from IH₂ (λ t h, hΓ t (by simp[h])) T rfl,
    simp[formula_elim] at IH₁ IH₂ ⊢,
    exact (provable.nfal_K _ _ _ ⨀ IH₁ ⨀ IH₂) },
  { rintros k p mem hΓ T rfl, simp[formula_elim] at mem ⊢, 
    have : T^k ⊢ ∏[Γ.length] elim_aux_f Γ 0 p,
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
  { rintros, refine generalize_itr _, simp[formula_elim, elim_aux_f_subst] },
  { rintros, refine generalize_itr _, simp[formula_elim] },
  { rintros, refine generalize_itr _, simp[formula_elim, ←elim_aux_f_succ_pow] },
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
(list.map consts_of_t ((proof.term_mem_finite b).to_finset.to_list)).join.dedup

lemma consts_list_spec {T : theory (L + consts C)} {p : formula (L + consts C)}
  (b : T ⟹ p) (t : term (L + consts C)) (h : t ∈ᵗ b) : consts_of_t t ⊆ consts_of b := λ c mem,
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

theorem consistent_iff {T : theory L} :
  (↑T : theory (L + consts C)).consistent ↔ T.consistent :=
begin
  have : (↑T : theory (L + consts C)) ⊢ ⊥ ↔ T ⊢ ⊥,
  { have : (↑T : theory (L + consts C)) ⊢ ↑(⊥ : formula L) ↔ T ⊢ ⊥, from provable_iff,
    simp at this, exact this },
  simp[theory.consistent_iff_bot, this],  
end

end add_consts

namespace consts_pelimination
open language_translation language_translation_coe extension
  proof provable axiomatic_classical_logic' axiomatic_classical_logic

variables (Γ : list C) (b : ℕ) 

def consts_to_var (Γ : list C) : {c : C | c ∈ Γ} → ℕ := λ ⟨c, _⟩, (list.index_of c Γ : ℕ)

lemma consts_to_var_lt_Γ_of_mem {Γ : list C} {c : C} (mem : c ∈ Γ) : consts_to_var Γ ⟨c, mem⟩ < Γ.length :=
by { simp[consts_to_var], exact list.index_of_lt_length.mpr mem }

@[simp] def pelim_aux_t : term (L + consts C) → term (L + consts C)
| (#n)                      := if n < b then #n else #(Γ.length + n)
| (@term.app _ n f v)       :=
    by { cases f, { exact app ↑f (λ i, pelim_aux_t (v i)) },
         { rcases n, { by_cases h : f ∈ Γ, { exact #(consts_to_var Γ ⟨f, h⟩ + b) },
         { exact app ↑f finitary.nil } }, { rcases f } } }

@[simp] def pelim_aux_f : ℕ → formula (L + consts C) → formula (L + consts C)
| b (app r v)                          := by { rcases r, { refine app ↑r (λ i, pelim_aux_t Γ b (v i)) }, { rcases r } }
| b ((t₁ : term (L + consts C)) ≃ t₂)  := pelim_aux_t Γ b t₁ ≃ pelim_aux_t Γ b t₂
| b ⊤                                  := ⊤
| b (p ⟶ q)                            := pelim_aux_f b p ⟶ pelim_aux_f b q
| b (⁻p)                               := ⁻pelim_aux_f b p
| b (∏ p)                              := ∏ pelim_aux_f (b + 1) p

def formula_elim : formula (L + consts C) → formula (L + consts C) := λ p, ∏[Γ.length] pelim_aux_f Γ 0 p

private lemma pelim_aux_t_pow_aux (t : term (L + consts C)) (i s k : ℕ) (le : s ≤ i) :
  pelim_aux_t Γ (i + k) (t.rew ((λ x, #(x + k))^s)) = (pelim_aux_t Γ i t).rew ((λ x, #(x + k)) ^ s) :=
begin
  induction t generalizing s k,
  case var : n
  { simp, have hn : n < s ∨ s ≤ n, exact lt_or_ge n s, 
    rcases hn; simp[hn],
    { simp[hn, show n < i, from (gt_of_ge_of_gt le hn), show n < i + k, from nat.lt_add_right _ _ _ (gt_of_ge_of_gt le hn)] },
    { simp[show n - s + k + s = n + k, by omega],
      have hi : n < i ∨ i ≤ n, exact lt_or_ge n i,
      rcases hi, { simp[hi, hn], omega },
      { simp[show ¬n < i, from not_lt.mpr hi, show s ≤ Γ.length + n, from le_add_left hn], omega } } },
  case app : n f v IH
  { rcases f,
    { simp, funext i, exact IH i s k le },
    { rcases n,
      { by_cases mem : f ∈ Γ; simp[mem, le],
        { simp[show s ≤ consts_to_var Γ ⟨f, mem⟩ + i, from le_add_left le], omega } }, { rcases f } } }
end

private lemma pelim_aux_t_pow (t : term (L + consts C)) (i k : ℕ) :
  pelim_aux_t Γ (i + k) (t^k) = (pelim_aux_t Γ i t)^k :=
by { have :=  pelim_aux_t_pow_aux Γ t i 0 k (by simp), simp at this,
     simp[term.pow_eq], exact this }

lemma pelim_aux_t_subst (t u : term (L + consts C)) {s m : ℕ} (le : m ≤ s) :
  pelim_aux_t Γ s (t.rew ı[m ⇝ u]) = (pelim_aux_t Γ (s + 1) t).rew ı[m ⇝ pelim_aux_t Γ s u] :=
begin
  induction t generalizing s m,
  case var : n { simp,
    have hn : n < m ∨ n = m ∨ m < n, from trichotomous n m, rcases hn with (hn | rfl | hn),
    { simp[hn, show n < s, from gt_of_ge_of_gt le hn, show n < s + 1, from nat.lt.step (gt_of_ge_of_gt le hn)] },
    { simp[show n < s + 1, from nat.lt_succ_iff.mpr le] },
    { simp[hn], rcases n;simp[←nat.add_one] at hn ⊢, { contradiction },
      { have hn' : n < s ∨ s ≤ n, from lt_or_ge n s, rcases hn' with (hn' | hn'), 
      { simp[hn', hn] }, { simp[show ¬n < s, from not_lt.mpr hn', show m < Γ.length + (n + 1), from nat.lt_add_left m _ _ hn] } } } },
  case app : n f v IH {
    rcases f,
    { simp, funext i, exact IH i le },
    { cases n,
      { by_cases mem : f ∈ Γ; simp[mem, le],
        { simp[show m < consts_to_var Γ ⟨f, mem⟩ + (s + 1), by omega] } }, { rcases f } } }
end

lemma pelim_aux_t_subst' (t u : term (L + consts C)) {s : ℕ} :
  pelim_aux_t Γ s (t.rew ı[s ⇝ u]) = (pelim_aux_t Γ (s + 1) t).rew ı[s ⇝ pelim_aux_t Γ s u] :=
pelim_aux_t_subst Γ t u (by refl) 

private def pelimination_aux : formula_homomorphism (L + consts C) (L + consts C) :=
{ to_fun := pelim_aux_f Γ,
  map_verum := by simp,
  map_imply := by simp,
  map_neg := by simp,
  map_univ := by simp }

lemma pelimination_aux_app (p : formula (L + consts C)) (k) : pelimination_aux Γ k p = pelim_aux_f Γ k p := rfl

def pelimination : (L + consts C) ↝ (L + consts C) :=
formula_homonorphism.mk_translation (pelimination_aux Γ)
  (λ n r v l s k le, by { rcases r,
      { simp[pelimination_aux_app], funext i, exact pelim_aux_t_pow_aux Γ (v i) l s k le },
      { rcases r } })
  (λ t u l s k le, by { simp[pelimination_aux_app], refine ⟨pelim_aux_t_pow_aux Γ t l s k le, pelim_aux_t_pow_aux Γ u l s k le⟩ })

lemma pelimination_app (p : formula (L + consts C)) (k) : pelimination Γ k p = pelim_aux_f Γ k p := rfl

def pelimination' : term_formula_translation (L + consts C) (L + consts C) :=
{ p := pelimination Γ,
  t := pelim_aux_t Γ,
  chr := λ n, id,
  equal := λ t u k, by simp[pelimination_app],
  app := λ k n r v, by { rcases r, { simp, refl }, { rcases r } },
  map_pow := λ t s, by { exact pelim_aux_t_pow Γ t s 1 } }

@[simp] lemma pelimination'_t_eq_pelim_aux_t (t : term (L + consts C)) (s : ℕ) :
  (pelimination' Γ).t s t = pelim_aux_t Γ s t := rfl

lemma pelimination'_subst (p : formula (L + consts C)) (t) (s : ℕ) :
  (pelimination' Γ).p s (p.rew ı[s ⇝ t]) = ((pelimination' Γ).p (s + 1) p).rew ı[s ⇝ pelim_aux_t Γ s t] :=
term_formula_translation.tr_subst_of_subst (pelimination' Γ) (pelim_aux_t_subst Γ) p t s s (by refl)

instance pelimination_conservative : (pelimination Γ : (L + consts C) ↝ (L + consts C)).conservative :=
term_formula_translation.conservative_of (pelimination' Γ : term_formula_translation (L + consts C) (L + consts C))
(λ t u s m le, by { simp[pelimination', pelim_aux_t_subst Γ t u le], })
  (λ s n f T k, by { rcases f,
    { simp[eq_axiom4, pelimination'], 
      simp[pelimination_app, show ∀ i : fin n, ↑i < s + k + 2 * n, { rintros ⟨i, lt⟩, simp, omega },
      show ∀ i : fin n, n + i < s + k + 2 * n, { rintros ⟨i, lt⟩, simp, omega } ], exact function_ext _ },
    { cases n,
      { simp[eq_axiom4, pelimination'], simp[pelimination_app] }, { rcases f } } })
  (λ s n r T k, by { rcases r,
    { simp[eq_axiom5, pelimination'],
    simp[pelimination_app, show ∀ i : fin n, ↑i < s + k + 2 * n, { rintros ⟨i, lt⟩, simp, omega },
      show ∀ i : fin n, n + i < s + k + 2 * n, { rintros ⟨i, lt⟩, simp, omega } ], exact predicate_ext _ },
    { rcases r } })

def disjoint (p : formula (L + consts C)) : Prop := ∀ c ∈ Γ, c ∉ consts_of_p p 

lemma pelim_aux_t_eq_pow_of_disjoint_aux (t : term (L + consts C)) (h : ∀ c ∈ Γ, c ∉ consts_of_t t) (s : ℕ) :
  pelim_aux_t Γ s t = t.rew ((λ x, #(Γ.length + x))^s) :=
begin
  induction t generalizing s,
  case var { simp, by_cases C : t < s; simp[C], { simp[show s ≤ t, from not_lt.mp C], omega } },
  case app : n f v IH
  { rcases f,
    { simp, refine ⟨rfl, _⟩, funext i, exact IH i (λ c mem, by { have := h c mem, simp at this, exact this i }) s },
    { rcases n,
      { have : f ∉ Γ, { intros mem, have := h f mem, simp [consts_of_t] at this, contradiction }, simp[this], refl }, { rcases f } } }
end

lemma pelimination_eq_pow_aux_of_disjoint (p : formula (L + consts C)) (h : disjoint Γ p) (s : ℕ) :
  pelimination Γ s p = p.rew ((λ x, #(Γ.length + x))^s) :=
begin
  induction p generalizing s,
  case app : n r v { rcases r,
    { simp[pelimination_app], refine ⟨rfl, _⟩, funext i,
      exact pelim_aux_t_eq_pow_of_disjoint_aux Γ (v i) (λ c mem, by { have := h c mem, simp[consts_of_p] at this, refine this (v i) i (by refl) }) s },
    { rcases r } },
  case equal : t u
  { simp[pelimination_app],
    refine ⟨pelim_aux_t_eq_pow_of_disjoint_aux Γ t (λ c mem, by { have := h c mem, simp[consts_of_p] at this, refine this t (by simp) }) s,
      pelim_aux_t_eq_pow_of_disjoint_aux Γ u (λ c mem, by { have := h c mem, simp[consts_of_p] at this, refine this u (by simp) }) s⟩,   },
  case verum { simp },
  case imply : p q IH_p IH_q
  { simp, refine
    ⟨IH_p (λ c mem mem_p, by { have := h c mem, simp[consts_of_p] at this mem_p, rcases mem_p with ⟨t, ht, mem_t⟩, exact this t (by simp[ht]) mem_t }) s,
     IH_q (λ c mem mem_p, by { have := h c mem, simp[consts_of_p] at this mem_p, rcases mem_p with ⟨t, ht, mem_t⟩, exact this t (by simp[ht]) mem_t }) s⟩ },
  case neg : p IH
  { simp, refine IH (λ c mem mem_p, by { have := h c mem, simp[consts_of_p] at this mem_p, rcases mem_p with ⟨t, ht, mem_t⟩, exact this t (by simp[ht]) mem_t }) s },
  case fal : p IH { simp[rewriting_sf_itr.pow_add], exact IH (λ c mem mem_p, by { have := h c mem, simp[consts_of_p] at this mem_p, rcases mem_p with ⟨t, ht, mem_t⟩,refine this t ht mem_t }) (s + 1) },
end

lemma pelimination_eq_pow_of_disjoint (p : formula (L + consts C)) (h : disjoint Γ p) :
  pelimination Γ 0 p = p^Γ.length :=
by { have := pelimination_eq_pow_aux_of_disjoint Γ p h 0, simp at this,
     simp[formula.pow_eq, show ∀ x, x + Γ.length = Γ.length + x, from λ x, add_comm _ _], exact this }

theorem provable_pelimination_of_disjoint (T : theory (L + consts C)) (p : formula (L + consts C))
  (disj : ∀ p ∈ T, disjoint Γ p) : T ⊢ p → T ⊢ ∏[Γ.length] (pelimination' Γ).p 0 p := λ b,
begin
  have lmm₁ : tr_theory (pelimination Γ) 0 T ⊢ (pelimination Γ) 0 p, from translation.provability (pelimination Γ) T p 0 b,
  have : tr_theory (pelimination Γ) 0 T = T^Γ.length,
  { ext q, simp[tr_theory, theory_sf_itr_eq], split,
    { rintros ⟨q, q_mem, rfl⟩, refine ⟨q, q_mem, pelimination_eq_pow_of_disjoint Γ q (disj q q_mem)⟩ },
    { rintros ⟨q, q_mem, rfl⟩, refine ⟨q, q_mem, pelimination_eq_pow_of_disjoint Γ q (disj q q_mem)⟩ } },
  rw this at lmm₁,
  exact generalize_itr lmm₁
end

@[simp] lemma disjoint_coe (p : formula L) : disjoint Γ (↑p : formula (L + consts C)) :=
λ c mem, by simp

lemma pelimination_coe_eq_pow_coe_aux (p : formula L) (s : ℕ) :
  (pelimination' Γ).p s (↑p : formula (L + consts C)) = (↑p : formula (L + consts C)).rew ((λ x, #(Γ.length + x))^s) :=
pelimination_eq_pow_aux_of_disjoint Γ (↑p : formula (L + consts C)) (disjoint_coe Γ p) s

@[simp] lemma pelim_aux_t_consts_of_Γ (c : C) (h : c ∈ Γ) (s : ℕ) :
  (pelim_aux_t Γ s c : term (L + consts C)) = #(Γ.index_of c + s) :=
by simp[consts.coe_def, show (↑(consts.c c) : (L + consts C).fn 0) = sum.inr (consts.c c), from rfl]; simp[consts.c, h]; refl

end consts_pelimination

end language

end fopl

