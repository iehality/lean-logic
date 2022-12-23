import logic lib.tukey

universes u

open_locale logic_symbol

namespace logic
open_locale aclogic
variables {F : Type*} [has_logic_symbol F] [axiomatic_classical_logic F]

namespace Theory

variables {T U : Theory F}

open axiomatic_classical_logic axiomatic_classical_logic'

lemma consistent_of_consistent_ss (h : T.consistent) (ss : U ⊆ T) : U.consistent :=
by { simp[consistent_iff_bot] at h ⊢, intros hU, have : T ⊢ ⊥, from weakening ss hU, contradiction }

private lemma list_set_finite {α} (l : list α) : {a : α | a ∈ l}.finite :=
by { induction l with a l IH, { simp },
  { simp[show {b : α | b = a ∨ b ∈ l} = insert a {b : α | b ∈ l}, by refl], exact set.finite.insert a IH } }

variables (F)

class has_finite_character :=
(finite_character' : ∀ {T : Theory F}, (∀ (s ⊆ T) (f : s.finite), consistent s) → consistent T)

def finite_character_of_finite_provable
  (H : ∀ T p, T ⊢ p → ∃ P : list F, (∀ p, p ∈ P → T p) ∧ ∅ ⊢ P.conjunction ⟶ p) :
  has_finite_character F :=
⟨λ T h, 
  begin
    by_contradiction A,
    have : ∃ (P : list F), (∀ p ∈ P, T p) ∧ ∅ ⊢ P.conjunction ⟶ ⊥, from H _ _ (not_consistent_iff_bot.mp A),
    rcases this with ⟨P, ss, b⟩,
    let s := {p | p ∈ P},
    have : s ⊢ ⊥,
    { have lmm₁ : s ⊢ P.conjunction ⟶ ⊥, from weakening (by simp) b,
      have lmm₂ : s ⊢ P.conjunction, from list_conjunction_provable (λ p h, by_axiom (by simp[s, h])),
      exact lmm₁ ⨀ lmm₂ },
    have : consistent s, from h s ss (by simp[s, list_set_finite]),
    have : ¬s ⊢ ⊥, exact consistent_iff_bot.mp this,
    contradiction
  end⟩

variables {F}

namespace consistent
open has_finite_character
variables [has_finite_character F]

lemma finite_character :
  consistent T ↔ ∀ (s ⊆ T) (f : s.finite), consistent s :=
⟨begin
  intros h,
  by_contradiction A, simp at A,
  rcases A with ⟨s, ss, s_fin, hs⟩,
  have : s ⊢ ⊥, from not_consistent_iff_bot.mp hs,
  have : T ⊢ ⊥, from weakening ss this,
  have : ¬T ⊢ ⊥, from consistent_iff_bot.mp h,
  contradiction
end, finite_character'⟩

lemma tukey_finite_charactor : tukey.finite_charactor (Theory.consistent : Theory F → Prop) :=
λ T, finite_character

lemma finite_character_union (consis : consistent T) :
  consistent (T ∪ U) ↔ ∀ (s ⊆ U) (f : s.finite), consistent (T ∪ s) :=
begin
  rw finite_character, split,
  { intros h s s_ss s_fin,
    rw finite_character, intros s' s'_ss, refine h s'
      (by { have : T ∪ s ⊆ T ∪ U, { simp, exact set.subset_union_of_subset_right s_ss T },
      exact set.subset.trans s'_ss this }) },
  { intros h s s_ss s_fin,
    let u := s ∩ U,
    have lmm : consistent (T ∪ u), from h u (by simp[u]) (by { simp[u], exact set.finite.inter_of_left s_fin U }),
    have ss : s ⊆ T ∪ u, { intros p mem, simp[u], have : p ∈ T ∨ p ∈ U, from s_ss mem, tauto },
    refine consistent_of_consistent_ss lmm ss }
end

lemma of_finite_induction
  (consis : consistent T)
  (H : ∀ (s ⊆ U) (p ∈ U), p ∉ s → s.finite → consistent (T ∪ s) → consistent ((T ∪ s) +{ p })) :
  consistent (T ∪ U) :=
begin
  refine (finite_character_union consis).mpr _,
  suffices : ∀ (s : Theory F), set.finite s → s ⊆ U → (T ∪ s).consistent,
  { intros s ss fin, exact this s fin ss },
  intros s fin,
  refine set.finite.induction_on fin (λ _, by simp[consis]) _,
  intros p s nmem fin consis ss, 
  have : T ∪ insert p s = (T ∪ s) +{ p }, { ext q, simp },
  simp[this],
  exact H s (set.subset.trans (show s ⊆ insert p s, by simp) ss) p (ss (show p ∈ insert p s, by simp)) nmem fin
    (consis (set.subset.trans (show s ⊆ insert p s, by simp) ss))
end

lemma Union_seq (T : ℕ → Theory F) (h : ∀ n, T n ⊆ T (n + 1)) :
  Theory.consistent (⋃ n, T n) ↔ ∀ n, Theory.consistent (T n) :=
⟨λ H n, consistent_of_consistent_ss H (set.subset_Union T n),
 λ H, by {
  have ss_of_le : ∀ {m n}, m ≤ n → T m ⊆ T n,
  { suffices : ∀ n m, T m ⊆ T (m + n),
    { intros m n le, simpa[show m + (n - m) = n, by omega] using this (n - m) m },
    intros n m, induction n with n IH; simp[←nat.add_one, ←add_assoc],
    { exact set.subset.trans IH (h (m + n)) } },
  rw[finite_character], intros s s_ss s_fin,
  casesI s_fin,
  choose f hf using show ∀ x : s, ∃ i, x.1 ∈ T i, { simpa [set.subset_def] using s_ss },
  let M := ⨆ᶠ i, f i,
  have : s ⊆ T M,
  { intros x hx,
    have : f ⟨x, hx⟩ ≤ M, from le_fintype_sup _ _,
    exact ss_of_le this (hf ⟨x, hx⟩) },
  exact consistent_of_consistent_ss (H M) this }⟩ 

lemma inconsistent_insert_iff_provable_neg {p : F} :
  ¬Theory.consistent (T +{ p }) ↔ T ⊢ ∼p :=
begin
  simp [Theory.consistent_iff_bot, deduction],
  have : T ⊢ ∼p ⟷ p ⟶ ⊥, from neg_iff p,
  split; intros h, { exact (iff_equiv.mp this).2 ⨀ h }, { exact (iff_equiv.mp this).1 ⨀ h }
end

lemma extendable (consis : T.consistent) (p : F) : 
  Theory.consistent (T +{ p }) ∨ Theory.consistent (T +{ ∼p }) :=
by { by_contradiction A, simp[not_or_distrib, inconsistent_insert_iff_provable_neg] at A, rcases A with ⟨A₁, A₂⟩,
     exact consis ⟨p, A₂, A₁⟩ }

def maximal (T : Theory F) : Theory F := classical.epsilon (λ M, consistent M ∧ T ⊆ M ∧ ∀ S, consistent S → M ⊆ S → S = M)

theorem maximal_consistent (consis : consistent T) :  consistent (maximal T) := (classical.epsilon_spec (tukey.exists_maximum tukey_finite_charactor T consis)).1

theorem ss_maximal (consis : consistent T) :  T ⊆ maximal T := (classical.epsilon_spec (tukey.exists_maximum tukey_finite_charactor T consis)).2.1

theorem maximal_maximal (consis : consistent T) : ∀ S, consistent S → maximal T ⊆ S → S = maximal T := (classical.epsilon_spec (tukey.exists_maximum tukey_finite_charactor T consis)).2.2

lemma mem_maximal (consis : consistent T) (p : F) : p ∈ maximal T ∨ ∼p ∈ maximal T :=
begin
  rcases extendable (maximal_consistent consis) p,
  { have : insert p (maximal T) = maximal T, from maximal_maximal consis _ h (set.subset_insert _ _),
    refine or.inl _, rw[←this], exact set.mem_insert p (maximal T) },
  { have : insert (∼p) (maximal T) = maximal T, from maximal_maximal consis _ h (set.subset_insert _ _),
    refine or.inr _, rw[←this], exact set.mem_insert (∼p) (maximal T) }
end

lemma mem_maximal_iff (consis : consistent T) {p : F} : p ∈ maximal T ↔ maximal T ⊢ p :=
⟨by_axiom,
  λ b, by { rcases mem_maximal consis p with (h | h),
    { exact h }, { have : maximal T ⊢ ∼p, from by_axiom h,
      have : ¬(consistent (maximal T)), { simp[consistent_def], refine ⟨_, b, this⟩ },
      have : consistent (maximal T), from maximal_consistent consis, 
      contradiction } }⟩

lemma neg_mem_maximal_iff (consis : consistent T) {p : F} :
  ∼p ∈ maximal T ↔ p ∉ maximal T :=
⟨λ b A, by { simp[mem_maximal_iff consis] at*,
  have : ¬consistent (maximal T), { simp[consistent_def], refine ⟨p, A, b⟩ },
  have : consistent (maximal T), from maximal_consistent consis,
  contradiction },
λ b, by { rcases mem_maximal consis p with (h | h), { contradiction }, { exact h } }⟩

lemma imply_mem_maximal_iff (consis : consistent T) {p q : F} :
  p ⟶ q ∈ maximal T ↔ (p ∈ maximal T → q ∈ maximal T) :=
⟨λ b₁ b₂, by { simp[mem_maximal_iff consis] at*, exact b₁ ⨀ b₂ },
λ h, begin
  by_cases C : p ∈ maximal T,
  { simp[mem_maximal_iff consis] at*, exact hyp_right (h C) p },
  { have : ∼p ∈ maximal T, from (neg_mem_maximal_iff consis).mpr C,
    simp[mem_maximal_iff consis] at*,
    refine deduction.mp _,
    exact explosion (show (maximal T) +{ p } ⊢ p, by simp) (show (maximal T) +{ p } ⊢ ∼p, by simp[this]) }
end⟩

end consistent

lemma provable_iff_inconsistent {p : F} : T ⊢ p ↔ ¬consistent (T +{∼p}) :=
⟨λ h, by { simp[consistent_def], refine ⟨p, by simp[h], by simp⟩ },
λ h, by { have : T +{ ∼p } ⊢ ⊥, from not_consistent_iff_bot.mp h,
          have : T ⊢ ∼∼p, from (iff_of_equiv (neg_iff _)).mpr (deduction.mp this),
          exact dn_iff.mp this }⟩

end Theory

namespace complete
open Theory
variables {F} {𝓢 : Type*} [has_finite_character F] [semantics F 𝓢] [complete F 𝓢] {S : 𝓢}


theorem compactness [semantics.nontrivial F 𝓢] {T : Theory F} :
  semantics.Satisfiable 𝓢 T ↔ (∀ u ⊆ T, u.finite → semantics.Satisfiable 𝓢 (u : set F)) :=
⟨by rintros ⟨S, hS⟩ u ss hu; refine ⟨S, semantics.models_of_ss ss hS⟩,
  begin
    intros h,
    have : consistent T,
    from consistent.finite_character.mpr
      (by { intros u ss hu, exact consistent_iff_Satisfiable.mpr (h u ss hu) }),
    exact consistent_iff_Satisfiable.mp this
  end⟩

theorem compactness' [semantics.nontrivial F 𝓢] {T : Theory F} :
  ¬semantics.Satisfiable 𝓢 T ↔ (∃ u ⊆ T, u.finite ∧ ¬semantics.Satisfiable 𝓢 (u : set F)) :=
by rw[compactness]; simp

end complete

end logic