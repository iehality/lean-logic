import lindenbaum

universes u

namespace fopl
variables {L : language.{u}} {T U : theory L}

namespace theory
open provable axiomatic_classical_logic'

lemma consistent_of_consistent_ss {T U : theory L} (h : consistent T) (ss : U ⊆ T) : consistent U :=
by { simp[consistent_iff_bot] at h ⊢, intros hU, have : T ⊢ ⊥, from weakening hU ss, contradiction }

private lemma list_set_finite {α} (l : list α) : {a : α | a ∈ l}.finite :=
by { induction l with a l IH, { simp },
  { simp[show {b : α | b = a ∨ b ∈ l} = insert a {b : α | b ∈ l}, by refl], exact set.finite.insert a IH } }

namespace consistent

lemma finite_character :
  consistent T ↔ ∀ (s ⊆ T) (f : s.finite), consistent s :=
⟨begin
  intros h,
  by_contradiction A, simp at A,
  rcases A with ⟨s, ss, s_fin, hs⟩,
  have : s ⊢ ⊥, from not_consistent_iff_bot.mp hs,
  have : T ⊢ ⊥, from weakening this ss,
  have : ¬T ⊢ ⊥, from (consistent_iff_bot _).mp h,
  contradiction
end,
begin
  intros H,
  by_contradiction A, simp[not_consistent_iff_bot] at A,
  have : ∃ (P : list (formula L)), (∀ p ∈ P, T p) ∧ ∅ ⊢ conjunction P ⟶ ⊥, from provable.proof_conjunction A,
  rcases this with ⟨P, ss, b⟩,
  let s := {p | p ∈ P},
  have : s ⊢ ⊥,
  { have lmm₁ : s ⊢ conjunction P ⟶ ⊥, from weakening b (by simp),
    have lmm₂ : s ⊢ conjunction P, from conjunction_provable (λ p h, by_axiom (by simp[s, h])),
    exact lmm₁ ⨀ lmm₂ },
  have : consistent s, from H s ss (by simp[s, list_set_finite]),
  have : ¬s ⊢ ⊥, exact (consistent_iff_bot s).mp this,
  contradiction
end⟩

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
  suffices : ∀ (s : theory L), set.finite s → s ⊆ U → (T ∪ s).consistent,
  { intros s ss fin, exact this s fin ss },
  intros s fin,
  refine set.finite.induction_on fin (λ _, by simp[consis]) _,
  intros p s nmem fin consis ss, 
  have : T ∪ insert p s = (T ∪ s) +{ p }, { ext q, simp },
  simp[this],
  exact H s (set.subset.trans (show s ⊆ insert p s, by simp) ss) p (ss (show p ∈ insert p s, by simp)) nmem fin
    (consis (set.subset.trans (show s ⊆ insert p s, by simp) ss))
end

end consistent

end theory

end fopl