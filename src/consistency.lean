import lindenbaum

universes u

namespace fopl
variables {L : language.{u}} {T U : theory L}

namespace theory
open provable axiomatic_classical_logic'

lemma not_consistent_iff_bot {T : theory L} : ¬T.consistent ↔ T ⊢ ⊥ :=
by simp[consistent_iff_bot T]

private lemma list_set_finite {α} (l : list α) : {a : α | a ∈ l}.finite :=
by { induction l with a l IH, { simp },
  { simp[show {b : α | b = a ∨ b ∈ l} = insert a {b : α | b ∈ l}, by refl], exact set.finite.insert a IH } }

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

end theory

end fopl