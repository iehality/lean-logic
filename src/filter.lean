import lindenbaum order.filter

universes u v

namespace fopl
variables (L : language.{u})

def provables (T : theory L) : filter (formula L) :=
{ sets := {S | ∃ p₀ : formula L, {p | T ⊢ p₀ ⟶ p} ⊆ S},
  univ_sets := by { simp },
  sets_of_superset := λ S S', by { simp, intros p₀ hS h, refine ⟨p₀, set.subset.trans hS h⟩ },
  inter_sets := λ S S', by { simp, intros p₀ ss_S q₀ ss_S', refine ⟨p₀ ⊔ q₀, _, _⟩,
    { have : {p | T ⊢ p₀ ⊔ q₀ ⟶ p} ⊆ {p | T ⊢ p₀ ⟶ p},
      { intros p, simp[Lindenbaum.le_of_provable_imply_0], intros h _, exact h },
      exact set.subset.trans this ss_S },
    { have : {p | T ⊢ p₀ ⊔ q₀ ⟶ p} ⊆ {p | T ⊢ q₀ ⟶ p},
      { intros p, simp[Lindenbaum.le_of_provable_imply_0] },
      exact set.subset.trans this ss_S' } } }

end fopl

