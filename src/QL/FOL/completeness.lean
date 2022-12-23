import QL.FOL.Tait.search_tree QL.FOL.Tait.semantics

universes u v

namespace fol
open_locale logic_symbol aclogic
open subformula
variables {L : language.{u}}  {m : ℕ}

theorem completeness_of_countable_language [∀ k, encodable (L.fn k)] [∀ k, encodable (L.pr k)] {T : Theory L} {σ : sentence L} :
  T ⊧₀ σ → T ⊢ σ :=
begin
  have s : T ⊧₀ σ → to_tait '' T ⊧ σ.to_tait,
  { intros h S hh, simpa using @h S (by { intros p hp, simpa using hh (set.mem_image_of_mem _ hp) }) },
  have complete : to_tait '' T ⊧ σ.to_tait → to_tait '' T ⊢ σ.to_tait, from Tait.completeness_of_countable_language,
  have b : to_tait '' T ⊢ to_tait σ → T ⊢ σ, from provable.of_Tait_provable,
  refine (λ h, (b $ complete $ s h))
end

end fol

