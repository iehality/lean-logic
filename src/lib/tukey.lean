import tactic order.zorn

namespace tukey
variables {α : Type*} {F : set α → Prop}

def finite_charactor (P : set α → Prop) : Prop := ∀ a, P a ↔ (∀ s ⊆ a, s.finite → P s)

lemma of_ss (H : finite_charactor F) {a} (ha : F a) {b} (ss : b ⊆ a) : F b :=
begin
  have : ∀ s ⊆ a, s.finite → F s, from (H a).mp ha,
  have : ∀ s ⊆ b, s.finite → F s,
  { intros s hs s_fin, exact this s (set.subset.trans hs ss) s_fin },
  exact (H b).mpr this
end

lemma empty_of_nonempty (H : finite_charactor F) {a} (ha : F a) : F ∅ :=
of_ss H ha (by simp)

lemma finite_chain_sup (H : finite_charactor F) {c : set (set α)} (ch : is_chain has_subset.subset c) :
  ∀ {d : set (set α)} (hs : d.finite) (nemp : d.nonempty) (ss : d ⊆ c), ∃ m ∈ d, ⋃₀d ⊆ m :=
begin
  intros d d_fin,
  refine set.finite.induction_on d_fin (by simp) _,
  intros a s ha s_fin IH _ ss,
  by_cases nemp : s.nonempty,
  { have : ∃ (m ∈ s), ⋃₀ s ⊆ m, from IH nemp (set.subset.trans (by simp) ss),
    rcases this with ⟨m, mem, hs⟩,
    have : m ⊆ a ∨ a ⊆ m, from is_chain.total ch (show m ∈ c, from ss (by simp[mem])) (show a ∈ c, from ss (by simp)),
    rcases this,
    { refine ⟨a, by simp, _⟩,
      simp at hs ⊢, refine ⟨by refl, λ t ht, set.subset.trans (hs t ht) this⟩ },
    { refine ⟨m, by simp[mem], _⟩,
      simp at hs ⊢, refine ⟨this, hs⟩ } },
  { have : s = ∅, from set.not_nonempty_iff_eq_empty.mp nemp, rcases this with rfl,
    refine ⟨a, by simp⟩ }
end

theorem exists_maximum (H : finite_charactor F) (a : set α) (ha : F a) :
  ∃ m, F m ∧ a ⊆ m ∧ ∀ s, F s → m ⊆ s → s = m :=
begin
  suffices : ∃ (m : set α) (H : m ∈ {x : set α | F x}),
  a ⊆ m ∧ ∀ (a : set α), a ∈ {x : set α | F x} → m ⊆ a → a = m,
  { simp at this, exact this },
  refine zorn_subset_nonempty {x | F x} _ a ha, simp,
  rintros c hF hc nemp,
  have : F (⋃₀ c),
  { have : ∀ s ⊆ ⋃₀ c, s.finite → F s,
    { rw[set.sUnion_eq_Union], intros s s_ss s_fin,
      have : ∃ (d : set (set α)), d ⊆ c ∧ d.finite ∧ s ⊆ ⋃₀ d,
      { rcases set.finite_subset_Union s_fin s_ss with ⟨I, I_fin, s_ss⟩,  simp at s_ss,
        refine ⟨coe '' I, by simp, set.finite.image coe I_fin, by simpa using s_ss⟩ },
      rcases this with ⟨d, d_ss, d_fin, hs⟩,
      by_cases d_nemp : d.nonempty,
      { have : ∃ m ∈ d, ⋃₀d ⊆ m, from finite_chain_sup H hc d_fin d_nemp d_ss,
        rcases this with ⟨m, m_mem, ss_m⟩,
        exact of_ss H (show F m, from hF (d_ss m_mem)) (show s ⊆ m, from set.subset.trans hs ss_m) },
      { have : d = ∅, from set.not_nonempty_iff_eq_empty.mp d_nemp, rcases this with rfl,
        simp at hs, have : s = ∅, exact set.subset_eq_empty hs rfl, rcases this with rfl,
        rcases set.nonempty_def.mp nemp with ⟨x, hx⟩, refine empty_of_nonempty H (hF hx) } },
    refine (H (⋃₀ c)).mpr this },
  refine ⟨⋃₀ c, this, λ _, set.subset_sUnion_of_mem⟩
end 

end tukey