import tactic

universes u

variables {α : Sort u} (r : α → α → Prop)

local infix ` ≺ `:50 := r

def infinite_descending_chain (c : ℕ → α) : Prop := ∀ i, c (i + 1) ≺ c i

variables {r}

lemma non_acc_iff {x : α} : ¬acc (≺) x ↔ ∃ y ≺ x, ¬acc (≺) y :=
⟨by { contrapose, simp, exact acc.intro x }, by { contrapose, simp, rintros ⟨h⟩, assumption }⟩

noncomputable def descending_chain (z : α) : ℕ → α
| 0       := z
| (i + 1) := @classical.epsilon α ⟨z⟩ (λ y, y ≺ descending_chain i ∧ ¬acc (≺) y)

@[simp] lemma descending_chain_zero (z : α) : descending_chain (≺) z 0 = z := rfl

lemma infinite_descending_chain_of_non_acc (z : α) (hz : ¬acc (≺) z) : infinite_descending_chain (≺) (descending_chain (≺) z) :=
begin
  haveI : nonempty α, from ⟨z⟩,
  have : ∀ n, (n ≠ 0 → descending_chain (≺) z n ≺ descending_chain (≺) z n.pred) ∧ ¬acc (≺) (descending_chain (≺) z n),
  { intros n, induction n with n IH,
    { simp, exact hz },
    { simp[descending_chain],
      have : ∃ y, y ≺ (descending_chain r z n) ∧ ¬acc (≺) y,
      { rcases (non_acc_iff (≺)).mp IH.2 with ⟨y, hy, hay⟩, exact ⟨y, hy, hay⟩ },
      exact classical.epsilon_spec_aux ⟨z⟩ _ this } },
  intros i, simpa using (this (i + 1)).1,
end

theorem has_infinite_descending_chain_of_non_well_founded (h : ¬well_founded (≺)) : ∃ c, infinite_descending_chain (≺) c :=
begin
  have : ∃ z, ¬acc (≺) z,
  { suffices : ¬∀ z, acc (≺) z, exact not_forall.mp this,
    intros h, have : well_founded r, from ⟨h⟩, contradiction },
  rcases this with ⟨z, hz⟩,
  refine ⟨descending_chain (≺) z, infinite_descending_chain_of_non_acc r z hz⟩
end