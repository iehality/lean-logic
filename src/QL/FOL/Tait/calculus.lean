import QL.FOL.Tait.tait QL.FOL.semantics logic

universes u v

namespace fol
open_locale logic_symbol aclogic
variables {L : language.{u}} {m n : ℕ}

namespace Tait

open subformula

noncomputable def finset_mlift (Δ : finset (bounded_subformula L m n)) :
  finset (bounded_subformula L (m + 1) n) := Δ.image mlift

-- Tate caluculus
inductive derivation : Π {m}, finset (bounded_formula L m) → Type u
| AxL {m} : ∀ (Δ : finset (bounded_formula L m)) {k} (r : L.pr k) (v : fin k → bounded_term L m),
    relation r v ∈ Δ → neg_relation r v ∈ Δ → derivation Δ
| verum {m} : ∀ (Δ : finset (bounded_formula L m)), ⊤ ∈ Δ → derivation Δ
| or_left {m} : ∀ (Δ : finset (bounded_formula L m)) (p q : bounded_formula L m),
    derivation (insert p Δ) → derivation (insert (p ⊔ q) Δ)
| or_right {m} : ∀ (Δ : finset (bounded_formula L m)) (p q : bounded_formula L m),
    derivation (insert q Δ) → derivation (insert (p ⊔ q) Δ)
| and {m} : ∀ (Δ : finset (bounded_formula L m)) (p q : bounded_formula L m),
    derivation (insert p Δ) → derivation (insert q Δ) → derivation (insert (p ⊓ q) Δ)
| all {m} : ∀ (Δ : finset (bounded_subformula L m 0)) (p : bounded_subformula L m 1),
    derivation (insert p.push (finset_mlift Δ)) → derivation (insert (∀'p) Δ)
| ex {m} : ∀ (Δ : finset (bounded_subformula L m 0)) (t : bounded_term L m) (p : bounded_subformula L m 1),
    derivation (insert (subst t p) Δ) → derivation (insert (∃'p) Δ)

variables {L m}

def derivable {m} (Δ : finset (bounded_formula L m)) : Prop := nonempty (derivation Δ)

prefix `⊢ᵀ `:45 := derivable

namespace derivable
variables {m} {Δ Γ : finset (bounded_formula L m)}

lemma AxL {k} (r : L.pr k) (v : fin k → bounded_term L m) (h : relation r v ∈ Δ) (hneg : neg_relation r v ∈ Δ) : ⊢ᵀ Δ :=
⟨derivation.AxL Δ r v h hneg⟩

lemma verum (h : ⊤ ∈ Δ) : ⊢ᵀ Δ := ⟨derivation.verum Δ h⟩

lemma or_left (p q : bounded_formula L m) : ⊢ᵀ insert p Δ → ⊢ᵀ insert (p ⊔ q) Δ := λ ⟨d⟩, ⟨derivation.or_left Δ p q d⟩

lemma or_right (p q : bounded_formula L m) : ⊢ᵀ insert q Δ → ⊢ᵀ insert (p ⊔ q) Δ := λ ⟨d⟩, ⟨derivation.or_right Δ p q d⟩

lemma and (p q : bounded_formula L m) : ⊢ᵀ insert p Δ → ⊢ᵀ insert q Δ → ⊢ᵀ insert (p ⊓ q) Δ := λ ⟨d₁⟩ ⟨d₂⟩, ⟨derivation.and Δ p q d₁ d₂⟩

lemma all (p : bounded_subformula L m 1) : ⊢ᵀ insert p.push (finset_mlift Δ) → ⊢ᵀ insert (∀'p) Δ := λ ⟨d⟩, ⟨derivation.all Δ p d⟩

lemma ex (t) (p : bounded_subformula L m 1) : ⊢ᵀ insert (subst t p) Δ → ⊢ᵀ insert (∃'p) Δ := λ ⟨d⟩, ⟨derivation.ex Δ t p d⟩

protected lemma cast (h : ⊢ᵀ Δ) (e : Δ = Γ) : ⊢ᵀ Γ := cast (by rw e) h

@[elab_as_eliminator]
theorem rec_on {C : Π {m} (Δ : finset (bounded_formula L m)), ⊢ᵀ Δ → Prop}
  {m : ℕ} {Δ : finset (bounded_formula L m)} (d : ⊢ᵀ Δ)
  (hAxL : ∀ {m} (Δ : finset (bounded_formula L m)) {k} (r : L.pr k) (v : fin k → bounded_term L m)
    (h : relation r v ∈ Δ) (hneg : neg_relation r v ∈ Δ), C Δ (AxL r v h hneg))
  (hverum : ∀ {m} (Δ : finset (bounded_formula L m)) (h : ⊤ ∈ Δ), C Δ (verum h))
  (hor_left : ∀ {m} (Δ : finset (bounded_formula L m)) (p q : bounded_formula L m) (d : ⊢ᵀ insert p Δ),
    C (insert p Δ) d → C (insert (p ⊔ q) Δ) (or_left p q d))
  (hor_right : ∀ {m} (Δ : finset (bounded_formula L m)) (p q : bounded_formula L m) (d : ⊢ᵀ insert q Δ),
    C (insert q Δ) d → C (insert (p ⊔ q) Δ) (or_right p q d))
  (hand : ∀ {m} (Δ : finset (bounded_formula L m)) (p q : bounded_formula L m) (d₁ : ⊢ᵀ insert p Δ) (d₂ : ⊢ᵀ insert q Δ),
    C (insert p Δ) d₁ → C (insert q Δ) d₂ → C (insert (p ⊓ q) Δ) (and p q d₁ d₂))
  (hall : ∀ {m} (Δ : finset (bounded_formula L m)) (p : bounded_subformula L m 1) (d : ⊢ᵀ insert p.push (finset_mlift Δ)),
    C (insert p.push (finset_mlift Δ)) d → C (insert (∀'p) Δ) (all p d))
  (hex : ∀ {m} (Δ : finset (bounded_formula L m)) (t) (p : bounded_subformula L m 1) (d : ⊢ᵀ insert (subst t p) Δ),
    C (insert (subst t p) Δ) d → C (insert (∃'p) Δ) (ex t p d)) : C Δ d :=
 by unfreezingI {
  begin
    cases d,
    induction d,
    case AxL : m Δ k r v h hneg { exact hAxL Δ r v h hneg },
    case verum : m Δ h { exact hverum Δ h },
    case or_left : m Δ p q _ ih { exact hor_left Δ p q _ ih },
    case or_right : m Δ p q _ ih { exact hor_right Δ p q _ ih },
    case and : m Δ p q _ _ ih₁ ih₂ { exact hand Δ p q _ _ ih₁ ih₂ },
    case all : m Δ p _ ih { exact hall Δ p _ ih },
    case ex : m Δ t p _ ih { exact hex Δ t p _ ih }
  end }

protected lemma weakening (h : ⊢ᵀ Δ) : ∀ {Γ}, Δ ⊆ Γ → ⊢ᵀ Γ :=
begin
  apply rec_on h,
  { intros m Δ k r v h hneg Γ ss, refine AxL r v (ss h) (ss hneg) },
  { intros m Δ h Γ ss, refine verum (ss h) },
  { intros m Δ p q h IH Γ ss,
    have : ⊢ᵀ insert p Γ, from IH (finset.insert_subset_insert _ (finset.insert_subset.mp ss).2),
    have : ⊢ᵀ insert (p ⊔ q) Γ, from or_left p q this,
    refine derivable.cast this (by { simp, exact (finset.insert_subset.mp ss).1}) },
  { intros m Δ p q h IH Γ ss,
    have : ⊢ᵀ insert q Γ, from IH (finset.insert_subset_insert _ (finset.insert_subset.mp ss).2),
    have : ⊢ᵀ insert (p ⊔ q) Γ, from or_right p q this,
    refine derivable.cast this (by { simp, exact (finset.insert_subset.mp ss).1}) },
  { intros m Δ p q h₁ h₂ IH₁ IH₂ Γ ss,
    have l₁ : ⊢ᵀ insert p Γ, from IH₁ (finset.insert_subset_insert _ $ (finset.insert_subset.mp ss).2),
    have l₂ : ⊢ᵀ insert q Γ, from IH₂ (finset.insert_subset_insert _ $ (finset.insert_subset.mp ss).2),
    have : ⊢ᵀ insert (p ⊓ q) Γ, from and p q l₁ l₂,
    refine derivable.cast this (by { simp, exact (finset.insert_subset.mp ss).1}) },
  { intros m Δ p h IH Γ ss,
    have : ⊢ᵀ insert p.push (finset_mlift Γ),
      from IH (finset.insert_subset_insert _ $ finset.image_subset_image (finset.insert_subset.mp ss).2),
    have : ⊢ᵀ insert (∀'p) Γ := all p this,
    refine derivable.cast this (by { simp, exact (finset.insert_subset.mp ss).1}) },
  { intros m Δ t p h IH Γ ss,
    have : ⊢ᵀ insert (subst t p) Γ, from IH (finset.insert_subset_insert _ (finset.insert_subset.mp ss).2),
    have : ⊢ᵀ insert (∃'p) Γ := ex t p this,
    refine derivable.cast this (by { simp, exact (finset.insert_subset.mp ss).1}) }
end

end derivable

section
variables {Δ : finset (bounded_formula L m)}
open axiomatic_classical_logic' axiomatic_classical_logic

lemma provable_of_derivation : derivation Δ → ∅ ⊢ (Δ.image to_fol).disjunction := λ h,
begin
  induction h,
  case AxL : m Δ k r v h nh
  { suffices : ∅ ⊢ fol.subformula.relation r v ⊔ ∼fol.subformula.relation r v ⟶ (finset.image to_fol Δ).disjunction,
    from this ⨀ excluded_middle,
    refine or_imply _ _ _ ⨀ _ ⨀ _,
    { refine imply_fdisj (by { simp, refine ⟨_, h, by simp⟩ }) },
    { refine imply_fdisj (by { simp, refine ⟨_, nh, by simp⟩ }) } },
  case or_left : m Δ p q b IH
  { refine fdisj_imply_of _ ⨀ IH,
    { simp, split,
      { refine imply_trans (imply_or_left p.to_fol q.to_fol) (imply_fdisj (by simp)) },
      { intros p hp, refine (imply_fdisj
          (finset.mem_insert_of_mem (finset.mem_image_of_mem to_fol hp))) } } },
  case or_right : m Δ p q b IH
  { refine fdisj_imply_of _ ⨀ IH,
    { simp, split,
      { refine imply_trans (imply_or_right p.to_fol q.to_fol) (imply_fdisj (by simp)) },
      { intros p hp, refine (imply_fdisj
          (finset.mem_insert_of_mem (finset.mem_image_of_mem to_fol hp))) } } },
  sorry
end

end


end Tait

end fol