import QL.FOL.Tait.tait QL.FOL.semantics QL.FOL.Tait.coding logic

universes u v

namespace fol
open_locale logic_symbol aclogic

namespace Tait

variables {L : language.{u}} {m n : ℕ}
namespace subformula

variables (S : Structure L) {n} {me : fin m → S} {e : fin n → S}

@[simp] def val' (me : fin m → S) : ∀ {n} (e : fin n → S), subformula L m n → Prop
| n _ verum              := true
| n _ falsum             := false
| n e (relation p v)     := S.pr p (subterm.val S me e ∘ v)
| n e (neg_relation p v) := ¬S.pr p (subterm.val S me e ∘ v)
| n e (and p q)          := p.val' e ∧ q.val' e
| n e (or p q)           := p.val' e ∨ q.val' e
| n e (fal p)            := ∀ x : S.dom, (p.val' (x *> e))
| n e (ex p)             := ∃ x : S.dom, (p.val' (x *> e))

@[simp] lemma val'_neg (p : subformula L m n) : val' S me e (∼p) = ¬val' S me e p :=
by induction p generalizing me e; simp[mlift, ←verum_eq, ←falsum_eq, ←and_eq, ←or_eq, ←not_eq, ←fal_eq, ←ex_eq, or_iff_not_imp_left, *] at*

@[irreducible] def val (me : fin m → S) (e : fin n → S) : subformula L m n →ₗ Prop :=
{ to_fun := val' S me e,
  map_neg' := λ _, by simp,
  map_imply' := λ _ _, by simp[has_arrow.arrow, imply, or_iff_not_imp_left, not_eq],
  map_and' := λ p q, by unfold has_inf.inf; simp; refl,
  map_or' := λ p q, by unfold has_sup.sup; simp; refl,
  map_top' := by refl,
  map_bot' := by refl }

@[simp] lemma val_relation {p} (r : L.pr p) (v) :
  val S me e (relation r v) ↔ S.pr r (subterm.val S me e ∘ v) :=  by simp[val]; refl

@[simp] lemma val_neg_relation {p} (r : L.pr p) (v) :
  val S me e (neg_relation r v) ↔ ¬S.pr r (subterm.val S me e ∘ v) := by simp[val]; refl

@[simp] lemma val_fal (p : subformula L m (n + 1)) :
  val S me e (∀'p) ↔ ∀ x : S, val S me (x *> e) p := by simp[val]; refl

@[simp] lemma val_ex (p : subformula L m (n + 1)) :
  val S me e (∃'p) ↔ ∃ x : S, val S me (x *> e) p := by simp[val]; refl

end subformula

namespace formula
variables (S : Structure L) {m n} (me : fin m → S)

def val : formula L m →ₗ Prop := subformula.val S me fin.nil  

end formula

def models (S : Structure L) (p : formula L m) : Prop := ∀ e, formula.val S e p

namespace sentence
variables (S : Structure L)


end sentence

open subformula

noncomputable def finset_mlift (Δ : finset (subformula L m n)) : finset (subformula L (m + 1) n) := Δ.image mlift

-- Tate caluculus
inductive derivative : Π {m}, finset (formula L m) → Type u
| AxL {m} : ∀ (Δ : finset (formula L m)) {k} (r : L.pr k) (v : fin k → subterm L m 0),
    relation r v ∈ Δ → neg_relation r v ∈ Δ → derivative Δ
| verum {m} : ∀ (Δ : finset (formula L m)), ⊤ ∈ Δ → derivative Δ
| or_left {m} : ∀ (Δ : finset (formula L m)) (p q : formula L m),
    derivative (insert p Δ) → derivative (insert (p ⊔ q) Δ)
| or_right {m} : ∀ (Δ : finset (formula L m)) (p q : formula L m),
    derivative (insert q Δ) → derivative (insert (p ⊔ q) Δ)
| and {m} : ∀ (Δ : finset (formula L m)) (p q : formula L m),
    derivative (insert p Δ) → derivative (insert q Δ) → derivative (insert (p ⊓ q) Δ)
| all {m} : ∀ (Δ : finset (subformula L m 0)) (p : subformula L m 1),
    derivative (insert p.push (finset_mlift Δ)) → derivative (insert (∀'p) Δ)
| ex {m} : ∀ (Δ : finset (subformula L m 0)) (t : subterm L m 0) (p : subformula L m 1),
    derivative (insert (subst t p) Δ) → derivative (insert (∃'p) Δ)

variables {L m}

def derivable {m} (Δ : finset (formula L m)) : Prop := nonempty (derivative Δ)

prefix `⊢ᵀ `:45 := derivable

namespace derivable
variables {m} {Δ Γ : finset (formula L m)}

lemma AxL {k} (r : L.pr k) (v : fin k → subterm L m 0) (h : relation r v ∈ Δ) (hneg : neg_relation r v ∈ Δ) : ⊢ᵀ Δ :=
⟨derivative.AxL Δ r v h hneg⟩

lemma verum (h : ⊤ ∈ Δ) : ⊢ᵀ Δ := ⟨derivative.verum Δ h⟩

lemma or_left (p q : formula L m) : ⊢ᵀ insert p Δ → ⊢ᵀ insert (p ⊔ q) Δ := λ ⟨d⟩, ⟨derivative.or_left Δ p q d⟩

lemma or_right (p q : formula L m) : ⊢ᵀ insert q Δ → ⊢ᵀ insert (p ⊔ q) Δ := λ ⟨d⟩, ⟨derivative.or_right Δ p q d⟩

lemma and (p q : formula L m) : ⊢ᵀ insert p Δ → ⊢ᵀ insert q Δ → ⊢ᵀ insert (p ⊓ q) Δ := λ ⟨d₁⟩ ⟨d₂⟩, ⟨derivative.and Δ p q d₁ d₂⟩

lemma all (p : subformula L m 1) : ⊢ᵀ insert p.push (finset_mlift Δ) → ⊢ᵀ insert (∀'p) Δ := λ ⟨d⟩, ⟨derivative.all Δ p d⟩

lemma ex (t) (p : subformula L m 1) : ⊢ᵀ insert (subst t p) Δ → ⊢ᵀ insert (∃'p) Δ := λ ⟨d⟩, ⟨derivative.ex Δ t p d⟩

protected lemma cast (h : ⊢ᵀ Δ) (e : Δ = Γ) : ⊢ᵀ Γ := cast (by rw e) h

@[elab_as_eliminator]
theorem rec_on {C : Π {m} (Δ : finset (formula L m)), ⊢ᵀ Δ → Prop}
  {m : ℕ} {Δ : finset (formula L m)} (d : ⊢ᵀ Δ)
  (hAxL : ∀ {m} (Δ : finset (formula L m)) {k} (r : L.pr k) (v : fin k → subterm L m 0)
    (h : relation r v ∈ Δ) (hneg : neg_relation r v ∈ Δ), C Δ (AxL r v h hneg))
  (hverum : ∀ {m} (Δ : finset (formula L m)) (h : ⊤ ∈ Δ), C Δ (verum h))
  (hor_left : ∀ {m} (Δ : finset (formula L m)) (p q : formula L m) (d : ⊢ᵀ insert p Δ),
    C (insert p Δ) d → C (insert (p ⊔ q) Δ) (or_left p q d))
  (hor_right : ∀ {m} (Δ : finset (formula L m)) (p q : formula L m) (d : ⊢ᵀ insert q Δ),
    C (insert q Δ) d → C (insert (p ⊔ q) Δ) (or_right p q d))
  (hand : ∀ {m} (Δ : finset (formula L m)) (p q : formula L m) (d₁ : ⊢ᵀ insert p Δ) (d₂ : ⊢ᵀ insert q Δ),
    C (insert p Δ) d₁ → C (insert q Δ) d₂ → C (insert (p ⊓ q) Δ) (and p q d₁ d₂))
  (hall : ∀ {m} (Δ : finset (formula L m)) (p : subformula L m 1) (d : ⊢ᵀ insert p.push (finset_mlift Δ)),
    C (insert p.push (finset_mlift Δ)) d → C (insert (∀'p) Δ) (all p d))
  (hex : ∀ {m} (Δ : finset (formula L m)) (t) (p : subformula L m 1) (d : ⊢ᵀ insert (subst t p) Δ),
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
variables {Δ : finset (formula L m)}
open axiomatic_classical_logic' axiomatic_classical_logic

lemma provable_of_derivative : derivative Δ → ∅ ⊢ (Δ.image to_fol).disjunction := λ h,
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

section search_tree

def is_terminal (Δ : list (subformula L m 0)) : Prop := ∃ {k} (r : L.pr k) (v), relation r v ∈ Δ ∧ neg_relation r v ∈ Δ

variables {L} [∀ k, encodable (L.fn k)] [∀ k, encodable (L.pr k)]
open encodable

def decomp : ℕ → list (subformula L m 0) →
  set (ℕ × Σ m, list (subformula L m 0))
| s []                      := { ⟨s, m, []⟩}
| s (relation r v :: Γ)     := { ⟨s, m, Γ ++ [relation r v]⟩, }
| s (neg_relation r v :: Γ) := { ⟨s, m, Γ ++ [neg_relation r v]⟩, }
| s (⊤ :: Γ)                := ∅
| s (⊥ :: Γ)                := { ⟨s, m, Γ ++ [⊥]⟩, }
| s (p ⊓ q :: Γ)            := { ⟨s, m, Γ ++ [p]⟩, ⟨s, _, Γ ++ [q]⟩, }
| s (p ⊔ q :: Γ)            := { ⟨s, m, Γ ++ [p, q]⟩, }
| s ((fal p) :: Γ)          := { ⟨s, m + 1, Γ.map mlift ++ [push p]⟩, }
| s ((ex p) :: Γ)           := { ⟨s + 1, m, Γ ++ (option.map (λ t, subst t p) $ fol.subterm.of_nat  L m 0 s).to_list ++ [∃'p]⟩, }

variables {L}

@[reducible] def search_label (L : language) := ℕ × ℕ × Σ m, list (subformula L m 0)

noncomputable def index_of_set (M : set (sentence L)) (i : ℕ) : option (formula L m) :=
(option.guard (λ i, i ∈ to_nat '' M) i).bind (subformula.of_nat L m 0)

@[simp] lemma mlift_index_of_set (M : set (sentence L)) (i : ℕ) :
  (index_of_set M i : option (formula L m)).map mlift = index_of_set M i :=
begin
  ext p, simp[index_of_set], split,
  { rintros ⟨q, ⟨i, ⟨rfl, σ, hσ, rfl⟩, h⟩, rfl⟩,
    refine ⟨σ.to_nat, ⟨rfl, σ, hσ, rfl⟩, _⟩,
    refine of_nat_eq_some.mpr (by simpa using subformula.of_nat_eq_some.mp h) },
  { rintros ⟨i, ⟨rfl, σ, hσ, rfl⟩, h⟩,
    let p' : formula L m := σ.to_uniform.to_subformula (le_trans (subformula_uvars σ) (by simp)),
    have hp' : to_nat p' = σ.to_nat, by simp[p', to_nat],
    refine ⟨p', ⟨σ.to_nat, ⟨rfl, σ, hσ, rfl⟩, of_nat_eq_some.mpr hp'⟩, _⟩,
    refine to_nat_inj.mp (by { simp, symmetry, refine of_nat_eq_some.mp (by simpa[hp'] using h) }) }
end

lemma index_of_neg_set_eq_some {M : set (sentence L)} {i : ℕ} {p : formula L m} :
  index_of_set M i = some p → ∃ σ ∈ M, to_nat σ = to_nat p := λ h,
by { simp[index_of_set] at h, rcases h with ⟨_, ⟨rfl, σ, hσ, rfl⟩, h⟩, 
     refine ⟨σ, hσ, (subformula.of_nat_eq_some.mp h).symm⟩ } 

@[simp] noncomputable def indices_of_neg_set (M : set (sentence L)) (m) : ℕ → list (formula L m)
| 0       := []
| (i + 1) := (index_of_set M i).to_list ++ indices_of_neg_set i

inductive search_tree (M : set (sentence L)) : search_label L → search_label L → Prop
| intro : ∀ {m₁ m₂} (Γ₁ : list (subformula L m₁ 0)) (Γ₂ : list (subformula L m₂ 0)) (s₁ s₂ i : ℕ),
    ¬is_terminal Γ₁ → 
    (s₂, sigma.mk m₂ Γ₂) ∈ decomp s₁ Γ₁ →
    search_tree ⟨i + 1, s₂, m₂, Γ₂ ++ (index_of_set M i).to_list⟩ ⟨i, s₁, m₁, Γ₁⟩

notation l₁ ` ≺[` :50 M `] ` l₂ :50 := search_tree M l₁ l₂

variables {M : set (sentence L)} {Δ : list (sentence L)}

variables (M Δ)

inductive accessible (Δ : list (sentence L)) : search_label L → Prop
| top : accessible ⟨0, 0, sigma.mk 0 Δ⟩
| lt : ∀ {l₁ l₂}, l₁ ≺[M] l₂ → accessible l₂ → accessible l₁

def accessible_label := { l // accessible M Δ l }

def accessible_search_tree : accessible_label M Δ → accessible_label M Δ → Prop :=
λ l₁ l₂, l₁.val ≺[M] l₂.val 

local infix ` ≺ `:50 := accessible_search_tree M Δ

@[simp] lemma Axl_bot (l) (Γ : list (formula L m)) (h : is_terminal Γ) {i s} : ¬search_tree M l ⟨i, s, _, Γ⟩ :=
by rintros ⟨⟩; contradiction

section well_founded
variables {M Δ} (H : well_founded (accessible_search_tree M Δ))

def accessible_search_tree.recursion {C : accessible_label M Δ → Sort*} 
  (l) (h : Π l₁, (Π l₂, l₂ ≺ l₁ → C l₂) → C l₁) : C l :=
well_founded.recursion H l h

lemma search_tree_nil (i s) {m} :
  ⟨i + 1, s, m, (index_of_set M i).to_list⟩ ≺[M] ⟨i, s, m, []⟩ := 
by { refine search_tree.intro [] [] s s i _ (by simp[decomp]), { simp[is_terminal] } }

lemma search_tree_falsum (i s) {m} (Γ : list (formula L m)) (h : ¬is_terminal (⊥ :: Γ)) :
  ⟨i + 1, s, m, Γ ++ [⊥] ++ (index_of_set M i).to_list⟩ ≺[M] ⟨i, s, m, ⊥ :: Γ⟩ := 
search_tree.intro _ _ _ _ _ h (by simp[decomp])

lemma search_tree_relation (i s) {m} (Γ : list (formula L m)) {k} (r : L.pr k) (v : fin k → subterm L m 0)
  (h : ¬is_terminal (relation r v :: Γ)) :
  ⟨i + 1, s, m, Γ ++ [relation r v] ++ (index_of_set M i).to_list⟩ ≺[M] ⟨i, s, m, relation r v :: Γ⟩ := 
search_tree.intro _ _ _ _ _ h (by simp[decomp])

lemma search_tree_neg_relation (i s) {m} (Γ : list (formula L m)) {k} (r : L.pr k) (v : fin k → subterm L m 0)
  (h : ¬is_terminal (neg_relation r v :: Γ)) :
  ⟨i + 1, s, m, Γ ++ [neg_relation r v] ++ (index_of_set M i).to_list⟩ ≺[M] ⟨i, s, m, neg_relation r v :: Γ⟩ := 
search_tree.intro _ _ _ _ _ h (by simp[decomp])

lemma search_tree_and_left (i s) {m} (Γ : list (formula L m)) (p q : formula L m)
  (h : ¬is_terminal (p ⊓ q :: Γ)) :
  ⟨i + 1, s, m, Γ ++ [p] ++ (index_of_set M i).to_list⟩ ≺[M] ⟨i, s, m, p ⊓ q :: Γ⟩ := 
search_tree.intro _ _ _ _ _ h (by simp[decomp])

lemma search_tree_and_right (i s) {m} (Γ : list (formula L m)) (p q : formula L m)
  (h : ¬is_terminal (p ⊓ q :: Γ)) :
  ⟨i + 1, s, m, Γ ++ [q] ++ (index_of_set M i).to_list⟩ ≺[M] ⟨i, s, m, p ⊓ q :: Γ⟩ := 
search_tree.intro _ _ _ _ _ h (by simp[decomp])

lemma search_tree_or (i s) {m} (Γ : list (formula L m)) (p q : formula L m)
  (h : ¬is_terminal (p ⊔ q :: Γ)) :
  ⟨i + 1, s, m, Γ ++ [p, q] ++ (index_of_set M i).to_list⟩ ≺[M] ⟨i, s, m, p ⊔ q :: Γ⟩ := 
search_tree.intro _ _ _ _ _ h (by simp[decomp])

lemma search_tree_fal (i s) {m} (Γ : list (formula L m)) (p : subformula L m 1)
  (h : ¬is_terminal ((∀'p) :: Γ)) :
  ⟨i + 1, s, m + 1, Γ.map mlift ++ [p.push] ++ (index_of_set M i).to_list⟩ ≺[M] ⟨i, s, m, (∀'p) :: Γ⟩ := 
search_tree.intro _ _ _ _ _ h (by simp[decomp, ←fal_eq])

lemma search_tree_ex (i s) {m} (Γ : list (formula L m)) (p : subformula L m 1)
  (h : ¬is_terminal ((∃'p) :: Γ)) :
  ⟨i + 1, s + 1, m, Γ ++ (option.map (λ t, subst t p) $ fol.subterm.of_nat L m 0 s).to_list ++
    [∃'p] ++ (index_of_set M i).to_list⟩ ≺[M] ⟨i, s, m, (∃'p) :: Γ⟩ := 
search_tree.intro ((∃'p) :: Γ)
  (Γ ++ (option.map (λ t, subst t p) $ fol.subterm.of_nat L m 0 s).to_list ++ [∃'p]) 
  s (s + 1) i h (by simp[decomp, ←ex_eq])


private lemma synthetic_main_lemma_aux_and {Γ : list (formula L m)} {p q : formula L m} {i} {I₁ I₂ : list ℕ}
  (d₁ : ⊢ᵀ (Γ ++ [p] ++ (index_of_set M i).to_list).to_finset ∪ (I₁.bind (λ i, (index_of_set M i).to_list)).to_finset)
  (d₂ : ⊢ᵀ (Γ ++ [q] ++ (index_of_set M i).to_list).to_finset ∪ (I₂.bind (λ i, (index_of_set M i).to_list)).to_finset) : 
  ⊢ᵀ (p ⊓ q :: Γ).to_finset ∪ ((i :: I₁ ++ I₂).bind (λ i, (index_of_set M i).to_list)).to_finset :=
begin
simp at d₁,
  have d₁ : ⊢ᵀ insert p (Γ.to_finset ∪ ((index_of_set M i).to_finset ∪ ((i :: I₁ ++ I₂).bind (λ i, (index_of_set M i).to_list)).to_finset)),
    from derivable.weakening d₁ (by intros p; simp[-list.mem_map, -list.mem_bind]; tauto),
  have d₂ : ⊢ᵀ insert q (Γ.to_finset ∪ ((index_of_set M i).to_finset ∪ ((i :: I₁ ++ I₂).bind (λ i, (index_of_set M i).to_list)).to_finset)),
    from derivable.weakening d₂ (by intros p; simp[-list.mem_map, -list.mem_bind]; tauto),
  have : ⊢ᵀ insert (p ⊓ q) (Γ.to_finset ∪ ((index_of_set M i).to_finset ∪ ((i :: I₁ ++ I₂).bind (λ i, (index_of_set M i).to_list)).to_finset)),
    from derivable.and p q d₁ d₂,
  exact derivable.cast this (by ext; simp[and_eq])
end

private lemma synthetic_main_lemma_aux_or {Γ : list (formula L m)} {p q : formula L m} {i} {I : list ℕ}
  (d : ⊢ᵀ (Γ ++ [p, q] ++ (index_of_set M i).to_list).to_finset ∪ (I.bind (λ i, (index_of_set M i).to_list)).to_finset) : 
  ⊢ᵀ (p ⊔ q :: Γ).to_finset ∪ ((i :: I).bind (λ i, (index_of_set M i).to_list)).to_finset :=
begin
  have : ⊢ᵀ (insert p $ insert q $ Γ.to_finset ∪ ((i :: I).bind (λ i, (index_of_set M i).to_list)).to_finset),
  by simpa using d,
  have : ⊢ᵀ (insert q $ insert (p ⊔ q) $ Γ.to_finset ∪ ((i :: I).bind (λ i, (index_of_set M i).to_list)).to_finset),
    from derivable.cast (derivable.or_left p q this) (finset.insert.comm _ _ _),
  have : ⊢ᵀ (insert (p ⊔ q) $ Γ.to_finset ∪ ((i :: I).bind (λ i, (index_of_set M i).to_list)).to_finset),
  from derivable.cast (derivable.or_right p q this) (finset.insert_idem _ _),
  exact derivable.cast this (by ext x; simp[-list.mem_map, -list.mem_bind])
end

private lemma synthetic_main_lemma_aux_all {Γ : list (formula L m)} {p : subformula L m 1} {i} {I : list ℕ}
  (d : ⊢ᵀ (Γ.map mlift ++ [p.push] ++ (index_of_set M i).to_list).to_finset ∪ (I.bind (λ i, (index_of_set M i).to_list)).to_finset) : 
  ⊢ᵀ ((∀'p) :: Γ).to_finset ∪ ((i :: I).bind (λ i, (index_of_set M i).to_list)).to_finset :=
begin
  have : ⊢ᵀ insert p.push (finset_mlift $ Γ.to_finset ∪ ((i :: I).bind (λ i, (index_of_set M i).to_list)).to_finset),
  { refine derivable.cast d (by { ext p,
    simp[-list.mem_map, -list.mem_bind, -finset.mem_image, finset_mlift, finset.image_union, 
      finset.image_to_finset_list, finset.image_to_finset_option, list.bind_map, list.map_to_list_option] }) },
  have : ⊢ᵀ insert (∀'p) (Γ.to_finset ∪ ((i :: I).bind (λ i, (index_of_set M i).to_list)).to_finset),
    from derivable.all p this,
  exact derivable.cast this (by ext x; simp)
end

private lemma synthetic_main_lemma_aux_ex {Γ : list (formula L m)} {p : subformula L m 1} {i s} {I : list ℕ}
  (d : ⊢ᵀ (Γ ++ ((subterm.of_nat L m 0 s).map (λ t, subst t p)).to_list ++ [(∃'p : subformula _ _ _)] ++
    (index_of_set M i).to_list).to_finset ∪ (I.bind (λ i, (index_of_set M i).to_list)).to_finset) : 
  ⊢ᵀ ((∃'p) :: Γ).to_finset ∪ ((i :: I).bind (λ i, (index_of_set M i).to_list)).to_finset :=
begin
  simp at d,
  cases subterm.of_nat L m 0 s with t; simp at d,
  { exact derivable.cast d (by ext x; simp) },
  { have : ⊢ᵀ (insert (subst t p) $ insert (∃'p) $ Γ.to_finset ∪ ((i :: I).bind (λ i, (index_of_set M i).to_list)).to_finset),
    exact derivable.cast d (by ext; simp[-list.mem_map, -list.mem_bind]; tauto),
    have : ⊢ᵀ (insert (∃'p) $ Γ.to_finset ∪ ((i :: I).bind (λ i, (index_of_set M i).to_list)).to_finset),
    exact derivable.cast (derivable.ex t p this) (by ext; simp),
    exact derivable.cast this (by ext; simp) }
end

include H

lemma synthetic_main_lemma_aux (l : accessible_label M Δ) : ∃ I : list ℕ,
  ⊢ᵀ l.val.2.2.2.to_finset ∪ list.to_finset (I.bind (λ i, (index_of_set M i).to_list)) :=
begin
  apply accessible_search_tree.recursion H l,
  rintros ⟨⟨i, s, m, Γ⟩, accΓ⟩ IH,
  have IH : ∀ (i₂ s₂) {m₂} (Γ₂ : list (subformula L m₂ 0)),
    ⟨i₂, s₂, m₂, Γ₂⟩ ≺[M] ⟨i, s, m, Γ⟩ →
    ∃ I : list ℕ, ⊢ᵀ Γ₂.to_finset ∪ list.to_finset (I.bind (λ i, (index_of_set M i).to_list)),
  { intros i₂ s₂ m₂ Γ₂ h, 
    have : accessible M Δ ⟨i₂, s₂, m₂, Γ₂⟩, from accessible.lt h accΓ,
    simpa using IH ⟨⟨i₂, s₂, _, Γ₂⟩, this⟩ h },
  show ∃ (I : list ℕ), ⊢ᵀ Γ.to_finset ∪ (I.bind (λ i, (index_of_set M i).to_list)).to_finset,
  by_cases hΓ : is_terminal Γ,
  { rcases hΓ with ⟨k, r, v, hΓ, hΓ_neg⟩,
    refine ⟨[], by simp; exact derivable.AxL r v (by simp; refine hΓ) (by simp; refine hΓ_neg)⟩ },
  cases Γ with p Γ,
  { rcases IH _ _ _ (search_tree_nil _ _) with ⟨I, d⟩,
    refine ⟨i :: I, derivable.cast d (by ext; simp)⟩ },
  cases p,
  case verum { refine ⟨[], derivable.verum (by simp[verum_eq])⟩ },
  case falsum
  { rcases IH _ _ _ (search_tree_falsum _ _ _ hΓ) with ⟨I, d⟩,
    refine ⟨i :: I, derivable.cast d (by ext; simp[falsum_eq])⟩ },  
  case relation : k r v
  { rcases IH _ _ _ (search_tree_relation _ _ _ r v hΓ) with ⟨I, d⟩,
    refine ⟨i :: I, derivable.cast d (by ext; simp)⟩ },
  case neg_relation : k r v
  { rcases IH _ _ _ (search_tree_neg_relation _ _ _ r v hΓ) with ⟨I, d⟩,
    refine ⟨i :: I, derivable.cast d (by ext; simp)⟩ },
  case and : p q
  { rcases IH _ _ _ (search_tree_and_left _ _ _ p q hΓ) with ⟨I₁, d₁⟩,
    rcases IH _ _ _ (search_tree_and_right _ _ _ p q hΓ) with ⟨I₂, d₂⟩,
    refine ⟨i :: I₁ ++ I₂, synthetic_main_lemma_aux_and d₁ d₂⟩ },      
  case or : p q
  { rcases IH _ _ _ (search_tree_or _ _ _ p q hΓ) with ⟨I, d⟩,
    refine ⟨i :: I, synthetic_main_lemma_aux_or d⟩ },  
  case fal : p
  { rcases IH _ _ _ (search_tree_fal _ _ _ p hΓ) with ⟨I, d⟩,
    refine ⟨i :: I, synthetic_main_lemma_aux_all d⟩ },
  case ex : p
  { rcases IH _ _ _ (search_tree_ex _ _ _ p hΓ) with ⟨I, d⟩,
    refine ⟨i :: I, synthetic_main_lemma_aux_ex d⟩ }
end

lemma synthetic_main_lemma (Γ : list (subformula L m 0)) {i s}
  (h : accessible M Δ ⟨i, s, _, Γ⟩) : 
  ∃ (I : list ℕ), ⊢ᵀ Γ.to_finset ∪ (I.bind (λ i, (index_of_set M i).to_list)).to_finset :=
by simpa using synthetic_main_lemma_aux H ⟨_, h⟩

end well_founded

end search_tree

end Tait

end fol