import QL.FOL.Tait.calculus QL.FOL.Tait.coding lib.order

universes u v

namespace fol
open_locale logic_symbol aclogic

namespace Tait

variables {L : language.{u}} {m n : ℕ}

open subformula

def is_terminal (Δ : list (subformula L m 0)) : Prop := ∃ {k} (r : L.pr k) (v), relation r v ∈ Δ ∧ neg_relation r v ∈ Δ

variables {L} [∀ k, encodable (L.fn k)] [∀ k, encodable (L.pr k)]
open encodable

@[simp] def instance_enum (p : subformula L m 1) : ℕ → list (formula L m)
| 0       := []
| (s + 1) := instance_enum s ++ (option.map (λ t, subst t p) $ fol.subterm.of_nat  L m 0 s).to_list

def decomp : ℕ → list (subformula L m 0) → set (Σ m, list (subformula L m 0))
| i []                      := { ⟨m, []⟩}
| i (relation r v :: Γ)     := { ⟨m, Γ ++ [relation r v]⟩, }
| i (neg_relation r v :: Γ) := { ⟨m, Γ ++ [neg_relation r v]⟩, }
| i (⊤ :: Γ)                := ∅
| i (⊥ :: Γ)                := { ⟨m, Γ ++ [⊥]⟩, }
| i (p ⊓ q :: Γ)            := { ⟨m, Γ ++ [p]⟩, ⟨m, Γ ++ [q]⟩, }
| i (p ⊔ q :: Γ)            := { ⟨m, Γ ++ [p, q]⟩, }
| i ((fal p) :: Γ)          := { ⟨m + 1, Γ.map mlift ++ [push p]⟩, }
| i ((ex p) :: Γ)           := { ⟨m, Γ ++ instance_enum p i ++ [∃'p]⟩, }

variables {L}

lemma decomp_tail_prefix {m₁ m₂} {Γ₁ : list (subformula L m₁ 0)} {Γ₂ : list (subformula L m₂ 0)} {i} :
  sigma.mk m₂ Γ₂ ∈ decomp i Γ₁ → Γ₁.tail.map to_uniform <+: Γ₂.map to_uniform :=
begin
  cases Γ₁ with p Γ₁; simp[decomp],
  { simp[list.nil_prefix] },
  { rcases p; simp[decomp, verum_eq, falsum_eq, and_eq, or_eq],
    { rintros rfl rfl, simp },
    { rintros rfl rfl, simp },
    { rintros rfl rfl, simp },
    { rintros (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩); simp },
    { rintros rfl rfl, simp },
    { rintros rfl rfl, simp[(∘)] },
    { rintros rfl rfl, simp } }
end


@[reducible] def search_label (L : language) := ℕ × Σ m, list (subformula L m 0)

noncomputable def index_of_set (M : set (sentence L)) (i : ℕ) : option (formula L m) :=
(option.guard (λ i, i ∈ to_nat '' M) i).bind (subformula.of_nat L m 0)

noncomputable def uniform_index_of_set (M : set (sentence L)) (i : ℕ) : option (uniform_subformula L 0) :=
(option.guard (λ i, i ∈ to_nat '' M) i).bind (encodable.decode₂ _)

@[simp] lemma index_of_set_to_uniform (M : set (sentence L)) (i : ℕ) :
  (index_of_set M i : option (formula L m)).map to_uniform = uniform_index_of_set M i :=
begin
  simp[index_of_set, uniform_index_of_set, option.map_bind'], ext p, simp, split,
  { rintros ⟨i, ⟨rfl, q, hq, rfl⟩, r, hr, rfl⟩,
    refine ⟨q.to_nat, ⟨rfl, q, hq, rfl⟩, _⟩,
    simp[←of_nat_eq_some.mp hr], refl },
  { rintros ⟨i, ⟨rfl, q, hq, rfl⟩, hp⟩,
    refine ⟨q.to_nat, ⟨rfl, q, hq, rfl⟩, _⟩, 
    have : p = q.to_uniform, { simp at hp, exact (option.some_inj.mp hp).symm },
    refine ⟨uniform_subformula.to_subformula p (by show p.uvars ≤ m; simp[this]), 
      by simp[of_nat_eq_some, this, of_nat_eq_som], by simp⟩ }
end

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
| intro : ∀ {m₁ m₂} (Γ₁ : list (subformula L m₁ 0)) (Γ₂ : list (subformula L m₂ 0)) (i : ℕ),
    ¬is_terminal Γ₁ → 
    sigma.mk m₂ Γ₂ ∈ decomp i Γ₁ →
    search_tree ⟨i + 1, m₂, Γ₂ ++ (index_of_set M i).to_list⟩ ⟨i, m₁, Γ₁⟩

notation l₁ ` ≺[` :50 M `] ` l₂ :50 := search_tree M l₁ l₂

namespace search_tree
variables {M : set (sentence L)} {Δ : list (sentence L)}

lemma search_tree_iff {l₁ l₂ : search_label L} : 
  l₂ ≺[M] l₁ ↔
  ∃ {m₁ m₂} (Γ₁ : list (subformula L m₁ 0)) (Γ₂ : list (subformula L m₂ 0)) (i : ℕ),
    ¬is_terminal Γ₁ ∧
    sigma.mk m₂ Γ₂ ∈ decomp i Γ₁ ∧
    l₁ = ⟨i, m₁, Γ₁⟩ ∧
    l₂ = ⟨i + 1, m₂, Γ₂ ++ (index_of_set M i).to_list⟩ :=
⟨by { rintros ⟨Γ₁, Γ₂, i, T, h⟩, refine ⟨_, _, Γ₁, Γ₂, i, T, h, rfl, rfl⟩ },
 by { rintros ⟨m₁, m₂, Γ₁, Γ₂, i, T, h, rfl, rfl⟩, exact search_tree.intro Γ₁ Γ₂ i T h }⟩

variables (M Δ)

@[reducible] def search_label.top : search_label L := ⟨0, sigma.mk 0 Δ⟩

inductive accessible (Δ : list (sentence L)) : search_label L → Prop
| top : accessible (search_label.top Δ)
| lt : ∀ {l₁ l₂}, l₁ ≺[M] l₂ → accessible l₂ → accessible l₁

def accessible_label := { l // accessible M Δ l }

def accessible_search_tree : accessible_label M Δ → accessible_label M Δ → Prop :=
λ l₁ l₂, l₁.val ≺[M] l₂.val 

local infix ` ≺ `:50 := accessible_search_tree M Δ

@[simp] lemma Axl_bot (l) (Γ : list (formula L m)) (h : is_terminal Γ) {i} : ¬search_tree M l ⟨i, m, Γ⟩ :=
by rintros ⟨⟩; contradiction

section well_founded
variables {M Δ} (H : well_founded (accessible_search_tree M Δ))

def accessible_search_tree.recursion {C : accessible_label M Δ → Sort*} 
  (l) (h : Π l₁, (Π l₂, l₂ ≺ l₁ → C l₂) → C l₁) : C l :=
well_founded.recursion H l h

lemma search_tree_nil (i) {m} : ⟨i + 1, m, (index_of_set M i).to_list⟩ ≺[M] ⟨i, m, []⟩ := 
by { refine search_tree.intro [] [] i _ (by simp[decomp]), { simp[is_terminal] } }

lemma search_tree_falsum (i) {m} (Γ : list (formula L m)) (h : ¬is_terminal (⊥ :: Γ)) :
  ⟨i + 1, m, Γ ++ [⊥] ++ (index_of_set M i).to_list⟩ ≺[M] ⟨i, m, ⊥ :: Γ⟩ := 
search_tree.intro _ _ _ h (by simp[decomp])

lemma search_tree_relation (i) {m} (Γ : list (formula L m)) {k} (r : L.pr k) (v : fin k → subterm L m 0)
  (h : ¬is_terminal (relation r v :: Γ)) :
  ⟨i + 1, m, Γ ++ [relation r v] ++ (index_of_set M i).to_list⟩ ≺[M] ⟨i, m, relation r v :: Γ⟩ := 
search_tree.intro _ _ _ h (by simp[decomp])

lemma search_tree_neg_relation (i) {m} (Γ : list (formula L m)) {k} (r : L.pr k) (v : fin k → subterm L m 0)
  (h : ¬is_terminal (neg_relation r v :: Γ)) :
  ⟨i + 1, m, Γ ++ [neg_relation r v] ++ (index_of_set M i).to_list⟩ ≺[M] ⟨i, m, neg_relation r v :: Γ⟩ := 
search_tree.intro _ _ _ h (by simp[decomp])

lemma search_tree_and_left (i) {m} (Γ : list (formula L m)) (p q : formula L m)
  (h : ¬is_terminal (p ⊓ q :: Γ)) :
  ⟨i + 1, m, Γ ++ [p] ++ (index_of_set M i).to_list⟩ ≺[M] ⟨i, m, p ⊓ q :: Γ⟩ := 
search_tree.intro _ _ _ h (by simp[decomp])

lemma search_tree_and_right (i) {m} (Γ : list (formula L m)) (p q : formula L m)
  (h : ¬is_terminal (p ⊓ q :: Γ)) :
  ⟨i + 1, m, Γ ++ [q] ++ (index_of_set M i).to_list⟩ ≺[M] ⟨i, m, p ⊓ q :: Γ⟩ := 
search_tree.intro _ _ _ h (by simp[decomp])

lemma search_tree_or (i) {m} (Γ : list (formula L m)) (p q : formula L m)
  (h : ¬is_terminal (p ⊔ q :: Γ)) :
  ⟨i + 1, m, Γ ++ [p, q] ++ (index_of_set M i).to_list⟩ ≺[M] ⟨i, m, p ⊔ q :: Γ⟩ := 
search_tree.intro _ _ _ h (by simp[decomp])

lemma search_tree_fal (i) {m} (Γ : list (formula L m)) (p : subformula L m 1)
  (h : ¬is_terminal ((∀'p) :: Γ)) :
  ⟨i + 1, m + 1, Γ.map mlift ++ [p.push] ++ (index_of_set M i).to_list⟩ ≺[M] ⟨i, m, (∀'p) :: Γ⟩ := 
search_tree.intro _ _ _ h (by simp[decomp, ←fal_eq])

lemma search_tree_ex (i) {m} (Γ : list (formula L m)) (p : subformula L m 1)
  (h : ¬is_terminal ((∃'p) :: Γ)) :
  ⟨i + 1, m, Γ ++ instance_enum p i ++ [∃'p] ++ (index_of_set M i).to_list⟩ ≺[M] ⟨i, m, (∃'p) :: Γ⟩ := 
search_tree.intro ((∃'p) :: Γ) _ i h (by simp[decomp, ←ex_eq])

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

lemma exists_of_instances (p : subformula L m 1) {Γ} (i) : ⊢ᵀ (instance_enum p i).to_finset ∪ Γ → ⊢ᵀ insert (∃'p) Γ :=
begin
  induction i with i IH generalizing Γ; simp,
  { assume h, exact derivable.weakening h (finset.subset_insert _ _) },
  { cases subterm.of_nat L m 0 i with t; simp; assume h,
    { exact IH h },
    { have : ⊢ᵀ insert (subst t p) (insert (∃'p) Γ), from derivable.cast (IH h) (by ext; simp; tauto),
      exact derivable.cast (derivable.ex t p this) (by ext; simp) } }
end

private lemma synthetic_main_lemma_aux_ex {Γ : list (formula L m)} {p : subformula L m 1} {i} {I : list ℕ}
  (d : ⊢ᵀ (Γ ++ instance_enum p i ++ [(∃'p : subformula _ _ _)] ++ (index_of_set M i).to_list).to_finset ∪
    (I.bind (λ i, (index_of_set M i).to_list)).to_finset) : 
  ⊢ᵀ ((∃'p) :: Γ).to_finset ∪ ((i :: I).bind (λ i, (index_of_set M i).to_list)).to_finset :=
begin
  simp at d,
  have : ⊢ᵀ (instance_enum p i).to_finset ∪
    insert (∃'p : subformula _ _ _) (Γ.to_finset ∪ ((i :: I).bind (λ (i : ℕ), (index_of_set M i).to_list)).to_finset),
  from derivable.cast d (by ext; simp[-list.mem_map, -list.mem_bind]; tauto),
  exact derivable.cast (exists_of_instances p i this) (by ext; simp)
end

include H

lemma synthetic_main_lemma_aux (l : accessible_label M Δ) : ∃ I : list ℕ,
  ⊢ᵀ l.val.2.2.to_finset ∪ list.to_finset (I.bind (λ i, (index_of_set M i).to_list)) :=
begin
  apply accessible_search_tree.recursion H l,
  rintros ⟨⟨i, m, Γ⟩, accΓ⟩ IH,
  have IH : ∀ (i₂) {m₂} (Γ₂ : list (subformula L m₂ 0)),
    ⟨i₂, m₂, Γ₂⟩ ≺[M] ⟨i, m, Γ⟩ →
    ∃ I : list ℕ, ⊢ᵀ Γ₂.to_finset ∪ list.to_finset (I.bind (λ i, (index_of_set M i).to_list)),
  { intros i₂ m₂ Γ₂ h, 
    have : accessible M Δ ⟨i₂, m₂, Γ₂⟩, from accessible.lt h accΓ,
    simpa using IH ⟨⟨i₂, m₂, Γ₂⟩, this⟩ h },
  show ∃ (I : list ℕ), ⊢ᵀ Γ.to_finset ∪ (I.bind (λ i, (index_of_set M i).to_list)).to_finset,
  by_cases hΓ : is_terminal Γ,
  { rcases hΓ with ⟨k, r, v, hΓ, hΓ_neg⟩,
    refine ⟨[], by simp; exact derivable.AxL r v (by simp; refine hΓ) (by simp; refine hΓ_neg)⟩ },
  cases Γ with p Γ,
  { rcases IH _ _ (search_tree_nil _) with ⟨I, d⟩,
    refine ⟨i :: I, derivable.cast d (by ext; simp)⟩ },
  cases p,
  case verum { refine ⟨[], derivable.verum (by simp[verum_eq])⟩ },
  case falsum
  { rcases IH _ _ (search_tree_falsum _ _ hΓ) with ⟨I, d⟩,
    refine ⟨i :: I, derivable.cast d (by ext; simp[falsum_eq])⟩ },  
  case relation : k r v
  { rcases IH _ _ (search_tree_relation _ _ r v hΓ) with ⟨I, d⟩,
    refine ⟨i :: I, derivable.cast d (by ext; simp)⟩ },
  case neg_relation : k r v
  { rcases IH _ _ (search_tree_neg_relation _ _ r v hΓ) with ⟨I, d⟩,
    refine ⟨i :: I, derivable.cast d (by ext; simp)⟩ },
  case and : p q
  { rcases IH _ _ (search_tree_and_left _ _ p q hΓ) with ⟨I₁, d₁⟩,
    rcases IH _ _ (search_tree_and_right _ _ p q hΓ) with ⟨I₂, d₂⟩,
    refine ⟨i :: I₁ ++ I₂, synthetic_main_lemma_aux_and d₁ d₂⟩ },      
  case or : p q
  { rcases IH _ _ (search_tree_or _ _ p q hΓ) with ⟨I, d⟩,
    refine ⟨i :: I, synthetic_main_lemma_aux_or d⟩ },  
  case fal : p
  { rcases IH _ _ (search_tree_fal _ _ p hΓ) with ⟨I, d⟩,
    refine ⟨i :: I, synthetic_main_lemma_aux_all d⟩ },
  case ex : p
  { rcases IH _ _ (search_tree_ex _ _ p hΓ) with ⟨I, d⟩,
    refine ⟨i :: I, synthetic_main_lemma_aux_ex d⟩ }
end

lemma synthetic_main_lemma (Γ : list (subformula L m 0)) {i}
  (h : accessible M Δ ⟨i, m, Γ⟩) : 
  ∃ (I : list ℕ), ⊢ᵀ Γ.to_finset ∪ (I.bind (λ i, (index_of_set M i).to_list)).to_finset :=
by simpa using synthetic_main_lemma_aux H ⟨_, h⟩

lemma synthetic_main_lemma' : ∃ Γ : finset (sentence L), ↑Γ ⊆ M ∧ ⊢ᵀ Δ.to_finset ∪ Γ :=
begin
  have : ∃ (I : list ℕ), ⊢ᵀ Δ.to_finset ∪ (I.bind (λ i, (index_of_set M i).to_list)).to_finset,
  from synthetic_main_lemma H Δ accessible.top,
  rcases this with ⟨I, h⟩,
  refine ⟨(I.bind (λ i, (index_of_set M i).to_list)).to_finset,
    by { intros x, simp, intros i hi hx, simpa using index_of_neg_set_eq_some hx}, h⟩
end

end well_founded

section non_well_founded
variables {M Δ} (H : ¬well_founded (accessible_search_tree M Δ))

include H

lemma top_inaccessible : ¬acc (accessible_search_tree M Δ) ⟨search_label.top Δ, accessible.top⟩ :=
begin
  assume A,
  suffices : well_founded (accessible_search_tree M Δ), by contradiction,
  refine ⟨_⟩,
  rintros ⟨l, hl⟩, induction hl,
  case top { exact A },
  case lt : l₁ l₂ h hl₂ IH { refine IH.inv h }
end

noncomputable def chain : ℕ → search_label L :=
  λ i, (descending_chain (accessible_search_tree M Δ) ⟨search_label.top Δ, accessible.top⟩ i).val

noncomputable def uniform_chain : ℕ → list (uniform_subformula L 0) :=
λ i, (chain H i).2.2.map to_uniform

@[simp] lemma chain_zero : chain H 0 = ⟨0, 0, Δ⟩ := by refl

@[simp] lemma uniform_chain_zero : uniform_chain H 0 = Δ.map to_uniform := by refl

@[simp] lemma chain_lt (i) : chain H (i + 1) ≺[M] chain H i :=
infinite_descending_chain_of_non_acc (accessible_search_tree M Δ) ⟨search_label.top Δ, accessible.top⟩ (top_inaccessible H) i

@[simp] lemma chain_fst (i) : (chain H i).1 = i :=
begin
  induction i with i IH,
  { simp },
  { rcases search_tree_iff.mp (chain_lt H i) with ⟨m₁', m₂, Γ₁', Γ₂, i', T, h, e₁, e₂⟩,
    have : i = i', by simpa[IH] using congr_arg prod.fst e₁,
    rcases this with rfl,
    simpa using congr_arg prod.fst e₂ }
end

lemma chain_fst' (i) : (i, (chain H i).snd) = chain H i :=
by ext; simp

lemma chain_succ (i : ℕ) {m₁} (Γ₁ : list (subformula L m₁ 0)) (hΓ₁ : chain H i = (i, sigma.mk m₁ Γ₁)) :
  ∃ {m₂} (Γ₂ : list (subformula L m₂ 0)),
    sigma.mk m₂ Γ₂ ∈ decomp i Γ₁ ∧ chain H (i + 1) = (i + 1, sigma.mk m₂ (Γ₂ ++ (index_of_set M i).to_list)) :=
begin
  rcases search_tree_iff.mp (chain_lt H i) with ⟨m₁', m₂, Γ₁', Γ₂, i', T, h, e₁, e₂⟩,
  have : i = i' ∧ m₁ = m₁',
  { refine ⟨by simpa using congr_arg prod.fst e₁,
      by simpa[hΓ₁] using congr_arg sigma.fst (congr_arg prod.snd e₁)⟩ },
  rcases this with ⟨rfl, rfl⟩,
  have : Γ₁ = Γ₁', by simpa[hΓ₁] using congr_arg prod.snd e₁,
  rcases this with rfl,
  refine ⟨m₂, Γ₂, h, e₂⟩
end

lemma uniform_chain_succ (i : ℕ) : ∃ {m₁ m₂} (Γ₁ : list (subformula L m₁ 0)) (Γ₂ : list (subformula L m₂ 0)),
    uniform_chain H i = Γ₁.map to_uniform ∧ sigma.mk m₂ Γ₂ ∈ decomp i Γ₁ ∧
    uniform_chain H (i + 1) = Γ₂.map to_uniform ++ (uniform_index_of_set M i).to_list :=
begin
  rcases chain_succ H i (chain H i).2.2 (by simp[chain_fst']) with ⟨m₂, Γ₂, h, c⟩,
  refine ⟨(chain H i).2.1, m₂, (chain H i).2.2, Γ₂, rfl, h, _⟩,
  simp[uniform_chain],
  rw [c, show (i + 1, sigma.mk m₂ (Γ₂ ++ (index_of_set M i).to_list)).snd.snd = Γ₂ ++ (index_of_set M i).to_list, by refl],
  simp[list.map_to_list_option]
end

lemma eq_head_of_mem_chain {i} {p} (hp : p ∈ uniform_chain H i) : ∃ z Γ, uniform_chain H (i + z) = p :: Γ :=
begin
  haveI : inhabited (uniform_subformula L 0), from ⟨p⟩,
  suffices : ∀ (z i) (hz : z < (uniform_chain H i).length), ∃ Γ,
    uniform_chain H (i + z) = (uniform_chain H i).nth_le z hz :: Γ,
  { rcases list.mem_iff_nth_le.mp hp with ⟨z, hz, rfl⟩,
    rcases this z i hz with ⟨Γ, hΓ⟩,
    refine ⟨z, Γ, hΓ⟩ },
  intros z, induction z with z IH,
  { intros i hz, simp[list.nth_le_zero], 
    refine ⟨(uniform_chain H i).tail,
      by {symmetry, refine list.cons_head_tail (by { intros A, simp[A] at hz, contradiction })  }⟩ },
  { intros i hz,
    rcases uniform_chain_succ H i with ⟨m₁, m₂, Γ₁, Γ₂, hi, hdecomp, hisucc⟩,
    have hprefix : Γ₁.tail.map to_uniform <+: Γ₂.map to_uniform, from decomp_tail_prefix hdecomp,
    have : Γ₁.length ≤ Γ₂.length + 1, by simpa using list.is_prefix.length_le hprefix,
    have hz₁ : z + 1 < Γ₁.length, by simpa[hi] using hz,
    have hz₂ : z < Γ₂.length, from nat.succ_lt_succ_iff.mp (lt_of_lt_of_le hz₁ this),
    rcases IH (i + 1) (by simpa[hisucc] using nat.lt_add_right z _ _ hz₂) with ⟨Γ, hΓ⟩,    
    have e₁ : (Γ₂.nth_le z _).to_uniform = (uniform_chain H (i + 1)).nth_le z _,
      by simpa using list.prefix_nth_le (list.map to_uniform Γ₂) (uniform_chain H (i + 1)) z (by simpa using hz₂) (by simp[hisucc]),
    have e₂ : (Γ₁.nth_le (z + 1) hz₁).to_uniform = (Γ₂.nth_le z hz₂).to_uniform,
    { have : (list.map to_uniform Γ₁.tail).nth_le z _ = (list.map to_uniform Γ₂).nth_le z _,
      from list.prefix_nth_le _ _ z (by simp; exact lt_tsub_iff_right.mpr hz₁) hprefix,
      have : (list.map to_uniform Γ₁).nth_le (z + 1) (by simpa using hz₁) = (list.map to_uniform Γ₂).nth_le z _,
      from eq.trans (by { symmetry, simp, rw list.nth_le_tail, simp, }) this,
      simpa using this },
    simp[show i + z.succ = i + 1 + z, by simp[←nat.add_one, add_comm z, add_assoc]],
    refine ⟨Γ, by { simp[hΓ, hi], exact eq.trans e₁.symm e₂.symm }⟩ }
end

def chain_union : set (uniform_subformula L 0) := {p | ∃ i, p ∈ uniform_chain H i}

lemma top_nonmem : uniform_subformula.verum ∉ chain_union H:=
begin
  rintros ⟨i, A⟩,
  rcases eq_head_of_mem_chain H A with ⟨z, Γ, hΓ⟩,

end

end non_well_founded

end search_tree

end Tait

end fol