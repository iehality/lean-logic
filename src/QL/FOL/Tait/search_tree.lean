import QL.FOL.Tait.semantics QL.FOL.Tait.coding lib.order

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
| (s + 1) := instance_enum s ++ (option.map (λ t, subst t p) $ fol.subterm.of_nat L m 0 s).to_list

lemma mem_instance_enum_of_lt (t : subterm L m 0) (p : subformula L m 1) (i) :
  t.to_nat < i → subst t p ∈ instance_enum p i :=
begin
  induction i with i IH,
  { simp },
  { simp, 
    intros h,
    have : t.to_nat < i ∨ t.to_nat = i, from nat.lt_succ_iff_lt_or_eq.mp h,
    rcases this with (lt | rfl),
    { refine or.inl (IH lt) },
    { refine or.inr ⟨t, by simp, rfl⟩ } }
end

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
  sigma.mk m₂ Γ₂ ∈ decomp i Γ₁ → Γ₁.tail.map uniform <+: Γ₂.map uniform :=
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

lemma decomp_le {m₁ m₂} {Γ₁ : list (subformula L m₁ 0)} {Γ₂ : list (subformula L m₂ 0)} {i} :
  sigma.mk m₂ Γ₂ ∈ decomp i Γ₁ → m₁ ≤ m₂ :=
begin
  cases Γ₁ with p Γ₁,
  {  simp[decomp], rintros rfl rfl, simp },
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

noncomputable def uniform_index_of_set (M : set (sentence L)) (i : ℕ) : option (uniform_formula L) :=
(option.guard (λ i, i ∈ to_nat '' M) i).bind (encodable.decode₂ _)

lemma uniform_index_of_set_of_nat (M : set (sentence L)) {p : sentence L} (hp : p ∈ M) :
  uniform_index_of_set M p.to_nat = some p.uniform :=
by simp[uniform_index_of_set, hp]; refl

@[simp] lemma index_of_set_uniform (M : set (sentence L)) (i : ℕ) :
  (index_of_set M i : option (formula L m)).map uniform = uniform_index_of_set M i :=
begin
  simp[index_of_set, uniform_index_of_set, option.map_bind'], ext p, simp, split,
  { rintros ⟨i, ⟨rfl, q, hq, rfl⟩, r, hr, rfl⟩,
    refine ⟨q.to_nat, ⟨rfl, q, hq, rfl⟩, _⟩,
    simp[←of_nat_eq_some.mp hr], refl },
  { rintros ⟨i, ⟨rfl, q, hq, rfl⟩, hp⟩,
    refine ⟨q.to_nat, ⟨rfl, q, hq, rfl⟩, _⟩, 
    have : p = q.uniform, { simp at hp, exact (option.some_inj.mp hp).symm },
    refine ⟨uniform_subformula.to_subformula p (by show p.arity ≤ m; simp[this]), 
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
    let p' : formula L m := σ.uniform.to_subformula (le_trans (subformula_arity σ) (by simp)),
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
variables {M Δ} (wf : well_founded (accessible_search_tree M Δ))

def accessible_search_tree.recursion {C : accessible_label M Δ → Sort*} 
  (l) (h : Π l₁, (Π l₂, l₂ ≺ l₁ → C l₂) → C l₁) : C l :=
well_founded.recursion wf l h

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

include wf

lemma synthetic_main_lemma_aux (l : accessible_label M Δ) : ∃ I : list ℕ,
  ⊢ᵀ l.val.2.2.to_finset ∪ list.to_finset (I.bind (λ i, (index_of_set M i).to_list)) :=
begin
  apply accessible_search_tree.recursion wf l,
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
by simpa using synthetic_main_lemma_aux wf ⟨_, h⟩

lemma synthetic_main_lemma' : ∃ Γ : finset (sentence L), ↑Γ ⊆ M ∧ ⊢ᵀ Δ.to_finset ∪ Γ :=
begin
  have : ∃ (I : list ℕ), ⊢ᵀ Δ.to_finset ∪ (I.bind (λ i, (index_of_set M i).to_list)).to_finset,
  from synthetic_main_lemma wf Δ accessible.top,
  rcases this with ⟨I, h⟩,
  refine ⟨(I.bind (λ i, (index_of_set M i).to_list)).to_finset,
    by { intros x, simp, intros i hi hx, simpa using index_of_neg_set_eq_some hx}, h⟩
end

end well_founded

section non_well_founded
variables {M Δ} (wf : ¬well_founded (accessible_search_tree M Δ))

include wf

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

def var_domain : set ℕ := set.range (λ i, (chain wf i).2.1)

def term_domain := {t : uniform_term L // ∃ s ∈ var_domain wf, t.arity ≤ s}

noncomputable def uniform_chain : ℕ → list (uniform_formula L) :=
λ i, (chain wf i).2.2.map uniform

@[simp] lemma chain_zero : chain wf 0 = ⟨0, 0, Δ⟩ := by refl

@[simp] lemma uniform_chain_zero : uniform_chain wf 0 = Δ.map uniform := by refl

@[simp] lemma chain_lt (i) : chain wf (i + 1) ≺[M] chain wf i :=
infinite_descending_chain_of_non_acc (accessible_search_tree M Δ) ⟨search_label.top Δ, accessible.top⟩ (top_inaccessible wf) i

@[simp] lemma chain_fst (i) : (chain wf i).1 = i :=
begin
  induction i with i IH,
  { simp },
  { rcases search_tree_iff.mp (chain_lt wf i) with ⟨m₁', m₂, Γ₁', Γ₂, i', T, h, e₁, e₂⟩,
    have : i = i', by simpa[IH] using congr_arg prod.fst e₁,
    rcases this with rfl,
    simpa using congr_arg prod.fst e₂ }
end

lemma chain_fst' (i) : (i, (chain wf i).snd) = chain wf i :=
by ext; simp

lemma chain_succ (i : ℕ) {m₁} (Γ₁ : list (subformula L m₁ 0)) (hΓ₁ : chain wf i = (i, sigma.mk m₁ Γ₁)) :
  ∃ {m₂} (Γ₂ : list (subformula L m₂ 0)),
    sigma.mk m₂ Γ₂ ∈ decomp i Γ₁ ∧ chain wf (i + 1) = (i + 1, sigma.mk m₂ (Γ₂ ++ (index_of_set M i).to_list)) :=
begin
  rcases search_tree_iff.mp (chain_lt wf i) with ⟨m₁', m₂, Γ₁', Γ₂, i', T, h, e₁, e₂⟩,
  have : i = i' ∧ m₁ = m₁',
  { refine ⟨by simpa using congr_arg prod.fst e₁,
      by simpa[hΓ₁] using congr_arg sigma.fst (congr_arg prod.snd e₁)⟩ },
  rcases this with ⟨rfl, rfl⟩,
  have : Γ₁ = Γ₁', by simpa[hΓ₁] using congr_arg prod.snd e₁,
  rcases this with rfl,
  refine ⟨m₂, Γ₂, h, e₂⟩
end

@[simp] lemma chain_uvar_mono : ∀ {i j}, i ≤ j → (chain wf i).2.1 ≤ (chain wf j).2.1 :=
begin
  suffices : ∀ {i j}, (chain wf i).2.1 ≤ (chain wf (i + j)).2.1,
  { intros i j hij, have := @this i (j - i),
    simpa[nat.add_sub_of_le hij] using this },
  intros i j, induction j with j IH,
  { simp },
  { rcases chain_succ wf (i + j) (chain wf (i + j)).2.2 (by { ext, simp, refl }) with ⟨m, Γ, hdecomp, hc⟩,
    have : (chain wf (i + j.succ)).snd.fst = m, by simp[←nat.add_one, ←add_assoc, hc],
    simp[this], exact le_trans IH (decomp_le hdecomp) }
end

lemma uniform_chain_succ (i : ℕ) : ∃ {m₁ m₂} (Γ₁ : list (subformula L m₁ 0)) (Γ₂ : list (subformula L m₂ 0)),
    uniform_chain wf i = Γ₁.map uniform ∧ sigma.mk m₂ Γ₂ ∈ decomp i Γ₁ ∧
    uniform_chain wf (i + 1) = Γ₂.map uniform ++ (uniform_index_of_set M i).to_list :=
begin
  rcases chain_succ wf i (chain wf i).2.2 (by simp[chain_fst']) with ⟨m₂, Γ₂, h, c⟩,
  refine ⟨(chain wf i).2.1, m₂, (chain wf i).2.2, Γ₂, rfl, h, _⟩,
  simp[uniform_chain],
  rw [c, show (i + 1, sigma.mk m₂ (Γ₂ ++ (index_of_set M i).to_list)).snd.snd = Γ₂ ++ (index_of_set M i).to_list, by refl],
  simp[list.map_to_list_option]
end

lemma eq_head_of_mem_uniform_chain {i} {p} (hp : p ∈ uniform_chain wf i) : ∃ z Γ, uniform_chain wf (i + z) = p :: Γ :=
begin
  haveI : inhabited (uniform_formula L), from ⟨p⟩,
  suffices : ∀ (z i) (hz : z < (uniform_chain wf i).length), ∃ Γ,
    uniform_chain wf (i + z) = (uniform_chain wf i).nth_le z hz :: Γ,
  { rcases list.mem_iff_nth_le.mp hp with ⟨z, hz, rfl⟩,
    rcases this z i hz with ⟨Γ, hΓ⟩,
    refine ⟨z, Γ, hΓ⟩ },
  intros z, induction z with z IH,
  { intros i hz, simp[list.nth_le_zero], 
    refine ⟨(uniform_chain wf i).tail,
      by {symmetry, refine list.cons_head_tail (by { intros A, simp[A] at hz, contradiction })  }⟩ },
  { intros i hz,
    rcases uniform_chain_succ wf i with ⟨m₁, m₂, Γ₁, Γ₂, hi, hdecomp, hisucc⟩,
    have hprefix : Γ₁.tail.map uniform <+: Γ₂.map uniform, from decomp_tail_prefix hdecomp,
    have : Γ₁.length ≤ Γ₂.length + 1, by simpa using list.is_prefix.length_le hprefix,
    have hz₁ : z + 1 < Γ₁.length, by simpa[hi] using hz,
    have hz₂ : z < Γ₂.length, from nat.succ_lt_succ_iff.mp (lt_of_lt_of_le hz₁ this),
    rcases IH (i + 1) (by simpa[hisucc] using nat.lt_add_right z _ _ hz₂) with ⟨Γ, hΓ⟩,    
    have e₁ : (Γ₂.nth_le z _).uniform = (uniform_chain wf (i + 1)).nth_le z _,
      by simpa using list.prefix_nth_le (list.map uniform Γ₂) (uniform_chain wf (i + 1)) z (by simpa using hz₂) (by simp[hisucc]),
    have e₂ : (Γ₁.nth_le (z + 1) hz₁).uniform = (Γ₂.nth_le z hz₂).uniform,
    { have : (list.map uniform Γ₁.tail).nth_le z _ = (list.map uniform Γ₂).nth_le z _,
      from list.prefix_nth_le _ _ z (by simp; exact lt_tsub_iff_right.mpr hz₁) hprefix,
      have : (list.map uniform Γ₁).nth_le (z + 1) (by simpa using hz₁) = (list.map uniform Γ₂).nth_le z _,
      from eq.trans (by { symmetry, simp, rw list.nth_le_tail, simp, }) this,
      simpa using this },
    simp[show i + z.succ = i + 1 + z, by simp[←nat.add_one, add_comm z, add_assoc]],
    refine ⟨Γ, by { simp[hΓ, hi], exact eq.trans e₁.symm e₂.symm }⟩ }
end

lemma eq_head_of_mem_chain {i} {m} {Γ} (hi : chain wf i = (i, sigma.mk m Γ)) {p} (hp : p ∈ Γ) :
  ∃ z {m'} (Γ' : list (subformula L m' 0)) p', chain wf (i + z) = (i + z, sigma.mk m' (p' :: Γ')) ∧ p'.uniform = p.uniform :=
begin
  have : uniform_chain wf i = Γ.map uniform,
  { simp[uniform_chain], rw hi },
  have : p.uniform ∈ uniform_chain wf i, { simp[this], refine ⟨p, hp, by simp⟩ },
  rcases eq_head_of_mem_uniform_chain wf this with ⟨z, Γ₂, hΓ₂⟩,
  simp[uniform_chain] at hΓ₂,
  rcases C : (chain wf (i + z)).2.2 with (_ | ⟨p', Γ'⟩),
  { simp[C] at hΓ₂, contradiction },
  { refine ⟨z, (chain wf (i + z)).2.1, Γ', p', by ext; simp[C], by simp[C] at hΓ₂; exact hΓ₂.1⟩ }
end

lemma eq_head_of_mem_chain' {i} {p} (hp : p ∈ uniform_chain wf i) :
  ∃ z {m'} (Γ' : list (subformula L m' 0)) p', chain wf (i + z) = (i + z, sigma.mk m' (p' :: Γ')) ∧ p'.uniform = p :=
begin
  rcases eq_head_of_mem_uniform_chain wf hp with ⟨z, Γ₂, hΓ₂⟩,
  simp[uniform_chain] at hΓ₂,
  rcases C : (chain wf (i + z)).2.2 with (_ | ⟨p', Γ'⟩),
  { simp[C] at hΓ₂, contradiction },
  { refine ⟨z, (chain wf (i + z)).2.1, Γ', p', by ext; simp[C], by simp[C] at hΓ₂; exact hΓ₂.1⟩ }
end

def chain_union : set (uniform_formula L) := {p | ∃ i, p ∈ uniform_chain wf i}

local notation `⛓️`:= chain_union wf 

lemma root_mem {p : sentence L} (hp : p ∈ M) : p.uniform ∈ ⛓️ :=
⟨p.to_nat + 1,
  begin
    rcases uniform_chain_succ wf p.to_nat with ⟨m₁, m₂, Γ₁, Γ₂, _, _, h⟩,
    have : uniform_index_of_set M (to_nat p) = some (uniform p), from uniform_index_of_set_of_nat M hp,
    simp[h, this]
  end⟩

lemma top_nonmem : ⊤ ∉ ⛓️:=
begin
  rintros ⟨i, A⟩,
  rcases eq_head_of_mem_chain' wf A with ⟨z, m, Γ, p, hc, hverum⟩,
  have : p = ⊤,
  { cases p; simp at hverum; try { contradiction },
    { refl } },
  rcases this with rfl,
  rcases chain_succ wf _ _ hc with ⟨m₂, Γ₂, hdecomp, hcsucc⟩,
  simp[decomp] at hdecomp, contradiction
end

lemma or_mem (p q : uniform_formula L) : p ⊔ q ∈ ⛓️ → p ∈ ⛓️ ∧ q ∈ ⛓️ :=
begin
  rintros ⟨i, A⟩,
  rcases eq_head_of_mem_chain' wf A with ⟨z, m, Γ, r, hc, hr⟩,
  have : ∃ p' q' : subformula L m 0, r = p' ⊔ q' ∧ p'.uniform = p ∧ q'.uniform = q,
  { cases r; simp[←uniform_subformula.or_eq] at hr; try { contradiction },
    case or : p' q' { exact ⟨p', q', rfl, hr⟩ } },
  rcases this with ⟨p, q, rfl, rfl, rfl⟩,
  rcases chain_succ wf _ _ hc with ⟨m₂, Γ₂, hdecomp, hcsucc⟩,
  simp[decomp] at hdecomp,
  rcases hdecomp with ⟨rfl, rfl⟩,
  refine ⟨⟨i + z + 1, by { simp[uniform_chain, -list.mem_map], rw hcsucc, simp }⟩,
    ⟨i + z + 1, by { simp[uniform_chain, -list.mem_map], rw hcsucc, simp }⟩⟩
end

lemma and_mem (p q : uniform_formula L) : p ⊓ q ∈ ⛓️ → p ∈ ⛓️ ∨ q ∈ ⛓️ :=
begin
  rintros ⟨i, A⟩,
  rcases eq_head_of_mem_chain' wf A with ⟨z, m, Γ, r, hc, hr⟩,
  have : ∃ p' q' : subformula L m 0, r = p' ⊓ q' ∧ p'.uniform = p ∧ q'.uniform = q,
  { cases r; simp[←uniform_subformula.and_eq] at hr; try { contradiction },
    case and : p' q' { exact ⟨p', q', rfl, hr⟩ } },
  rcases this with ⟨p, q, rfl, rfl, rfl⟩,
  rcases chain_succ wf _ _ hc with ⟨m₂, Γ₂, hdecomp, hcsucc⟩,
  simp[decomp] at hdecomp,
  rcases hdecomp with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩),
  refine or.inl ⟨i + z + 1, by { simp[uniform_chain, -list.mem_map], rw hcsucc, simp }⟩,
  refine or.inr ⟨i + z + 1, by { simp[uniform_chain, -list.mem_map], rw hcsucc, simp }⟩
end

lemma forall_mem (p : uniform_subformula L 1) :
  ∀'p ∈ ⛓️ → ∃ t : term_domain wf, uniform_subformula.subst t.val p ∈ ⛓️ :=
begin
  rintros ⟨i, A⟩,
  rcases eq_head_of_mem_chain' wf A with ⟨z, m, Γ, r, hc, hr⟩,
  have : ∃ p' : subformula L m 1, r = ∀' p' ∧ p'.uniform = p,
  { cases r; simp[←uniform_subformula.fal_eq] at hr; try { contradiction },
    case fal : p' { exact ⟨p', rfl, hr⟩ } },
  rcases this with ⟨p, rfl, rfl⟩,
  rcases chain_succ wf _ _ hc with ⟨m₂, Γ₂, hdecomp, hcsucc⟩,
  simp[←fal_eq, decomp] at hdecomp,
  rcases hdecomp with ⟨rfl, rfl⟩,
  refine ⟨⟨&&m, m + 1, ⟨i + z + 1, by simp[hcsucc]⟩, by simp⟩,
    i + z + 1, by { simp[uniform_chain, -list.mem_map], rw hcsucc, simp }⟩
end

lemma ex_infinitely_mem (p : uniform_subformula L 1) :
  ∃'p ∈ ⛓️ → ∀ i, ∃ j ≥ i, ∃'p ∈ uniform_chain wf j :=
begin
  intros h i,
  induction i with i IH,
  { rcases h with ⟨j, h⟩, refine ⟨j, by simp, h⟩ },
  { rcases IH with ⟨j, hj, h⟩,
    rcases eq_head_of_mem_chain' wf h with ⟨z, m, Γ, r, hc, hr⟩,
  have : ∃ p' : subformula L m 1, r = ∃' p' ∧ p'.uniform = p,
  { cases r; simp[←uniform_subformula.ex_eq] at hr; try { contradiction },
    case ex : p' { exact ⟨p', rfl, hr⟩ } },
  rcases this with ⟨p, rfl, rfl⟩,
  rcases chain_succ wf _ _ hc with ⟨m₂, Γ₂, hdecomp, hcsucc⟩,
  simp[←ex_eq, decomp] at hdecomp,
  rcases hdecomp with ⟨rfl, rfl⟩,
  refine ⟨j + z + 1, by { simp[←nat.add_one], from le_add_right hj},
    by { simp[uniform_chain, -list.mem_map], rw hcsucc,
         simp[←uniform_subformula.ex_eq] }⟩ }
end

lemma ex_mem (p : uniform_subformula L 1) :
  ∃'p ∈ ⛓️ → ∀ t : term_domain wf, uniform_subformula.subst t.val p ∈ ⛓️ :=
begin
  rintros h ⟨t, s, ⟨i', rfl⟩, ht⟩, simp at ht,
  let i := max i' (encode t + 1),
  have : ∃ j ≥ i, p.ex ∈ uniform_chain wf j, from ex_infinitely_mem wf p h i,
  rcases this with ⟨j, hj, h⟩,
  rcases eq_head_of_mem_chain' wf h with ⟨z, m, Γ, r, hc, hr⟩,
  have : ∃ p' : subformula L m 1, r = ∃' p' ∧ p'.uniform = p,
  { cases r; simp at hr; try { contradiction },
    case ex : p' { exact ⟨p', rfl, hr⟩ } },
  rcases this with ⟨p, rfl, rfl⟩,
  rcases chain_succ wf _ _ hc with ⟨m', Γ', hdecomp, hcsucc⟩,
  simp[←ex_eq, decomp] at hdecomp,
  rcases hdecomp with ⟨rfl, rfl⟩,
  have : i' ≤ j + z + 1, from le_trans (show i' ≤ i, by simp[i]) (by simp only [add_assoc]; exact le_add_right hj),
  have : t.arity ≤ m', from le_trans ht (by simpa[hcsucc] using chain_uvar_mono wf this),
  let u : subterm L m' 0 := t.to_subterm this,
  have : subst u p ∈ instance_enum p (j + z),
    from mem_instance_enum_of_lt u p (j + z) 
      (by { simp[u], refine lt_of_lt_of_le (show encode t < i, by simp[i]) (le_add_right hj) }),
  have : uniform_subformula.subst t p.uniform ∈ list.map uniform (instance_enum p (j + z)),
  by simpa[-list.mem_map] using list.mem_map_of_mem uniform this,
  refine ⟨j + z + 1, by { simp[uniform_chain, -list.mem_map], rw hcsucc,
    simp[-list.mem_map, this] }⟩
end

def model_fn {k} (f : L.fn k) (v : fin k → term_domain wf) : term_domain wf :=
⟨uniform_subterm.function f (λ i, (v i).val),
  begin
    cases k,
    { refine ⟨0, ⟨0, by simp⟩, by simp⟩ },
    { rcases classical.skolem.mp (λ i, (v i).property) with ⟨f, h⟩,
      simp,
      refine ⟨⨆ᶠ i, f i,
      by { rcases fintype_sup.exists_sup_index f with ⟨i, hi⟩,
           simp[←hi], rcases h i with ⟨h, _⟩, exact h },
      by { intros i, rcases h i with ⟨hi, lei⟩,
           refine le_trans lei (by simp) }⟩ }
  end⟩

def model_pr {k} (r : L.pr k) (v : fin k → term_domain wf) : Prop :=
uniform_subformula.neg_relation r (λ i, (v i).val) ∈ ⛓️

@[reducible] def model : Structure L :=
{ dom := term_domain wf,
  fn := λ k f, model_fn wf f,
  pr := λ k r, model_pr wf r }

def assignment : ℕ → ↥(model wf)

lemma model.val_term (e) (t : uniform_term L) : (uniform_subterm.val (model wf) e fin.nil t).val = t :=
by { induction t; simp*, }

lemma semantic_main_lemma : ∀ p ∈ ⛓️, model wf ⊧ᵀᵤ ∼p
| ⊤ h := by { have : ⊤ ∉ ⛓️, from top_nonmem wf, contradiction }
| ⊥ h := by simp[uniform_models]
| (p ⊓ q) h :=
    begin
      have : p ∈ ⛓️ ∨ q ∈ ⛓️, from and_mem wf _ _ h,
      rcases this with (h | h),
      { intros e, simp, refine or.inl (by simpa using semantic_main_lemma p h e) },
      { intros e, simp, refine or.inr (by simpa using semantic_main_lemma q h e) }
    end
| (p ⊔ q) h :=
    begin
      have : p ∈ ⛓️ ∧ q ∈ ⛓️, from or_mem wf _ _ h,
      rcases this with ⟨h₁, h₂⟩,
      intros e, simp,
      refine ⟨by simpa using semantic_main_lemma p h₁ e, 
        by simpa using semantic_main_lemma q h₂ e⟩
    end
| (uniform_subformula.relation r v) h := by { intros e,  simp[uniform_formula.val, model_pr], }

end non_well_founded

end search_tree

end Tait

end fol