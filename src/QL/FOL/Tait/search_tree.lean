import QL.FOL.Tait.semantics QL.FOL.Tait.coding lib.order

universes u v

namespace fol
open_locale logic_symbol aclogic

namespace Tait

variables {L : language.{u}} {m n : ℕ}

open subformula

def is_terminal (Δ : finset (bounded_subformula L m 0)) : Prop := ∃ {k} (r : L.pr k) (v), relation r v ∈ Δ ∧ neg_relation r v ∈ Δ

variables {L} [∀ k, encodable (L.fn k)] [∀ k, encodable (L.pr k)]
open encodable

@[simp] noncomputable def instance_enum (p : bounded_subformula L m 1) : ℕ → finset (bounded_formula L m)
| 0       := ∅
| (s + 1) := instance_enum s ∪ (option.map (λ t, subst t p) $ fol.subterm.of_index L m 0 s).to_finset

lemma mem_instance_enum_of_lt (t : bounded_subterm L m 0) (p : bounded_subformula L m 1) (i) :
  t.index < i → subst t p ∈ instance_enum p i :=
begin
  induction i with i IH,
  { simp },
  { simp, 
    intros h,
    have : t.index < i ∨ t.index = i, from nat.lt_succ_iff_lt_or_eq.mp h,
    rcases this with (lt | rfl),
    { refine or.inl (IH lt) },
    { refine or.inr ⟨t, by simp, rfl⟩ } }
end

--lemma cast_le_instance_enum {m₁ m₂} (h : m₁ ≤ m₂) (p : bounded_subformula L m₁ 1) (i) :
--  (instance_enum p i).image (cast_le h) = instance_enum (cast_le h p) i :=
--by { induction i with i IH, { simp }, { simp[finset.image_union, IH], } }


variables {L}

def decomp : ℕ → bounded_subformula L m 0 → finset (bounded_formula L m) → set (Σ m, finset (bounded_formula L m))
| i (relation r v)     Γ := { ⟨m, Γ⟩, }
| i (neg_relation r v) Γ := { ⟨m, Γ⟩, }
| i (⊤)                Γ := ∅
| i (⊥)                Γ := { ⟨m, Γ⟩, }
| i (p ⊓ q)            Γ := { ⟨m, insert p Γ⟩, ⟨m, insert q Γ⟩, }
| i (p ⊔ q)            Γ := { ⟨m, insert q (insert p Γ)⟩, }
| i (∀'p)              Γ := { ⟨m + 1, insert (push p) (finset_mlift Γ)⟩, }
| i (∃'p)              Γ := { ⟨m, instance_enum p i ∪ Γ⟩, }

lemma decomp_le {m₁ m₂} {p : bounded_subformula L m₁ 0} {Γ₁ : finset (bounded_formula L m₁)} {Γ₂ : finset (bounded_formula L m₂)} {i} :
  sigma.mk m₂ Γ₂ ∈ decomp i p Γ₁ → m₁ ≤ m₂ :=
begin
  { rcases p; simp[decomp, verum_eq, falsum_eq, and_eq, or_eq, fal_eq, ex_eq],
    { rintros rfl rfl, simp },
    { rintros rfl rfl, simp },
    { rintros rfl rfl, simp },
    { rintros (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩); simp },
    { rintros rfl rfl, simp },
    { rintros rfl rfl, simp[(∘)] },
    { rintros rfl rfl, simp } }
end

noncomputable def index_of_set (T : set (sentence L)) (i : ℕ) : option (sentence L) :=
(option.guard (λ i, i ∈ index '' T) i).bind (subformula.of_index L 0 0)

lemma index_of_neg_set_eq_some {T : set (sentence L)} {i : ℕ} {σ : sentence L} :
  index_of_set T i = some σ ↔ i = index σ ∧ σ ∈ T :=
⟨λ h, by { simp[index_of_set] at h, rcases h with ⟨rfl, τ, hτ, e⟩, simp at e, rcases e with rfl, refine ⟨by simp, hτ⟩ },
  by rintros ⟨rfl, hτ⟩; simp[index_of_set, hτ]⟩

@[simp] lemma index_of_neg_set_index {T : set (sentence L)} {σ : sentence L} (h : σ ∈ T) :
  index_of_set T σ.index = some σ :=
by simp[index_of_neg_set_eq_some, h]

@[simp] noncomputable def indices_of_neg_set (T : set (sentence L)) (m) : ℕ → list (bounded_formula L m)
| 0       := []
| (i + 1) := ((index_of_set T i).map coe).to_list ++ indices_of_neg_set i

@[reducible] def search_label (L : language) := ℕ × Σ m, finset (bounded_subformula L m 0)

inductive search_tree_decomp (T : set (sentence L)) (i : ℕ) :
  ∀ {m₁ m₂}, finset (bounded_subformula L m₁ 0) → finset (bounded_subformula L m₂ 0) → Prop
| decomp : ∀ {m₁ m₂} (Γ₁ : finset (bounded_formula L m₁)) (Γ₂ : finset (bounded_formula L m₂))
    (p : bounded_formula L m₁) (hp : p ∈ Γ₁) (hi : p.index = i.unpair.fst),
    sigma.mk m₂ Γ₂ ∈ decomp i.unpair.snd p Γ₁ → search_tree_decomp Γ₂ Γ₁
| none : ∀ {m} (Γ : finset (bounded_formula L m)) 
    (hi : ∀ p ∈ Γ, subformula.index p ≠ i.unpair.fst),
    search_tree_decomp Γ Γ

notation Γ₂ ` ≺[` :50 i : 50 `; ` T `] ` Γ₁ :50 := search_tree_decomp T i Γ₂ Γ₁

inductive search_tree (T : set (sentence L)) : search_label L → search_label L → Prop
| intro : ∀ (i : ℕ) {m₁ m₂} (Γ₁ : finset (bounded_formula L m₁)) (Γ₂ : finset (bounded_formula L m₂)),
    ¬is_terminal Γ₁ → 
    Γ₂ ≺[i; T] Γ₁ →
    search_tree (i + 1, ⟨m₂, Γ₂ ∪ ((index_of_set T i).map coe).to_finset⟩) (i, ⟨m₁, Γ₁⟩)

namespace search_tree
variables {T : set (sentence L)} {Δ : finset (sentence L)}

lemma le_of_decomp (i) {m₁ m₂} {Γ₁ : finset (bounded_subformula L m₁ 0)} {Γ₂ : finset (bounded_subformula L m₂ 0)}
  (h : Γ₂ ≺[i; T] Γ₁) : m₁ ≤ m₂ :=
begin
  cases h,
  case decomp : _ _ _ _ p hi hp hdecomp
  { cases p; simp[decomp, verum_eq, falsum_eq, and_eq, or_eq, fal_eq, ex_eq] at hdecomp; try { simp[hdecomp] },
    { contradiction }, { cases hdecomp; simp[hdecomp] } },
  case none : _ _ hi { refl }
end

lemma ss_of_decomp (i) {m₁ m₂} {Γ₁ : finset (bounded_subformula L m₁ 0)} {Γ₂ : finset (bounded_subformula L m₂ 0)}
  (h : Γ₂ ≺[i; T] Γ₁) {p} (hp : p ∈ Γ₁) : cast_le (le_of_decomp i h) p ∈ Γ₂ :=
begin
  cases h,
  case decomp : _ _ _ _ p hi hp hdecomp
  { cases p; simp[decomp, verum_eq, falsum_eq, and_eq, or_eq, fal_eq, ex_eq] at hdecomp,
    { contradiction },
    { rcases hdecomp with ⟨rfl, rfl⟩, simp* },
    { rcases hdecomp with ⟨rfl, rfl⟩, simp* },
    { rcases hdecomp with ⟨rfl, rfl⟩, simp* },
    { rcases hdecomp with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩); simp* },
    { rcases hdecomp with ⟨rfl, rfl⟩; simp* },
    { rcases hdecomp with ⟨rfl, rfl⟩; simp[*, cast_le_eq_mlift] },
    { rcases hdecomp with ⟨rfl, rfl⟩; simp* } },
  { simp* }
end

lemma decomp_iff_of_mem {m₁ m₂} {Γ₁ : finset (bounded_subformula L m₁ 0)} {Γ₂ : finset (bounded_subformula L m₂ 0)}
  {p : bounded_formula L m₁} (hp : p ∈ Γ₁) {j} :
  Γ₂ ≺[p.index.mkpair j; T] Γ₁ ↔ sigma.mk m₂ Γ₂ ∈ decomp j p Γ₁ :=
⟨by { rintros (⟨_, _, p', hp', hi, hdecomp⟩ | ⟨_, hi⟩),
      { simp at hdecomp hi, rcases hi with rfl, exact hdecomp },
      { have := hi p hp, simp at this, contradiction } },
 by { intros hdecomp, refine search_tree_decomp.decomp Γ₁ Γ₂ p hp (by simp) (by simpa using hdecomp) }⟩

lemma search_tree_iff {l₁ l₂ : search_label L} :
  search_tree T l₂ l₁ ↔
  ∃ (i : ℕ) {m₁ m₂} (Γ₁ : finset (bounded_formula L m₁)) (Γ₂ : finset (bounded_formula L m₂)),
  l₂ = (i + 1, ⟨m₂, Γ₂ ∪ ((index_of_set T i).map coe).to_finset⟩) ∧
  l₁ = (i, ⟨m₁, Γ₁⟩) ∧ 
  ¬is_terminal Γ₁ ∧ Γ₂ ≺[i; T] Γ₁ :=
⟨by { rintros ⟨i, Γ₁, Γ₂, hΓ₁, hdecomp⟩, refine ⟨i, _, _, Γ₁, Γ₂, rfl, rfl, hΓ₁, hdecomp⟩ },
 by { rintros ⟨i, _, _, Γ₁, Γ₂, rfl, rfl, hΓ₁, hdecomp⟩,
      exact search_tree.intro i Γ₁ Γ₂ hΓ₁ hdecomp }⟩

lemma search_tree_iff' {i : ℕ} {m₁ m₂} {Γ₁ : finset (bounded_formula L m₁)} {Γ₂ : finset (bounded_formula L m₂)} :
  search_tree T (i + 1, ⟨m₂, Γ₂⟩) (i, ⟨m₁, Γ₁⟩) ↔
  ∃ (Γ : finset (bounded_formula L m₂)),
  Γ₂ = Γ ∪ ((index_of_set T i).map coe).to_finset ∧
  ¬is_terminal Γ₁ ∧ Γ ≺[i; T] Γ₁ :=
⟨by { rintros ⟨i, Γ₁, Γ₂, hΓ₁, hdecomp⟩, refine ⟨Γ₂, by refl, hΓ₁, hdecomp⟩ },
 by { rintros ⟨Γ, rfl, hΓ₁, hdecomp⟩,
      exact search_tree.intro i Γ₁ Γ hΓ₁ hdecomp }⟩

variables (T Δ)

@[reducible] def search_label.top : search_label L := ⟨0, sigma.mk 0 Δ⟩

inductive accessible (Δ : finset (sentence L)) : search_label L → Prop
| top : accessible (search_label.top Δ)
| lt : ∀ {l₁ l₂}, search_tree T l₁ l₂ → accessible l₂ → accessible l₁

def accessible_label := { l // accessible T Δ l }

def accessible_search_tree : accessible_label T Δ → accessible_label T Δ → Prop :=
λ l₁ l₂, search_tree T l₁.val l₂.val 

local infix ` ≺ `:50 := accessible_search_tree T Δ

@[simp] lemma Axl_bot (l) (Γ : finset (bounded_formula L m)) (h : is_terminal Γ) {i} : ¬search_tree T l ⟨i, m, Γ⟩ :=
by rintros ⟨⟩; contradiction

section well_founded
variables {T Δ} (wf : well_founded (accessible_search_tree T Δ))

def accessible_search_tree.recursion {C : accessible_label T Δ → Sort*} 
  (l) (h : Π l₁, (Π l₂, l₂ ≺ l₁ → C l₂) → C l₁) : C l :=
well_founded.recursion wf l h

variables {m} {Γ : finset (bounded_formula L m)} (hΓ : ¬is_terminal Γ) (i : ℕ)

private lemma synthetic_main_lemma_aux_and {Γ : finset (bounded_formula L m)}
  (IH : ∀ {m'} (Γ' : finset (bounded_formula L m')),
    Γ' ≺[i; T] Γ → ∃ I : finset ℕ, ⊢ᵀ Γ' ∪ I.bind (λ i, (option.map coe (index_of_set T i)).to_finset))
  {p q : bounded_formula L m}
  (hp : p ⊓ q ∈ Γ)
  (hi : index (p ⊓ q) = (nat.unpair i).fst) : 
  ∃ (I : finset ℕ), ⊢ᵀ Γ ∪ I.bind (λ i, (option.map coe (index_of_set T i)).to_finset) :=
begin
  rcases IH (insert p Γ) (search_tree_decomp.decomp _ _ _ hp hi (by simp[and_eq, decomp])) with ⟨I₁, hI₁⟩,
      rcases IH (insert q Γ) (search_tree_decomp.decomp _ _ _ hp hi (by simp[and_eq, decomp])) with ⟨I₂, hI₂⟩,
      simp at hI₁ hI₂,
      have : ⊢ᵀ insert (p ⊓ q) (Γ ∪ (
        I₁.sup (λ i, ((index_of_set T i).map coe).to_finset) ∪
        I₂.sup (λ i, ((index_of_set T i).map coe).to_finset))),
      by simpa[←finset.union_union_distrib_left] using derivable.and' hI₁ hI₂,
      refine ⟨I₁ ∪ I₂, derivable.cast this (by simp[finset.bind, finset.sup_union, hp])⟩ 
end

private lemma synthetic_main_lemma_aux_or {Γ : finset (bounded_formula L m)}
  (IH : ∀ {m'} (Γ' : finset (bounded_formula L m')),
    Γ' ≺[i; T] Γ → ∃ I : finset ℕ, ⊢ᵀ Γ' ∪ I.bind (λ i, (option.map coe (index_of_set T i)).to_finset))
  {p q : bounded_formula L m}
  (hp : p ⊔ q ∈ Γ)
  (hi : index (p ⊔ q) = (nat.unpair i).fst) : 
  ∃ (I : finset ℕ), ⊢ᵀ Γ ∪ I.bind (λ i, (option.map coe (index_of_set T i)).to_finset) :=
begin
  rcases IH (insert q (insert p Γ)) (search_tree_decomp.decomp _ _ _ hp hi (by simp[and_eq, decomp])) with ⟨I, hI⟩,
  simp at hI,
  have : ⊢ᵀ (insert p $ insert (p ⊔ q) $ Γ ∪ I.bind (λ i, (option.map coe (index_of_set T i)).to_finset)),
  from derivable.cast (derivable.or_right p q hI) (finset.insert.comm _ _ _),
  refine ⟨I, derivable.cast (derivable.or_left p q this) (by simp[hp])⟩,
end

private lemma synthetic_main_lemma_aux_all {Γ : finset (bounded_formula L m)}
  (IH : ∀ {m'} (Γ' : finset (bounded_formula L m')),
    Γ' ≺[i; T] Γ → ∃ I : finset ℕ, ⊢ᵀ Γ' ∪ I.bind (λ i, (option.map coe (index_of_set T i)).to_finset))
  {p : bounded_subformula L m 1}
  (hp : ∀'p ∈ Γ)
  (hi : index (∀'p) = (nat.unpair i).fst) : 
  ∃ (I : finset ℕ), ⊢ᵀ Γ ∪ I.bind (λ i, (option.map coe (index_of_set T i)).to_finset) :=
begin
  rcases IH (insert (push p) (finset_mlift Γ)) (search_tree_decomp.decomp _ _ _ hp hi (by simp[decomp])) with ⟨I, hI⟩,
  simp at hI,
  have : ⊢ᵀ insert (∀'p) (Γ ∪ I.bind (λ (i : ℕ), (option.map coe (index_of_set T i)).to_finset)),
  from @derivable.all L _ (Γ ∪ I.bind (λ (i : ℕ), (option.map coe (index_of_set T i)).to_finset)) p
    (derivable.cast hI $ by simp[finset_mlift, finset.image_union, finset.image_bind, finset.image_to_finset_option, (∘)]),
  refine ⟨I, derivable.cast this $ by simp[hp]⟩
end

lemma exists_of_instances {p : bounded_subformula L m 1} {i Γ} : ⊢ᵀ instance_enum p i ∪ Γ → ⊢ᵀ insert (∃'p) Γ :=
begin
  induction i with i IH generalizing Γ; simp,
  { assume h, exact derivable.weakening h (finset.subset_insert _ _) },
  { cases subterm.of_index L m 0 i with t; simp; assume h,
    { exact IH h },
    { have : ⊢ᵀ insert (subst t p) (insert (∃'p) Γ), from derivable.cast (IH h) (by ext; simp; tauto),
      exact derivable.cast (derivable.ex this) (by ext; simp) } }
end

private lemma synthetic_main_lemma_aux_ex {Γ : finset (bounded_formula L m)}
  (IH : ∀ {m'} (Γ' : finset (bounded_formula L m')),
    Γ' ≺[i; T] Γ → ∃ I : finset ℕ, ⊢ᵀ Γ' ∪ I.bind (λ i, (option.map coe (index_of_set T i)).to_finset))
  {p : bounded_subformula L m 1}
  (hp : ∃'p ∈ Γ)
  (hi : index (∃'p) = (nat.unpair i).fst) : 
  ∃ (I : finset ℕ), ⊢ᵀ Γ ∪ I.bind (λ i, (option.map coe (index_of_set T i)).to_finset) :=
begin
  rcases IH (instance_enum p i.unpair.snd ∪ Γ) (search_tree_decomp.decomp _ _ _ hp hi (by {simp[decomp], })) with ⟨I, hI⟩,
  simp at hI,
  refine ⟨I, derivable.cast (exists_of_instances hI) $ by simp[hp]⟩
end

include wf

lemma synthetic_main_lemma_aux (l : accessible_label T Δ) : ∃ I : finset ℕ,
  ⊢ᵀ l.val.2.2 ∪ (I.bind (λ i, ((index_of_set T i).map coe).to_finset)) :=
begin
  apply accessible_search_tree.recursion wf l,
  rintros ⟨⟨i, m, Γ⟩, accΓ⟩ IH, simp,
  show ∃ I : finset ℕ, ⊢ᵀ Γ ∪ I.bind (λ i, (option.map coe (index_of_set T i)).to_finset),
  by_cases hΓ : is_terminal Γ,
  { rcases hΓ with ⟨k, r, v, hΓ, hΓ_neg⟩,
    refine ⟨∅, by simp[finset.bind]; exact derivable.AxL r v hΓ hΓ_neg⟩ },
  have IH : ∀ {m'} (Γ' : finset (bounded_subformula L m' 0)),
    Γ' ≺[i; T] Γ → ∃ I : finset ℕ, ⊢ᵀ Γ' ∪ I.bind (λ i, (option.map coe (index_of_set T i)).to_finset),
  { intros m' Γ' h,
    have hs := search_tree.intro i Γ Γ' hΓ h,
    have : accessible T Δ (i + 1, ⟨m', Γ' ∪ (option.map coe (index_of_set T i)).to_finset⟩),
      from accessible.lt hs accΓ,
    rcases IH ⟨_, this⟩ (by simpa[accessible_search_tree] using hs) with ⟨I, hI⟩,
    refine ⟨insert i I, by simpa[finset.bind] using hI⟩ },
    by_cases hp : ∀ p ∈ Γ, subformula.index p ≠ i.unpair.fst,
    { exact IH Γ (search_tree_decomp.none Γ hp) },
    simp at hp, rcases hp with ⟨p, hp, hi⟩,
    cases p,
    case verum { refine ⟨∅, by simpa[finset.bind] using derivable.verum hp⟩ },
    case falsum { refine IH Γ (search_tree_decomp.decomp _ _ _ hp hi (by simp[falsum_eq, decomp])) },
    case relation : k r v { refine IH Γ (search_tree_decomp.decomp _ _ _ hp hi (by simp[decomp])) },
    case neg_relation : k r v { refine IH Γ (search_tree_decomp.decomp _ _ _ hp hi (by simp[decomp])) },
    case and : { exact synthetic_main_lemma_aux_and i @IH hp hi },
    case or : { exact synthetic_main_lemma_aux_or i @IH hp hi },
    case fal : { exact synthetic_main_lemma_aux_all i @IH hp hi },
    case ex : { exact synthetic_main_lemma_aux_ex i @IH hp hi }
end

lemma synthetic_main_lemma (Γ : finset (bounded_subformula L m 0)) {i}
  (h : accessible T Δ ⟨i, m, Γ⟩) : 
  ∃ (I : finset ℕ), ⊢ᵀ Γ ∪ I.bind (λ i, ((index_of_set T i).map coe).to_finset) :=
by simpa using synthetic_main_lemma_aux wf ⟨_, h⟩

variables (T Δ wf)

lemma synthetic_main_lemma' : ∃ Γ : finset (sentence L), ↑Γ ⊆ T ∧ ⊢ᵀ Δ ∪ Γ :=
begin
  have : ∃ I : finset ℕ, ⊢ᵀ Δ ∪ I.bind (λ i, ((index_of_set T i).map coe).to_finset),
  from synthetic_main_lemma wf Δ accessible.top,
  rcases this with ⟨I, h⟩,
  refine ⟨I.bind (λ i, ((index_of_set T i).map coe).to_finset), by intros x; simp[index_of_neg_set_eq_some, finset.mem_bind], h⟩
end

end well_founded

section non_well_founded
variables {T Δ} (wf : ¬well_founded (accessible_search_tree T Δ))

include wf

lemma top_inaccessible : ¬acc (accessible_search_tree T Δ) ⟨search_label.top Δ, accessible.top⟩ :=
begin
  assume A,
  suffices : well_founded (accessible_search_tree T Δ), by contradiction,
  refine ⟨_⟩,
  rintros ⟨l, hl⟩, induction hl,
  case top { exact A },
  case lt : l₁ l₂ h hl₂ IH { refine IH.inv h }
end

noncomputable def chain : ℕ → search_label L :=
  λ i, (descending_chain (accessible_search_tree T Δ) ⟨search_label.top Δ, accessible.top⟩ i).val

@[reducible] noncomputable def rank (i : ℕ) : ℕ := (chain wf i).2.1

def var_domain : set ℕ := set.range (λ i, (chain wf i).2.1)

def domain := {n : ℕ // ∃ i, n < rank wf i}

noncomputable def uniform (i : ℕ) : fin (rank wf i) → domain wf := by { rintros ⟨n, hn⟩, refine ⟨n, i, hn⟩ }

lemma subterm_uniform_inj {i} {t u : bounded_subterm L (rank wf i) n} :
  subterm.map (uniform wf i) t = subterm.map (uniform wf i) u → t = u := λ h,
subterm.map_inj_of_inj (uniform wf i) (by rintros ⟨x, hx⟩ ⟨y, hy⟩; simp[uniform]) h

@[simp] lemma uniform_comp_cast_le {i j} (h) : uniform wf j ∘ fin.cast_le h = uniform wf i :=
by { ext x; cases x; simp[uniform], rw[fin.cast_le_mk], simp }

@[simp] lemma uniform_cast_le_term {i j} (h : rank wf i ≤ rank wf j) (t : bounded_subterm L (rank wf i) n) :
  (subterm.cast_le h t).map (uniform wf j) = t.map (uniform wf i) :=
by simp[subterm.cast_le]

@[simp] lemma uniform_cast_le {i j} (h : rank wf i ≤ rank wf j) (p : bounded_subformula L (rank wf i) n) :
  map (uniform wf j) (cast_le h p) = map (uniform wf i) p :=
by simp[cast_le]

@[reducible] noncomputable def Gamma (i : ℕ) : finset (bounded_formula L (rank wf i)) := (chain wf i).2.2

local notation `Γ`:80 := Gamma wf

@[reducible] noncomputable def uniform_Gamma (i : ℕ) : finset (formula L (domain wf)) := (Γ i).image (map $ uniform wf i)

def chain_union : set (formula L (domain wf)) := {p | ∃ i (p' ∈ Γ i), p = subformula.map (uniform wf i) p'}

local notation `⛓️`:= chain_union wf 

lemma mem_chain_union_iff {p : formula L (domain wf)} : p ∈ ⛓️ ↔ ∃ i, p ∈ (Γ i).image (map $ uniform wf i) :=
by simp[chain_union, eq_comm]

@[simp] lemma chain_zero : chain wf 0 = ⟨0, 0, Δ⟩ := by refl

@[simp] lemma chain_zero' : Γ 0 = Δ := by refl

@[simp] lemma chain_lt (i) : search_tree T (chain wf (i + 1)) (chain wf i) :=
infinite_descending_chain_of_non_acc (accessible_search_tree T Δ) ⟨search_label.top Δ, accessible.top⟩ (top_inaccessible wf) i

@[simp] lemma chain_fst (i) : (chain wf i).1 = i :=
begin
  induction i with i IH,
  { simp },
  { rcases search_tree_iff.mp (chain_lt wf i) with ⟨i', m₁, m₂, Γ₁, Γ₂, his, hi, hterminal, hdecomp⟩,
    have : i = i', by simpa[IH] using congr_arg prod.fst hi,
    rcases this with rfl,
    simpa using congr_arg prod.fst his }
end

lemma chain_eq (i) : chain wf i = (i, ⟨_, Γ i⟩) :=
by ext; simp

lemma Γ_is_not_terminal (i) : ¬is_terminal (Γ i) :=
by { rcases search_tree_iff.mp (chain_lt wf i) with ⟨i', m₁, m₂, Γ₁, Γ₂, his, hi, hterminal, hdecomp⟩,
     simp only [chain_eq, prod.mk.inj_iff] at hi, rcases hi with ⟨rfl, rfl, rfl⟩,
     assumption }

@[simp] lemma Γ_lt (i) : ∃ Γ', Γ (i + 1) = Γ' ∪ ((index_of_set T i).map coe).to_finset ∧ Γ' ≺[i; T] Γ i :=
begin  
  have : search_tree T (i + 1, ⟨_, Γ (i + 1)⟩) (i, ⟨_, Γ i⟩),
  { have := chain_lt wf i, rw[chain_eq, chain_eq] at this, exact this },
  rcases search_tree_iff'.mp this with ⟨Γ', hΓ', hterminal, hdecomp⟩,
  refine ⟨Γ', hΓ', hdecomp⟩
end

@[simp] lemma Γ_lt' (i) : ∃ {m'} (Γ' : finset (bounded_formula L m')) (hm' : m' = rank wf (i + 1)),
   Γ (i + 1) = Γ'.image (cast_le (eq.symm hm').ge) ∪ ((index_of_set T i).map coe).to_finset ∧ Γ' ≺[i; T] Γ i :=
begin
  rcases Γ_lt wf i with ⟨Γ', h⟩,
  refine ⟨rank wf (i + 1), Γ', rfl, by simpa using h⟩,
end

@[simp] lemma rank_mono {i j} (h : i ≤ j) : rank wf i ≤ rank wf j :=
begin
  induction j with j IH,
  { have : i = 0, from le_zero_iff.mp h,
    simp[this] },
  { have : i ≤ j ∨ i = j.succ, from nat.of_le_succ h,
    rcases this with (le | eq),
    { rcases Γ_lt wf j with ⟨Γ', _, hdecomp⟩,
      exact le_trans (IH le) (le_of_decomp j hdecomp) },
    { simp[eq] } }
end

lemma cast_mem {i j} (hj : i ≤ j) {p} (h : p ∈ Γ i) : cast_le (rank_mono wf hj) p ∈ Γ j :=
begin
  induction j with j IH,
  { have : i = 0, from le_zero_iff.mp hj, rcases this with rfl,
    simpa using h },
  { have : i ≤ j ∨ i = j.succ, from nat.of_le_succ hj,
    rcases this with (le | eq),
    { rcases Γ_lt wf j with ⟨Γ', his, hdecomp⟩,
      have : cast_le _ p ∈ Γ', by simpa using ss_of_decomp j hdecomp (IH le),
      simp[his, this] },
    { rcases eq with rfl, simp[h] } }
end

lemma cast_mem' {i} {p} (h : p ∈ Γ i) :
  cast_le (rank_mono wf $ nat.right_le_mkpair _ _) p ∈ Γ (p.index.mkpair i) :=
cast_mem wf _ h

lemma cast_mem'' {i j} {p} (h : p ∈ Γ i) (hj : i ≤ j) :
  cast_le (rank_mono wf $ le_trans hj (nat.right_le_mkpair _ _)) p ∈ Γ (p.index.mkpair j) :=
cast_mem wf _ h

lemma T_mem {σ : sentence L} (h : σ ∈ T) : ↑σ ∈ ⛓️ :=
⟨σ.index + 1,
  begin
    refine ⟨↑σ, _⟩,
    rcases Γ_lt wf σ.index with ⟨Γ', hΓ', hdecomp⟩,
    have : Gamma wf (index σ + 1) = Γ' ∪ {↑σ}, by simpa[h] using hΓ',
    refine ⟨by simp[this], by simp[uniform]⟩
  end⟩

lemma domian_inv (t : subterm L (domain wf) 0) : ∃ {i} (t' : bounded_term L (rank wf i)), t'.map (uniform wf i) = t :=
by { induction t,
  case metavar : x { rcases x with ⟨x, i, hx⟩, refine ⟨i, &⟨x, hx⟩, by simp[uniform]⟩ },
  case var : x { refine fin.nil x },
  case function : k f v IH { rcases classical.skolem.mp IH with ⟨I, hI⟩,
    let isup := ⨆ᶠ i, I i,
    have : ∀ x, ∃ (t' : bounded_term L (rank wf isup)), subterm.map (uniform wf isup) t' = v x,
    { intros x, rcases hI x with ⟨t, ht⟩,
      refine ⟨subterm.cast_le (rank_mono wf (by simp)) t, by simp[ht]⟩ },
    rcases classical.skolem.mp this with ⟨v', hv'⟩,
    refine ⟨isup, subterm.function f v', by simp[hv']⟩ } } 

lemma relation_decomp {k} {r : L.pr k} {v} : relation r v ∈ ⛓️ → neg_relation r v ∉ ⛓️ :=
begin
  rintros ⟨i, p, hp, eq_rel⟩ ⟨i', p', hp', eq_nrel⟩,
  have : ∃ v', p = relation r v' ∧ v = (λ j, subterm.map (uniform wf i) (v' j)),
  { cases p; simp[map, rew] at eq_rel; try { contradiction },
    case relation : k r v' { rcases eq_rel with ⟨rfl, rfl, rfl⟩, refine ⟨v', rfl, by refl⟩, } },
  rcases this with ⟨v, rfl, rfl⟩,
  have : ∃ v', p' = neg_relation r v' ∧ ∀ j, subterm.map (uniform wf i) (v j) = subterm.map (uniform wf i') (v' j),
  { cases p'; simp[map, rew] at eq_nrel; try { contradiction },
    case neg_relation : k r v { rcases eq_nrel with ⟨rfl, rfl, e⟩,
      refine ⟨v, rfl, by { simp at e, simpa using congr_fun (e) }⟩ } },
  rcases this with ⟨v', rfl, hv⟩,
  let I := max i i',
  let V : fin k → bounded_term L (rank wf I) := λ (j : fin k), subterm.cast_le (rank_mono wf (by simp)) (v j),
  let V' : fin k → bounded_term L (rank wf I) := λ (j : fin k), subterm.cast_le (rank_mono wf (by simp)) (v' j),
  have V_eq : V = V', { ext j, simp[V, V'], refine subterm_uniform_inj wf (by simpa using hv j) },
  have hr : relation r V ∈ Γ I, by simpa using cast_mem wf (show i ≤ max i i', by simp) hp, 
  have hnr : neg_relation r V ∈ Γ I, by simpa[V_eq] using cast_mem wf (show i' ≤ max i i', by simp) hp',
  have : is_terminal (Γ I), from ⟨k, r, V, hr, hnr⟩,
  have : ¬is_terminal (Γ I), from Γ_is_not_terminal wf I,
  contradiction
end

lemma verum_decomp : ⊤ ∉ ⛓️ :=
begin
  rintros ⟨i, p, hp, eq_top⟩,
  have : p = ⊤, { cases p; simp[map, rew, ←verum_eq] at eq_top; try {contradiction}, { refl } },
  rcases this with rfl,
  let k := (index (⊤ : bounded_subformula L (rank wf i) 0)).mkpair i,
  have mem_Γ : ⊤ ∈ Γ k, from cast_mem' wf hp,
  rcases Γ_lt wf k with ⟨Γ', hΓ', hdecomp⟩,
  have := (decomp_iff_of_mem mem_Γ).mp hdecomp,
  simp[decomp] at this, contradiction
end

lemma and_decomp {p q : formula L (domain wf)} : p ⊓ q ∈ ⛓️ → p ∈ ⛓️ ∨ q ∈ ⛓️ :=
begin
  rintros ⟨i, r, hr, eq_and⟩,
  have : ∃ p' q', r = p' ⊓ q' ∧ p = map (uniform wf i) p' ∧ q = map (uniform wf i) q',
  { cases r; simp[map, rew, ←and_eq] at eq_and; try { contradiction },
    case and : p' q' { refine ⟨p', q', rfl, eq_and⟩ } },
  rcases this with ⟨p, q, rfl, rfl, rfl⟩, 
  let k := (index (p ⊓ q)).mkpair i,
  have mem_Γ : cast_le _ (p ⊓ q) ∈ Γ k, from cast_mem' wf hr,  
  rcases Γ_lt' wf k with ⟨m', Γ', hm', hΓ', hdecomp⟩,
  have : sigma.mk m' Γ' ∈ decomp i (cast_le _ (p ⊓ q)) (Gamma wf k), 
    from (decomp_iff_of_mem mem_Γ).mp (by simp only [cast_le_index]; exact hdecomp),
  simp[decomp] at this, rcases this with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩),
  { refine or.inl ((mem_chain_union_iff wf).mpr (⟨k + 1, by simp[hΓ']⟩)) },
  { refine or.inr ((mem_chain_union_iff wf).mpr (⟨k + 1, by simp[hΓ']⟩)) }
end

lemma or_decomp {p q : formula L (domain wf)} : p ⊔ q ∈ ⛓️ → p ∈ ⛓️ ∧ q ∈ ⛓️ :=
begin
  rintros ⟨i, r, hr, eq_or⟩,
  have : ∃ p' q', r = p' ⊔ q' ∧ p = map (uniform wf i) p' ∧ q = map (uniform wf i) q',
  { cases r; simp[map, rew, ←or_eq] at eq_or; try { contradiction },
    case or : p' q' { refine ⟨p', q', rfl, eq_or⟩ } },
  rcases this with ⟨p, q, rfl, rfl, rfl⟩, 
  let k := (index (p ⊔ q)).mkpair i,
  have mem_Γ : cast_le _ (p ⊔ q) ∈ Γ k, from cast_mem' wf hr,  
  rcases Γ_lt' wf k with ⟨m', Γ', hm', hΓ', hdecomp⟩,
  have : sigma.mk m' Γ' ∈ decomp i (cast_le _ (p ⊔ q)) (Gamma wf k), 
    from (decomp_iff_of_mem mem_Γ).mp (by simp only [cast_le_index]; exact hdecomp),
  simp[decomp] at this, rcases this with ⟨rfl, rfl⟩,
  refine ⟨(mem_chain_union_iff wf).mpr ⟨k + 1, by simp[hΓ']⟩, (mem_chain_union_iff wf).mpr ⟨k + 1, by simp[hΓ']⟩⟩
end

lemma all_decomp {p : subformula L (domain wf) 1} : ∀'p ∈ ⛓️ → ∃ t, subst t p ∈ ⛓️ :=
begin
  rintros ⟨i, r, hr, eq_fal⟩,
  have : ∃ p', r = ∀' p' ∧ p = map (uniform wf i) p',
  { cases r; simp[map, rew, ←fal_eq, ←eq_fal] at eq_fal; try { contradiction },
    case fal : p' { refine ⟨p', rfl, eq_fal⟩ } },
  rcases this with ⟨p, rfl, rfl⟩,
  let k := (index (∀'p)).mkpair i,
  have mem_Γ : cast_le _ (∀'p) ∈ Γ k, from cast_mem' wf hr,  
  rcases Γ_lt' wf k with ⟨m', Γ', hm', hΓ', hdecomp⟩,
  have : sigma.mk m' Γ' ∈ decomp i (cast_le _ (∀'p)) (Gamma wf k), 
    from (decomp_iff_of_mem mem_Γ).mp (by simp only [cast_le_index]; exact hdecomp),
  simp[decomp] at this, rcases this with ⟨rfl, rfl⟩,
  let t : bounded_term L (rank wf (k + 1)) :=
    subterm.cast_le (by simp[hm']) (&(fin.last _) : bounded_term L (rank wf k + 1)),
  refine ⟨t.map (uniform wf _), (mem_chain_union_iff wf).mpr ⟨k + 1, by simp[hΓ', map_subst, t]⟩⟩
end

lemma ex_decomp {p : subformula L (domain wf) 1} : ∃'p ∈ ⛓️ → ∀ t, subst t p ∈ ⛓️ :=
begin
  rintros ⟨i, r, hr, eq_ex⟩ t,
  have : ∃ p', r = ∃' p' ∧ p = map (uniform wf i) p',
  { cases r; simp[map, rew, ←ex_eq, ←eq_ex] at eq_ex; try { contradiction },
    case ex : p' { refine ⟨p', rfl, eq_ex⟩ } },
  rcases this with ⟨p, rfl, rfl⟩,
  rcases domian_inv wf t with ⟨it, t, rfl⟩,
  let j := (max (max i it) (t.index + 1)),
  let k := (∃'p).index.mkpair j,
  have i_le_k : i ≤ k, { simp[k], refine le_trans (by simp) (nat.right_le_mkpair _ _) },
  have it_le_k : it ≤ k, { simp[k], refine le_trans (by simp) (nat.right_le_mkpair _ _) },
  have mem_Γ : cast_le _ ∃'p ∈ Γ k := cast_mem'' wf hr (by simp),  
  rcases Γ_lt' wf k with ⟨m', Γ', hm', hΓ', hdecomp⟩,
  have : sigma.mk m' Γ' ∈ decomp j (cast_le _ (∃'p)) (Γ k), 
    from (decomp_iff_of_mem mem_Γ).mp (by simp only [cast_le_index]; exact hdecomp),
  simp[decomp] at this, rcases this with ⟨rfl, rfl⟩,
  have : subst (subterm.cast_le _ t) (cast_le _ p) ∈ instance_enum (cast_le _ p) j, 
    from mem_instance_enum_of_lt (subterm.cast_le (rank_mono wf it_le_k) t) (cast_le (rank_mono wf i_le_k) p) j (by simp),
  have : subst (subterm.map (uniform wf it) t) (map (uniform wf i) p) ∈ finset.image (map (uniform wf k)) (instance_enum (cast_le _ p) j),
  by simpa[map_subst, -finset.mem_image] using finset.mem_image_of_mem (map $ uniform wf k) this,
  refine (mem_chain_union_iff wf).mpr ⟨k + 1,
    by simp [hΓ', -finset.mem_image, finset.image_union, finset.mem_union, finset.image_image, (∘), this]⟩
end

def model_pr {k} (r : L.pr k) (v : fin k → term L (domain wf)) : Prop :=
subformula.neg_relation r v ∈ ⛓️

@[reducible] def model : Structure L :=
{ dom := term L (domain wf),
  fn := λ k f, subterm.function f,
  pr := λ k r, model_pr wf r }

@[simp] lemma model_val (t) : subterm.val (model wf) subterm.metavar fin.nil t = t :=
by { induction t; simp*, case var : x { exact fin.nil x } }

lemma semantic_main_lemma : ∀ p ∈ ⛓️, model wf ⊧ᵀ[subterm.metavar] ∼p
| ⊤                  h  := by { have : ⊤ ∉ ⛓️, from verum_decomp wf, contradiction }
| ⊥                  h  := by simp
| (relation r v)     h  := by simpa[model_pr, (∘)] using relation_decomp wf h
| (neg_relation r v) h := by simp[model_pr, (∘), h]
| (p ⊓ q)            h :=
    begin
      have : p ∈ ⛓️ ∨ q ∈ ⛓️, from and_decomp wf h,
      rcases this with (h | h),
      { simp, refine or.inl (by simpa using semantic_main_lemma p h) },
      { simp, refine or.inr (by simpa using semantic_main_lemma q h) }
    end
| (p ⊔ q)            h :=
    begin
      have : p ∈ ⛓️ ∧ q ∈ ⛓️, from or_decomp wf h,
      rcases this with ⟨h₁, h₂⟩,
      simp,
      refine ⟨by simpa using semantic_main_lemma p h₁, by simpa using semantic_main_lemma q h₂⟩
    end
| (∀'p)              h :=
    begin
      simp, rcases all_decomp wf h with ⟨t, h⟩,
      refine ⟨t, by simpa[val, subval_subst, fin.concat_zero] using semantic_main_lemma (subst t p) h⟩
    end
| (∃'p)              h :=
    begin
      simp, intros t,
      by simpa[val, subval_subst, fin.concat_zero] using semantic_main_lemma (subst t p) (ex_decomp wf h t)
    end
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.1.complexity)⟩]}

variables (T Δ wf)

lemma semantic_main_lemma' : ∀ σ ∈ T, ¬model wf ⊧ σ :=
by intros σ hσ; simpa using semantic_main_lemma wf ↑σ (T_mem wf hσ)

lemma semantic_main_lemma'_root : ∀ σ ∈ Δ, ¬model wf ⊧ σ := λ σ hσ,
by simpa using semantic_main_lemma wf σ ⟨0,↑σ, by simp[hσ]⟩

end non_well_founded

end search_tree

variables (T : set (sentence L)) (Δ : finset (sentence L))

theorem completeness (h : ∀ S : Structure L, S ⊧ T → ∃ σ ∈ Δ, S ⊧ σ) :
  ∃ Γ : finset (sentence L), ↑Γ ⊆ not '' T ∧ ⊢ᵀ Δ ∪ Γ :=
begin
  by_contradiction A, simp at A,
  by_cases wf : well_founded (search_tree.accessible_search_tree (not '' T) Δ),
  { have : ∃ (Γ : finset (sentence L)), ↑Γ ⊆ not '' T ∧ ⊢ᵀ Δ ∪ Γ,
      from search_tree.synthetic_main_lemma' (not '' T) Δ wf,
    rcases this with ⟨Γ, hΓ, b⟩,
    have := A Γ hΓ, contradiction },
  { have : search_tree.model wf ⊧ T,
    { intros σ hσ,
      simpa[sentence_models_def] using search_tree.semantic_main_lemma' (not '' T) Δ wf (∼σ)
        (set.mem_image_of_mem subformula.not hσ) },
    have : ∃ σ ∈ Δ, search_tree.model wf ⊧ σ, from h (search_tree.model wf) this,
    have : ¬∃ σ ∈ Δ, search_tree.model wf ⊧ σ, by simpa using search_tree.semantic_main_lemma'_root (not '' T) Δ wf,
    contradiction }
end

end Tait

end fol