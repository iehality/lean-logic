import QL.FOL.deduction QL.FOL.language

universes u v

namespace fol
open_locale logic_symbol aclogic
open subformula
variables (L L₁ L₂ : language.{u}) (m n : ℕ)

namespace Tait

inductive subformula (m) : ℕ → Type u
| verum          {n} : subformula n
| falsum        {n} : subformula n
| relation     {n} : ∀ {p}, L.pr p → (fin p → subterm L m n) → subformula n
| neg_relation {n} : ∀ {p}, L.pr p → (fin p → subterm L m n) → subformula n
| and          {n} : subformula n → subformula n → subformula n
| or           {n} : subformula n → subformula n → subformula n
| fal          {n} : subformula (n + 1) → subformula n
| ex           {n} : subformula (n + 1) → subformula n

@[reducible] def formula (m) := subformula L m 0

@[reducible] def sentence := formula L 0

variables {L m n}

namespace subformula

instance : has_univ_quantifier' (subformula L m) := ⟨@fal L m⟩

instance : has_exists_quantifier' (subformula L m) := ⟨@ex L m⟩

attribute [pattern]  has_sup.sup has_inf.inf has_univ_quantifier.univ has_exists_quantifier.ex

@[simp] def not : ∀ {n}, subformula L m n → subformula L m n
| n verum              := falsum
| n falsum             := verum
| n (relation r v)     := neg_relation r v
| n (neg_relation r v) := relation r v
| n (and p q)          := or (not p) (not q)
| n (or p q)           := and (not p) (not q)
| n (fal p)            := ex (not p)
| n (ex p)             := fal (not p)

def imply (p q : subformula L m n) := or (not p) q

instance : has_logic_symbol (subformula L m n) :=
{ bot := falsum,
  top := verum,
  sup := or,
  inf := and,
  arrow := imply,
  neg := not }

lemma verum_eq : @verum L m n = ⊤ := rfl
lemma falsum_eq : @falsum L m n = ⊥ := rfl
lemma and_eq : @and L m n = has_inf.inf := rfl
lemma or_eq : @or L m n = has_sup.sup := rfl
lemma not_eq : @not L m n = has_negation.neg := rfl
lemma imply_eq : @imply L m n = has_arrow.arrow := rfl
lemma imply_def (p q : subformula L m n) : (p ⟶ q) = (∼p) ⊔ q := by simp[←imply_eq, imply]; refl
lemma fal_eq : @fal L m n = has_univ_quantifier'.univ := rfl
lemma ex_eq : @ex L m n = has_exists_quantifier'.ex := rfl

@[simp] lemma not_falsum : ∼(⊥ : subformula L m n) = ⊤ := rfl

@[simp] lemma not_verum : ∼(⊤ : subformula L m n) = ⊥ := rfl

@[simp] lemma not_relation {k} (r : L.pr k) (v : fin k → subterm L m n) : ∼(relation r v) = neg_relation r v := rfl

@[simp] lemma not_neg_relation {k} (r : L.pr k) (v : fin k → subterm L m n) : ∼(neg_relation r v) = relation r v := rfl

@[simp] lemma not_and (p q : subformula L m n) : ∼(p ⊓ q) = ∼p ⊔ ∼q := rfl

@[simp] lemma not_or (p q : subformula L m n) : ∼(p ⊔ q) = ∼p ⊓ ∼q := rfl

@[simp] lemma not_fal (p : subformula L m (n + 1)) : ∼(∀'p) = ∃'∼p := rfl

@[simp] lemma not_ex (p : subformula L m (n + 1)) : ∼(∃'p) = ∀'∼p := rfl

@[simp] def complexity : Π {n}, subformula L m n → ℕ
| n verum              := 0
| n falsum             := 0
| n (relation r v)     := 0
| n (neg_relation r v) := 0
| n (and p q)          := max p.complexity q.complexity + 1
| n (or p q)           := max p.complexity q.complexity + 1
| n (fal p)            := p.complexity + 1
| n (ex p)             := p.complexity + 1

section rew
variables {m₁ m₂ : ℕ} (s : fin m₁ → subterm L m₂ n)

@[simp] def rew' {m₁ m₂} : Π {n}, (fin m₁ → subterm L m₂ n) → subformula L m₁ n → subformula L m₂ n
| n s verum              := ⊤
| n s falsum             := ⊥
| n s (relation p v)     := relation p (subterm.rew s ∘ v)
| n s (neg_relation p v) := neg_relation p (subterm.rew s ∘ v)
| n s (and p q)          := p.rew' s ⊓ q.rew' s
| n s (or p q)           := p.rew' s ⊔ q.rew' s
| n s (fal p)            := ∀'p.rew' (subterm.lift ∘ s)
| n s (ex p)             := ∃'p.rew' (subterm.lift ∘ s)

@[simp] lemma rew'_neg (p : subformula L m₁ n) : (∼p).rew' s = ∼(p.rew' s) :=
by induction p; simp[mlift, ←verum_eq, ←falsum_eq, ←and_eq, ←or_eq, ←not_eq, ←fal_eq, ←ex_eq, *] at*

def rew (s : fin m₁ → subterm L m₂ n) : subformula L m₁ n →ₗ subformula L m₂ n :=
{ to_fun := rew' s,
  map_neg' := λ p, by simp,
  map_imply' := λ p q, by simp[imply_def, ←or_eq],
  map_and' := λ p q, by refl,
  map_or' := λ p q, by refl,
  map_top' := by refl,
  map_bot' := by refl }

@[simp] lemma rew_relation {k} (r : L.pr k) (v : fin k → subterm L m₁ n) :
  rew s (relation r v) = relation r (subterm.rew s ∘ v) := rfl

@[simp] lemma rew_neg_relation {k} (r : L.pr k) (v : fin k → subterm L m₁ n) :
  rew s (neg_relation r v) = neg_relation r (subterm.rew s ∘ v) := rfl

@[simp] lemma rew_fal (p : subformula L m₁ (n + 1)) :
  rew s (∀'p) = ∀'rew (subterm.lift ∘ s) p := rfl

@[simp] lemma rew_ex (p : subformula L m₁ (n + 1)) :
  rew s (∃'p) = ∃'rew (subterm.lift ∘ s) p := rfl

end rew

section mlift

@[simp] def mlift' {m} : Π {n}, subformula L m n → subformula L (m + 1) n
| n verum              := ⊤
| n falsum             := ⊥
| n (relation p v)     := relation p (subterm.mlift ∘ v)
| n (neg_relation p v) := neg_relation p (subterm.mlift ∘ v)
| n (and p q)          := p.mlift' ⊓ q.mlift'
| n (or p q)           := p.mlift' ⊔ q.mlift'
| n (fal p)            := ∀'p.mlift'
| n (ex p)             := ∃'p.mlift'

@[simp] lemma mlift'_neg (p : subformula L m n) : (∼p).mlift' = ∼p.mlift' :=
by induction p; simp[mlift, ←verum_eq, ←falsum_eq, ←and_eq, ←or_eq, ←not_eq, ←fal_eq, ←ex_eq, *] at*

def mlift : subformula L m n →ₗ subformula L (m + 1) n :=
{ to_fun := mlift',
  map_neg' := λ p, by simp,
  map_imply' := λ p q, by simp[imply_def, ←or_eq],
  map_and' := λ p q, by refl,
  map_or' := λ p q, by refl,
  map_top' := by refl,
  map_bot' := by refl }

@[simp] lemma mlift_relation {k} (r : L.pr k) (v : fin k → subterm L m n) :
  mlift (relation r v) = relation r (subterm.mlift ∘ v) := rfl

@[simp] lemma mlift_neg_relation {k} (r : L.pr k) (v : fin k → subterm L m n) :
  mlift (neg_relation r v) = neg_relation r (subterm.mlift ∘ v) := rfl

@[simp] lemma mlift_fal (p : subformula L m (n + 1)) :
  mlift (∀'p) = ∀'mlift p := rfl

@[simp] lemma mslift_ex (p : subformula L m (n + 1)) :
  mlift (∃'p) = ∃'mlift p := rfl

end mlift

section push

@[simp] def push' {m} : Π {n}, subformula L m (n + 1) → subformula L (m + 1) n
| n verum              := ⊤
| n falsum             := ⊥
| n (relation p v)     := relation p (subterm.push ∘ v)
| n (neg_relation p v) := neg_relation p (subterm.push ∘ v)
| n (and p q)          := p.push' ⊓ q.push'
| n (or p q)           := p.push' ⊔ q.push'
| n (fal p)            := ∀'p.push'
| n (ex p)             := ∃'p.push'
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.complexity)⟩]}

@[simp] lemma push'_neg : ∀ {n} (p : subformula L m (n + 1)), (∼p).push' = ∼p.push'
| n verum              := by simp[←falsum_eq, ←verum_eq, ←not_eq]
| n falsum             := by simp[←falsum_eq, ←verum_eq, ←not_eq]
| n (relation p v)     := by simp
| n (neg_relation p v) := by simp
| n (and p q)          := by simp[←not_eq, ←and_eq, ←or_eq]; exact ⟨push'_neg p, push'_neg q⟩
| n (or p q)           := by simp[←not_eq, ←and_eq, ←or_eq]; exact ⟨push'_neg p, push'_neg q⟩
| n (fal p)            := by simp[←not_eq, ←fal_eq, ←ex_eq]; exact push'_neg p
| n (ex p)             := by simp[←not_eq, ←fal_eq, ←ex_eq]; exact push'_neg p
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.complexity)⟩]}

def push : subformula L m (n + 1) →ₗ subformula L (m + 1) n :=
{ to_fun := push',
  map_neg' := λ p, by simp,
  map_imply' := λ p q, by simp[imply_def, ←or_eq],
  map_and' := λ p q, by simp[←and_eq],
  map_or' := λ p q, by simp[←or_eq],
  map_top' := by simp[←verum_eq],
  map_bot' := by simp[←falsum_eq] }

@[simp] lemma push_relation {k} (r : L.pr k) (v : fin k → subterm L m (n + 1)) :
  push (relation r v) = relation r (subterm.push ∘ v) := by simp[push]

@[simp] lemma push_neg_relation {k} (r : L.pr k) (v : fin k → subterm L m (n + 1)) :
  push (neg_relation r v) = neg_relation r (subterm.push ∘ v) := by simp[push]

@[simp] lemma push_fal (p : subformula L m (n + 1 + 1)) :
  push (∀'p) = ∀'push p := by simp[push]; unfold has_univ_quantifier'.univ; simp; refl

@[simp] lemma push_ex (p : subformula L m (n + 1 + 1)) :
  push (∃'p) = ∃'push p := by simp[push]; unfold has_exists_quantifier'.ex; simp; refl

end push

section pull

@[simp] def pull' {m} : Π {n}, subformula L (m + 1) n → subformula L m (n + 1)
| n verum              := ⊤
| n falsum             := ⊥
| n (relation p v)     := relation p (subterm.pull ∘ v)
| n (neg_relation p v) := neg_relation p (subterm.pull ∘ v)
| n (and p q)          := p.pull' ⊓ q.pull'
| n (or p q)           := p.pull' ⊔ q.pull'
| n (fal p)            := ∀'p.pull'
| n (ex p)             := ∃'p.pull'

@[simp] lemma pull_neg (p : subformula L (m + 1) n) : (∼p).pull' = ∼p.pull' :=
by induction p; simp[mlift, ←verum_eq, ←falsum_eq, ←and_eq, ←or_eq, ←not_eq, ←fal_eq, ←ex_eq, *] at*

def pull : subformula L (m + 1) n →ₗ subformula L m (n + 1) :=
{ to_fun := pull',
  map_neg' := λ p, by simp,
  map_imply' := λ p q, by simp[imply_def, ←or_eq],
  map_and' := λ p q, by refl,
  map_or' := λ p q, by refl,
  map_top' := by refl,
  map_bot' := by refl }

@[simp] lemma pull_relation {k} (r : L.pr k) (v : fin k → subterm L (m + 1) n) :
  pull (relation r v) = relation r (subterm.pull ∘ v) := rfl

@[simp] lemma pull_neg_relation {k} (r : L.pr k) (v : fin k → subterm L (m + 1) n) :
  pull (neg_relation r v) = neg_relation r (subterm.pull ∘ v) := rfl

end pull

def msubst (t : subterm L m n) : subformula L (m + 1) n →ₗ subformula L m n :=
rew (t *> subterm.metavar)

section msubst
variables (u : subterm L m n)

@[simp] lemma msubst_relation {p} (r : L.pr p) (v) :
  msubst u (relation r v) = relation r (subterm.msubst u ∘ v) := by simp[msubst, subterm.msubst]

@[simp] lemma msubst_neg_relation {p} (r : L.pr p) (v) :
  msubst u (neg_relation r v) = neg_relation r (subterm.msubst u ∘ v) := by simp[msubst, subterm.msubst]

@[simp] lemma msubst_fal (p : subformula L (m + 1) (n + 1)) :
  msubst u (∀'p) = ∀'msubst u.lift p := by simp[msubst, fin.comp_left_concat]

@[simp] lemma msubst_ex (p : subformula L (m + 1) (n + 1)) :
  msubst u (∃'p) = ∃'msubst u.lift p := by simp[msubst, fin.comp_left_concat]

end msubst

def subst (u : subterm L m n) : subformula L m (n + 1) →ₗ subformula L m n := (msubst u).comp push

section subst
variables (u : subterm L m n)

@[simp] lemma subst_relation {p} (r : L.pr p) (v) :
  subst u (relation r v) = relation r (subterm.subst u ∘ v) := by simp[subst, subterm.subst, subterm.msubst]

@[simp] lemma subst_neg_relation {p} (r : L.pr p) (v) :
  subst u (neg_relation r v) = neg_relation r (subterm.subst u ∘ v) := by simp[subst, subterm.subst, subterm.msubst]

@[simp] lemma subst_fal (p : subformula L m (n + 1 + 1)) :
  subst u (∀'p) = ∀'subst u.lift p := by simp[subst]

@[simp] lemma subst_ex (p : subformula L m (n + 1 + 1)) :
  subst u (∃'p) = ∃'subst u.lift p := by simp[subst]

end subst

@[simp] def to_fol : Π {n}, subformula L m n → fol.subformula L m n
| n verum              := ⊤
| n falsum             := ⊥
| n (relation r v)     := fol.subformula.relation r v
| n (neg_relation r v) := ∼fol.subformula.relation r v
| n (and p q)          := p.to_fol ⊓ q.to_fol
| n (or p q)           := p.to_fol ⊔ q.to_fol
| n (fal p)            := ∀'p.to_fol
| n (ex p)             := ∃'p.to_fol

@[simp] lemma to_fol_verum : to_fol (⊤ : subformula L m n) = ⊤ := rfl

@[simp] lemma to_fol_falsum : to_fol (⊥ : subformula L m n) = ⊥ := rfl

@[simp] lemma to_fol_and (p q : subformula L m n) : to_fol (p ⊓ q) = to_fol p ⊓ to_fol q := rfl

@[simp] lemma to_fol_or (p q : subformula L m n) : to_fol (p ⊔ q) = to_fol p ⊔ to_fol q := rfl

@[simp] lemma to_fol_fal (p : subformula L m (n + 1)) : to_fol (∀'p) = ∀'to_fol p := rfl

@[simp] lemma to_fol_ex (p : subformula L m (n + 1)) : to_fol (∃'p) = ∃'to_fol p := rfl

end subformula

end Tait

namespace subformula
variables {L m n}

@[simp] def to_Tait : Π {n}, subformula L m n → Tait.subformula L m n
| n verum          := ⊤
| n (relation r v) := Tait.subformula.relation r v
| n (imply p q)    := p.to_Tait ⟶ q.to_Tait
| n (neg p)        := ∼p.to_Tait
| n (fal p)        := ∀'p.to_Tait

@[simp] lemma to_Tait_verum : to_Tait (⊤ : subformula L m n) = ⊤ := rfl

end subformula

namespace Tait

namespace subformula
variables {L₁ L₂} (l : L₁ ⤳ᴸ L₂) {m n}

@[simp] def of_lhom' : Π {n}, subformula L₁ m n → subformula L₂ m n
| n verum              := ⊤
| n falsum             := ⊥
| n (relation r v)     := relation (l.pr _ r) (λ i, subterm.of_lhom l (v i))
| n (neg_relation r v) := neg_relation (l.pr _ r) (λ i, subterm.of_lhom l (v i))
| n (and p q)          := of_lhom' p ⊓ of_lhom' q
| n (or p q)           := of_lhom' p ⊔ of_lhom' q
| n (fal p)            := ∀'of_lhom' p
| n (ex p)             := ∃'of_lhom' p

@[simp] lemma of_lhom'_neg (p : subformula L₁ m n) : of_lhom' l (∼p) = ∼ of_lhom' l p :=
by induction p; simp[mlift, ←verum_eq, ←falsum_eq, ←and_eq, ←or_eq, ←not_eq, ←fal_eq, ←ex_eq, *] at*

def of_lhom : subformula L₁ m n →ₗ subformula L₂ m n :=
{ to_fun := of_lhom' l,
  map_neg' := λ p, by simp,
  map_imply' := λ p q, by simp[imply_def, ←or_eq],
  map_and' := λ p q, by refl,
  map_or' := λ p q, by refl,
  map_top' := by refl,
  map_bot' := by refl }

@[simp] lemma of_lhom_rel {k} (r : L₁.pr k) (v : fin k → subterm L₁ m n) :
  of_lhom l (relation r v) = relation (l.pr k r) (λ i, subterm.of_lhom l (v i)) := rfl

@[simp] lemma of_lhom_neg_rel {k} (r : L₁.pr k) (v : fin k → subterm L₁ m n) :
  of_lhom l (neg_relation r v) = neg_relation (l.pr k r) (λ i, subterm.of_lhom l (v i)) := rfl

@[simp] lemma of_lhom_fal (p : subformula L₁ m (n + 1)) : of_lhom l (∀'p) = ∀'of_lhom l p := rfl

@[simp] lemma of_lhom_ex (p : subformula L₁ m (n + 1)) : of_lhom l (∃'p) = ∃'of_lhom l p := rfl

end subformula

end Tait

end fol