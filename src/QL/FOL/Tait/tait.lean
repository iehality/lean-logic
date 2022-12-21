import QL.FOL.coding QL.FOL.deduction

universes u v

namespace fol
open_locale logic_symbol aclogic

variables (L L₁ L₂ : language.{u}) (μ : Type v) (μ₁ : Type*) (μ₂ : Type*) (m m₁ m₂ n : ℕ)

namespace Tait

inductive subformula (μ : Type v) : ℕ → Type (max u v)
| verum        {n} : subformula n
| falsum       {n} : subformula n
| relation     {n} : ∀ {p}, L.pr p → (fin p → subterm L μ n) → subformula n
| neg_relation {n} : ∀ {p}, L.pr p → (fin p → subterm L μ n) → subformula n
| and          {n} : subformula n → subformula n → subformula n
| or           {n} : subformula n → subformula n → subformula n
| fal          {n} : subformula (n + 1) → subformula n
| ex           {n} : subformula (n + 1) → subformula n

@[reducible] def formula := subformula L μ 0

@[reducible] def bounded_subformula (m n : ℕ) := subformula L (fin m) n

@[reducible] def bounded_formula (m : ℕ) := bounded_subformula L m 0

@[reducible] def sentence := bounded_formula L 0

variables {L μ n}

namespace subformula

instance : has_univ_quantifier' (subformula L μ) := ⟨@fal L μ⟩

instance : has_exists_quantifier' (subformula L μ) := ⟨@ex L μ⟩

attribute [pattern]  has_sup.sup has_inf.inf has_univ_quantifier.univ has_exists_quantifier.ex

@[simp] def not : ∀ {n}, subformula L μ n → subformula L μ n
| n verum              := falsum
| n falsum             := verum
| n (relation r v)     := neg_relation r v
| n (neg_relation r v) := relation r v
| n (and p q)          := or (not p) (not q)
| n (or p q)           := and (not p) (not q)
| n (fal p)            := ex (not p)
| n (ex p)             := fal (not p)

def imply (p q : subformula L μ n) := or (not p) q

instance : has_logic_symbol (subformula L μ n) := Tait.logic_simbol_default (subformula L μ n) verum falsum not and or
 
lemma verum_eq : @verum L μ n = ⊤ := rfl
lemma falsum_eq : @falsum L μ n = ⊥ := rfl
lemma and_eq : @and L μ n = has_inf.inf := rfl
lemma or_eq : @or L μ n = has_sup.sup := rfl
lemma not_eq : @not L μ n = has_negation.neg := rfl
lemma imply_eq : @imply L μ n = has_arrow.arrow := rfl
lemma imply_def (p q : subformula L μ n) : (p ⟶ q) = (∼p) ⊔ q := by simp[←imply_eq, imply]; refl
lemma fal_eq : @fal L μ n = has_univ_quantifier'.univ := rfl
lemma ex_eq : @ex L μ n = has_exists_quantifier'.ex := rfl

@[simp] lemma and.inj' (p₁ q₁ p₂ q₂ : subformula L μ n) : p₁ ⊓ p₂ = q₁ ⊓ q₂ ↔ p₁ = q₁ ∧ p₂ = q₂ :=
by simp[has_inf.inf]

@[simp] lemma or.inj' (p₁ q₁ p₂ q₂ : subformula L μ n) : p₁ ⊔ p₂ = q₁ ⊔ q₂ ↔ p₁ = q₁ ∧ p₂ = q₂ :=
by simp[has_sup.sup]

@[simp] lemma fal.inj' (p q : subformula L μ (n + 1)) : ∀'p = ∀'q ↔ p = q := ⟨fal.inj, congr_arg _⟩

@[simp] lemma ex.inj' (p q : subformula L μ (n + 1)) : ∃'p = ∃'q ↔ p = q := 
by simp[has_exists_quantifier'.ex]

@[simp] lemma not_falsum : ∼(⊥ : subformula L μ n) = ⊤ := rfl

@[simp] lemma not_verum : ∼(⊤ : subformula L μ n) = ⊥ := rfl

@[simp] lemma not_relation {k} (r : L.pr k) (v : fin k → subterm L μ n) : ∼(relation r v) = neg_relation r v := rfl

@[simp] lemma not_neg_relation {k} (r : L.pr k) (v : fin k → subterm L μ n) : ∼(neg_relation r v) = relation r v := rfl

@[simp] lemma not_and (p q : subformula L μ n) : ∼(p ⊓ q) = ∼p ⊔ ∼q := rfl

@[simp] lemma not_or (p q : subformula L μ n) : ∼(p ⊔ q) = ∼p ⊓ ∼q := rfl

@[simp] lemma not_fal (p : subformula L μ (n + 1)) : ∼(∀'p) = ∃'∼p := rfl

@[simp] lemma not_ex (p : subformula L μ (n + 1)) : ∼(∃'p) = ∀'∼p := rfl

@[simp] def complexity : Π {n}, subformula L μ n → ℕ
| n verum              := 0
| n falsum             := 0
| n (relation r v)     := 0
| n (neg_relation r v) := 0
| n (and p q)          := max p.complexity q.complexity + 1
| n (or p q)           := max p.complexity q.complexity + 1
| n (fal p)            := p.complexity + 1
| n (ex p)             := p.complexity + 1

@[simp] lemma complexity_top : (⊤ : subformula L μ n).complexity = 0 := by refl

@[simp] lemma complexity_bot : (⊥ : subformula L μ n).complexity = 0 := by refl

@[simp] lemma complexity_and (p q : subformula L μ n) : (p ⊓ q).complexity = max p.complexity q.complexity + 1 := by refl

@[simp] lemma complexity_or (p q : subformula L μ n) : (p ⊔ q).complexity = max p.complexity q.complexity + 1 := by refl

@[simp] lemma complexity_fal (p : subformula L μ (n + 1)) : (∀'p).complexity = p.complexity + 1 := by refl

@[simp] lemma complexity_ex (p : subformula L μ (n + 1)) : (∃'p).complexity = p.complexity + 1 := by refl

def cases' {C : Π n, subformula L μ n → Sort*}
  (hverum : Π {n : ℕ}, C n ⊤)
  (hfalsum : Π {n : ℕ}, C n ⊥)
  (hrelation : Π {n l : ℕ} (r : L.pr l) (v : fin l → subterm L μ n), C n (relation r v))
  (hneg_relation : Π {n l : ℕ} (r : L.pr l) (v : fin l → subterm L μ n), C n (neg_relation r v))
  (hand : Π {n : ℕ} (p q : subformula L μ n), C n (p ⊓ q))
  (hor : Π {n : ℕ} (p q : subformula L μ n), C n (p ⊔ q))
  (hfal : Π {n : ℕ} (p : subformula L μ (n + 1)), C n (∀'p))
  (hex : Π {n : ℕ} (p : subformula L μ (n + 1)), C n (∃'p)) :
  Π {n : ℕ} (p : subformula L μ n), C n p
| n verum              := hverum
| n falsum             := hfalsum
| n (relation r v)     := hrelation r v
| n (neg_relation r v) := hneg_relation r v
| n (and p q)          := hand p q
| n (or p q)           := hor p q
| n (fal p)            := hfal p
| n (ex p)             := hex p

@[elab_as_eliminator]
protected def cases_on' {C : Π n, subformula L μ n → Sort*}
  {n : ℕ} (p : subformula L μ n)
  (verum : Π {n : ℕ}, C n ⊤)
  (falsum : Π {n : ℕ}, C n ⊥)
  (relation : Π {n l : ℕ} (r : L.pr l) (v : fin l → subterm L μ n), C n (relation r v))
  (neg_relation : Π {n l : ℕ} (r : L.pr l) (v : fin l → subterm L μ n), C n (neg_relation r v))
  (and : Π {n : ℕ} (p q : subformula L μ n), C n (p ⊓ q))
  (or : Π {n : ℕ} (p q : subformula L μ n), C n (p ⊔ q))
  (fal : Π {n : ℕ} (p : subformula L μ (n + 1)), C n (∀'p))
  (ex : Π {n : ℕ} (p : subformula L μ (n + 1)), C n (∃'p)) :
  C n p :=
cases' @verum @falsum @relation @neg_relation @and @or @fal @ex p

def ind {C : Π n, subformula L μ n → Sort*}
  (hverum : Π {n : ℕ}, C n ⊤)
  (hfalsum : Π {n : ℕ}, C n ⊥)
  (hrelation : Π {n l : ℕ} (r : L.pr l) (v : fin l → subterm L μ n), C n (relation r v))
  (hneg_relation : Π {n l : ℕ} (r : L.pr l) (v : fin l → subterm L μ n), C n (neg_relation r v))
  (hand : Π {n : ℕ} (p q : subformula L μ n), C n p → C n q → C n (p ⊓ q))
  (hor : Π {n : ℕ} (p q : subformula L μ n), C n p → C n q → C n (p ⊔ q))
  (hfal : Π {n : ℕ} (p : subformula L μ (n + 1)), C (n + 1) p → C n (∀'p))
  (hex : Π {n : ℕ} (p : subformula L μ (n + 1)), C (n + 1) p → C n (∃'p)) :
  Π {n : ℕ} (p : subformula L μ n), C n p
| n verum              := hverum
| n falsum             := hfalsum
| n (relation r v)     := hrelation r v
| n (neg_relation r v) := hneg_relation r v
| n (and p q)          := hand p q (ind p) (ind q)
| n (or p q)           := hor p q (ind p) (ind q)
| n (fal p)            := hfal p (ind p)
| n (ex p)             := hex p (ind p)

--普通に帰納法をすると論理記号で表示されないから
@[elab_as_eliminator]
protected def ind_on {C : Π n, subformula L μ n → Sort*}
  {n : ℕ} (p : subformula L μ n)
  (verum : Π {n : ℕ}, C n ⊤)
  (falsum : Π {n : ℕ}, C n ⊥)
  (relation : Π {n l : ℕ} (r : L.pr l) (v : fin l → subterm L μ n), C n (relation r v))
  (neg_relation : Π {n l : ℕ} (r : L.pr l) (v : fin l → subterm L μ n), C n (neg_relation r v))
  (and : Π {n : ℕ} (p q : subformula L μ n), C n p → C n q → C n (p ⊓ q))
  (or : Π {n : ℕ} (p q : subformula L μ n), C n p → C n q → C n (p ⊔ q))
  (fal : Π {n : ℕ} (p : subformula L μ (n + 1)), C (n + 1) p → C n (∀'p))
  (ex : Π {n : ℕ} (p : subformula L μ (n + 1)), C (n + 1) p → C n (∃'p)) :
  C n p :=
ind @verum @falsum @relation @neg_relation @and @or @fal @ex p

def ind_succ {C : Π n, subformula L μ (n + 1) → Sort*}
  (hverum : Π {n : ℕ}, C n ⊤)
  (hfalsum : Π {n : ℕ}, C n ⊥)
  (hrelation : Π {n l : ℕ} (r : L.pr l) (v : fin l → subterm L μ (n + 1)), C n (relation r v))
  (hneg_relation : Π {n l : ℕ} (r : L.pr l) (v : fin l → subterm L μ (n + 1)), C n (neg_relation r v))
  (hand : Π {n : ℕ} (p q : subformula L μ (n + 1)), C n p → C n q → C n (p ⊓ q))
  (hor : Π {n : ℕ} (p q : subformula L μ (n + 1)), C n p → C n q → C n (p ⊔ q))
  (hfal : Π {n : ℕ} (p : subformula L μ (n + 1 + 1)), C (n + 1) p → C n (∀'p))
  (hex : Π {n : ℕ} (p : subformula L μ (n + 1 + 1)), C (n + 1) p → C n (∃'p)) :
  Π {n : ℕ} (p : subformula L μ (n + 1)), C n p
| n verum              := hverum
| n falsum             := hfalsum
| n (relation r v)     := hrelation r v
| n (neg_relation r v) := hneg_relation r v
| n (and p q)          := hand p q (ind_succ p) (ind_succ q)
| n (or p q)           := hor p q (ind_succ p) (ind_succ q)
| n (fal p)            := hfal p (ind_succ p)
| n (ex p)             := hex p (ind_succ p)
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.complexity)⟩]}

@[elab_as_eliminator]
def ind_succ_on {C : Π n, subformula L μ (n + 1) → Sort*}
  {n : ℕ} (p : subformula L μ (n + 1))
  (verum : Π {n : ℕ}, C n ⊤)
  (falsum : Π {n : ℕ}, C n ⊥)
  (relation : Π {n l : ℕ} (r : L.pr l) (v : fin l → subterm L μ (n + 1)), C n (relation r v))
  (neg_relation : Π {n l : ℕ} (r : L.pr l) (v : fin l → subterm L μ (n + 1)), C n (neg_relation r v))
  (and : Π {n : ℕ} (p q : subformula L μ (n + 1)), C n p → C n q → C n (p ⊓ q))
  (or : Π {n : ℕ} (p q : subformula L μ (n + 1)), C n p → C n q → C n (p ⊔ q))
  (fal : Π {n : ℕ} (p : subformula L μ (n + 1 + 1)), C (n + 1) p → C n (∀'p))
  (ex : Π {n : ℕ} (p : subformula L μ (n + 1 + 1)), C (n + 1) p → C n (∃'p)) :
  C n p :=
ind_succ @verum @falsum @relation @neg_relation @and @or @fal @ex p

section rew
variables {μ₁ μ₂} (s : μ₁ → subterm L μ₂ n) (f : μ₁ → μ₂)

@[simp] def rew' {μ₁ μ₂} : Π {n}, (μ₁ → subterm L μ₂ n) → subformula L μ₁ n → subformula L μ₂ n
| n s verum              := verum
| n s falsum             := falsum
| n s (relation p v)     := relation p (λ i, subterm.rew s (v i))
| n s (neg_relation p v) := neg_relation p (λ i, subterm.rew s (v i))
| n s (and p q)          := and (p.rew' s) (q.rew' s)
| n s (or p q)           := or (p.rew' s) (q.rew' s)
| n s (fal p)            := fal (p.rew' (subterm.lift ∘ s))
| n s (ex p)             := ex (p.rew' (subterm.lift ∘ s))

@[simp] lemma rew'_neg (p : subformula L μ₁ n) : (∼p).rew' s = ∼(p.rew' s) :=
by induction p; simp[←verum_eq, ←falsum_eq, ←and_eq, ←or_eq, ←not_eq, ←fal_eq, ←ex_eq, *] at*

def rew (s : μ₁ → subterm L μ₂ n) : subformula L μ₁ n →ₗ subformula L μ₂ n :=
{ to_fun := rew' s,
  map_neg' := λ p, by simp,
  map_imply' := λ p q, by simp[imply_def, ←or_eq],
  map_and' := λ p q, by refl,
  map_or' := λ p q, by refl,
  map_top' := by refl,
  map_bot' := by refl }

def map (f : μ₁ → μ₂) : subformula L μ₁ n →ₗ subformula L μ₂ n := rew (λ x, &(f x))

@[simp] lemma rew_relation {k} (r : L.pr k) (v : fin k → subterm L μ₁ n) :
  rew s (relation r v) = relation r (λ i, subterm.rew s (v i)) := rfl

@[simp] lemma rew_neg_relation {k} (r : L.pr k) (v : fin k → subterm L μ₁ n) :
  rew s (neg_relation r v) = neg_relation r (λ i, subterm.rew s (v i)) := rfl

@[simp] lemma rew_fal (p : subformula L μ₁ (n + 1)) :
  rew s (∀'p) = ∀'rew (λ x, subterm.lift (s x)) p := rfl

@[simp] lemma rew_ex (p : subformula L μ₁ (n + 1)) :
  rew s (∃'p) = ∃'rew (λ x, subterm.lift (s x)) p := rfl

@[simp] lemma map_relation {k} (r : L.pr k) (v : fin k → subterm L μ₁ n) :
  map f (relation r v) = relation r (λ x, subterm.map f (v x)) := rfl

@[simp] lemma map_neg_relation {k} (r : L.pr k) (v : fin k → subterm L μ₁ n) :
  map f (neg_relation r v) = neg_relation r (λ x, subterm.map f (v x)) := rfl

@[simp] lemma map_fal (p : subformula L μ₁ (n + 1)) :
  map f (∀'p) = ∀'map f p := rfl

@[simp] lemma map_ex (p : subformula L μ₁ (n + 1)) :
  map f (∃'p) = ∃'map f p := rfl

lemma eq_rew_of_eq {p : subformula L μ₁ n} {s₁ s₂ : μ₁ → subterm L μ₂ n} (h : s₁ = s₂) :
  rew s₁ p = rew s₂ p := by rw[h]

lemma eq_map_of_eq {p : subformula L μ₁ n} {f₁ f₂ : μ₁ → μ₂} (h : f₁ = f₂) :
  map f₁ p = map f₂ p := by rw[h]

@[simp] lemma rew_metavar (p : subformula L μ n) : rew subterm.metavar p = p :=
by induction p using fol.Tait.subformula.ind_on; simp[subterm.mlift_rew, *]

@[simp] lemma map_id (p : subformula L μ n) : map id p = p := by simp[map]

lemma rew_rew {μ₁ μ₂ μ₃} : ∀ {n} (p : subformula L μ₁ n) (s₀ : μ₁ → subterm L μ₂ n) (s₁ : μ₂ → subterm L μ₃ n),
  rew s₁ (rew s₀ p) = rew (λ x, subterm.rew s₁ (s₀ x)) p
| n verum              s₀ s₁ := by simp[verum_eq]
| n falsum             s₀ s₁ := by simp[falsum_eq]
| n (relation p v)     s₀ s₁ := by simp; funext; simp[subterm.rew_rew]
| n (neg_relation p v) s₀ s₁ := by simp; funext; simp[subterm.rew_rew]
| n (and p q)          s₀ s₁ := by simp[and_eq, rew_rew p, rew_rew q]
| n (or p q)           s₀ s₁ := by simp[or_eq, rew_rew p, rew_rew q]
| n (fal p)            s₀ s₁ := by simp[fal_eq, rew_rew p]; refine eq_rew_of_eq (by funext x; simp[subterm.lift_rew])
| n (ex p)             s₀ s₁ := by simp[ex_eq, rew_rew p]; refine eq_rew_of_eq (by funext x; simp[subterm.lift_rew])

@[simp] lemma map_map {μ₁ μ₂ μ₃} (f₁ : μ₁ → μ₂) (f₂ : μ₂ → μ₃) (p : subformula L μ₁ n) :
  map f₂ (map f₁ p) = map (f₂ ∘ f₁) p :=
by simp[map, rew_rew]

lemma map_inj_of_inj (f : μ₁ → μ₂) (I : function.injective f) :
  function.injective (map f : Tait.subformula L μ₁ n → Tait.subformula L μ₂ n) := λ p q,
begin
  induction p,
  case verum { cases q; simp[map, rew] },
  case falsum { cases q; simp[map, rew] },
  case relation : n k r v₁
  { cases q; simp[map, rew],
    case relation : _ _ r₂ v₂
    { rintros rfl rfl, simp, intros h, funext i, exact subterm.map_inj_of_inj f I (congr_fun h i) } },
  case neg_relation : n k r v₁
  { cases q; simp[map, rew],
    case neg_relation : _ _ r₂ v₂
    { rintros rfl rfl, simp, intros h, funext i, exact subterm.map_inj_of_inj f I (congr_fun h i) } },
  case and : n p₁ q₁ IH₁ IH₂ { cases q; simp[map, rew] at*, intros h₁ h₂, exact ⟨IH₁ _ h₁, IH₂ _ h₂⟩ },
  case or : n p₁ q₁ IH₁ IH₂ { cases q; simp[map, rew] at*, intros h₁ h₂, exact ⟨IH₁ _ h₁, IH₂ _ h₂⟩ },
  case fal : n p IH
  { cases q; simp[map, rew],
      case fal : _ p₂ { intros h, exact IH _ h } },
  case ex : n p IH
  { cases q; simp[map, rew],
      case ex : _ p₂ { intros h, exact IH _ h } }
end

instance : has_coe (bounded_subformula L 0 n) (subformula L μ n) := ⟨map fin.nil⟩

lemma sentence_coe_def (σ : bounded_subformula L 0 n) : (σ : subformula L μ n) = map fin.nil σ := rfl

@[simp] lemma sentence_coe_self (σ : bounded_subformula L 0 n) : (↑σ : bounded_subformula L 0 n) = σ :=
by simpa [sentence_coe_def] using @eq_map_of_eq _ _ _ _ σ fin.nil id (by ext x; exact fin_zero_elim x)

@[simp] lemma map_sentence_coe (f : fin 0 → μ₂) (σ : bounded_subformula L 0 n) :
  map f σ = σ :=
by simp[sentence_coe_def]; refine eq_map_of_eq (by ext x; exact fin_zero_elim x)

@[simp] lemma map_sentence_coe' (f : μ₁ → μ₂) (σ : bounded_subformula L 0 n) :
  map f (↑σ : subformula L μ₁ n) = σ :=
by simp only [sentence_coe_def, map_map]; refine eq_map_of_eq (by ext x; exact fin_zero_elim x)

@[simp] lemma complexity_rew (p : subformula L μ₁ n) : complexity (rew s p) = complexity p :=
by induction p using fol.Tait.subformula.ind_on; simp*

end rew

section subst

@[simp] def subst' : Π {n}, subterm L μ n → subformula L μ (n + 1) → subformula L μ n
| n u verum              := ⊤
| n u falsum             := ⊥
| n u (relation r v)     := relation r (λ i, subterm.subst u $ v i)
| n u (neg_relation r v) := neg_relation r (λ i, subterm.subst u $ v i)
| n u (and p q)          := subst' u p ⊓ subst' u q
| n u (or p q)           := subst' u p ⊔ subst' u q
| n u (fal p)            := ∀' (subst' u.lift p)
| n u (ex p)             := ∃' (subst' u.lift p)
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.2.complexity)⟩]}

@[simp] lemma subst'_neg (p : subformula L μ₁ (n + 1)) : ∀ u, subst' u (∼p) = ∼(subst' u p) :=
by apply ind_succ_on p; intros; simp[←verum_eq, ←falsum_eq, ←and_eq, ←or_eq, ←not_eq, ←fal_eq, ←ex_eq, *] at*

def subst (u : subterm L μ n) : subformula L μ (n + 1) →ₗ subformula L μ n :=
{ to_fun := subst' u,
  map_neg' := λ p, by simp; refl,
  map_imply' := λ p q, by simp[imply_def, ←or_eq],
  map_and' := λ p q, by unfold has_inf.inf; simp; refl,
  map_or' := λ p q, by unfold has_sup.sup; simp; refl,
  map_top' := by unfold has_top.top; simp; refl,
  map_bot' := by unfold has_bot.bot; simp; refl }

variables (u : subterm L μ n)

@[simp] lemma subst_relation {k} (r : L.pr k) (v : fin k → subterm L μ (n + 1)) :
  subst u (relation r v) = relation r (λ i, u.subst (v i)) := by simp[subst]

@[simp] lemma subst_neg_relation {k} (r : L.pr k) (v : fin k → subterm L μ (n + 1)) :
  subst u (neg_relation r v) = neg_relation r (λ i, u.subst (v i)) := by simp[subst]

@[simp] lemma subst_fal (p : subformula L μ (n + 1 + 1)) :
  subst u (∀'p) = ∀'subst u.lift p := by simp[←fal_eq, subst]

@[simp] lemma subst_ex (p : subformula L μ (n + 1 + 1)) :
  subst u (∃'p) = ∃'subst u.lift p := by simp[←ex_eq, subst]

@[simp] lemma complexity_subst (p : subformula L μ (n + 1)) : ∀ u, complexity (subst u p) = complexity p :=
by apply ind_succ_on p; intros; simp*

variables {μ₁ μ₂} (f : μ₁ → μ₂)

lemma map_subst (p : subformula L μ₁ (n + 1)) : ∀ (u : subterm L μ₁ n),
  map f (subst u p) = subst (u.map f) (map f p) :=
by apply ind_succ_on p; intros; simp[*, subterm.map_subst, subterm.map_lift]

end subst

@[simp] def of_tait : Π {n}, subformula L μ n → fol.subformula L μ n
| n verum              := ⊤
| n falsum             := ⊥
| n (relation r v)     := fol.subformula.relation r v
| n (neg_relation r v) := ∼fol.subformula.relation r v
| n (and p q)          := p.of_tait ⊓ q.of_tait
| n (or p q)           := p.of_tait ⊔ q.of_tait
| n (fal p)            := ∀'p.of_tait
| n (ex p)             := ∃'p.of_tait

section of_tait

@[simp] lemma of_tait_verum : (of_tait (⊤ : Tait.subformula L μ n)) = ⊤ := rfl

@[simp] lemma of_tait_falsum : (of_tait (⊥ : Tait.subformula L μ n)) = ⊥ := rfl

@[simp] lemma of_tait_and (p q : subformula L μ n) : of_tait (p ⊓ q) = of_tait p ⊓ of_tait q := rfl

@[simp] lemma of_tait_or (p q : subformula L μ n) : of_tait (p ⊔ q) = of_tait p ⊔ of_tait q := rfl

@[simp] lemma of_tait_fal (p : subformula L μ (n + 1)) : of_tait (∀'p) = ∀'of_tait p := rfl

@[simp] lemma of_tait_ex (p : subformula L μ (n + 1)) : of_tait (∃'p) = ∃'of_tait p := rfl

lemma of_tait_subst (p : bounded_subformula L m (n + 1)) : ∀ t, of_tait (subst t p) = fol.subformula.subst t (of_tait p) :=
by apply ind_succ_on p; intros ; simp*

end of_tait

section bounded
variables {m}

section mlift

def mlift {m n} : bounded_subformula L m n →ₗ bounded_subformula L (m + 1) n := map fin.cast_succ

@[simp] lemma mlift_relation {k} (r : L.pr k) (v : fin k → bounded_subterm L m n) :
  mlift (relation r v) = relation r (λ i, (v i).mlift) := rfl

@[simp] lemma mlift_neg_relation {k} (r : L.pr k) (v : fin k → bounded_subterm L m n) :
  mlift (neg_relation r v) = neg_relation r (λ i, (v i).mlift) := rfl

@[simp] lemma mlift_fal (p : bounded_subformula L m (n + 1)) :
  mlift (∀'p) = ∀'mlift p := rfl

@[simp] lemma mslift_ex (p : bounded_subformula L m (n + 1)) :
  mlift (∃'p) = ∃'mlift p := rfl

@[simp] lemma mlift_coe (σ : bounded_subformula L 0 n) : mlift (σ : bounded_subformula L m n) = σ :=
by { simp only [sentence_coe_def, mlift, map_map], refine eq_map_of_eq (by ext x; exact fin_zero_elim x) }

lemma mlift_inj : function.injective (@mlift L m n) := map_inj_of_inj _ (rel_embedding.injective _)

@[simp] lemma mlift_inj' (p q : bounded_subformula L m n) :
  mlift p = mlift q ↔ p = q :=
⟨λ h, (map_inj_of_inj _ (rel_embedding.injective _)) h, λ h, by rw[h]⟩

end mlift

section push

@[simp] def push' {m} : Π {n}, bounded_subformula L m (n + 1) → bounded_subformula L (m + 1) n
| n verum              := ⊤
| n falsum             := ⊥
| n (relation p v)     := relation p (λ i, (v i).push)
| n (neg_relation p v) := neg_relation p (λ i, (v i).push)
| n (and p q)          := p.push' ⊓ q.push'
| n (or p q)           := p.push' ⊔ q.push'
| n (fal p)            := ∀'p.push'
| n (ex p)             := ∃'p.push'
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.complexity)⟩]}

@[simp] lemma push'_neg : ∀ {n} (p : bounded_subformula L m (n + 1)), (∼p).push' = ∼p.push'
| n verum              := by simp[←falsum_eq, ←verum_eq, ←not_eq]
| n falsum             := by simp[←falsum_eq, ←verum_eq, ←not_eq]
| n (relation p v)     := by simp
| n (neg_relation p v) := by simp
| n (and p q)          := by simp[←not_eq, ←and_eq, ←or_eq]; exact ⟨push'_neg p, push'_neg q⟩
| n (or p q)           := by simp[←not_eq, ←and_eq, ←or_eq]; exact ⟨push'_neg p, push'_neg q⟩
| n (fal p)            := by simp[←not_eq, ←fal_eq, ←ex_eq]; rw[←fal_eq, ←ex_eq]; simp; exact push'_neg p
| n (ex p)             := by simp[←not_eq, ←fal_eq, ←ex_eq]; rw[←fal_eq, ←ex_eq]; simp; exact push'_neg p
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.complexity)⟩]}

def push : bounded_subformula L m (n + 1) →ₗ bounded_subformula L (m + 1) n :=
{ to_fun := push',
  map_neg' := λ p, by simp,
  map_imply' := λ p q, by simp[imply_def, ←or_eq],
  map_and' := λ p q, by simp[←and_eq],
  map_or' := λ p q, by simp[←or_eq],
  map_top' := by simp[←verum_eq],
  map_bot' := by simp[←falsum_eq] }

@[simp] lemma push_relation {k} (r : L.pr k) (v : fin k → bounded_subterm L m (n + 1)) :
  push (relation r v) = relation r (λ i, (v i).push) := by simp[push]

@[simp] lemma push_neg_relation {k} (r : L.pr k) (v : fin k → bounded_subterm L m (n + 1)) :
  push (neg_relation r v) = neg_relation r (λ i, (v i).push) := by simp[push]

@[simp] lemma push_fal (p : bounded_subformula L m (n + 1 + 1)) :
  push (∀'p) = ∀'push p := by simp[push]; unfold has_univ_quantifier'.univ; simp; refl

@[simp] lemma push_ex (p : bounded_subformula L m (n + 1 + 1)) :
  push (∃'p) = ∃'push p := by simp[push]; unfold has_exists_quantifier'.ex; simp; refl

@[simp] lemma complexity_push {n} (p : bounded_subformula L m (n + 1)) : p.push.complexity = p.complexity :=
by apply ind_succ_on p; intros; simp*

end push

section pull

@[simp] def pull' {m} : Π {n}, bounded_subformula L (m + 1) n → bounded_subformula L m (n + 1)
| n verum              := ⊤
| n falsum             := ⊥
| n (relation p v)     := relation p (λ i, (v i).pull)
| n (neg_relation p v) := neg_relation p (λ i, (v i).pull)
| n (and p q)          := p.pull' ⊓ q.pull'
| n (or p q)           := p.pull' ⊔ q.pull'
| n (fal p)            := ∀'p.pull'
| n (ex p)             := ∃'p.pull'

@[simp] lemma pull_neg (p : bounded_subformula L (m + 1) n) : (∼p).pull' = ∼p.pull' :=
by induction p; simp[←verum_eq, ←falsum_eq, ←and_eq, ←or_eq, ←not_eq, ←fal_eq, ←ex_eq, *] at*; refl

def pull : bounded_subformula L (m + 1) n →ₗ bounded_subformula L m (n + 1) :=
{ to_fun := pull',
  map_neg' := λ p, by simp,
  map_imply' := λ p q, by simp[imply_def, ←or_eq],
  map_and' := λ p q, by refl,
  map_or' := λ p q, by refl,
  map_top' := by refl,
  map_bot' := by refl }

@[simp] lemma pull_relation {k} (r : L.pr k) (v : fin k → bounded_subterm L (m + 1) n) :
  pull (relation r v) = relation r (λ i, (v i).pull) := rfl

@[simp] lemma pull_neg_relation {k} (r : L.pr k) (v : fin k → bounded_subterm L (m + 1) n) :
  pull (neg_relation r v) = neg_relation r (λ i, (v i).pull) := rfl

@[simp] lemma pull_fal (p : bounded_subformula L (m + 1) (n + 1)) :
  pull (∀'p) = ∀'pull p := by simp[pull]; unfold has_univ_quantifier'.univ; simp; refl

@[simp] lemma pull_ex (p : bounded_subformula L (m + 1) (n + 1)) :
  pull (∃'p) = ∃'pull p := by simp[pull]; unfold has_exists_quantifier'.ex; simp; refl

@[simp] lemma pull_push (p : bounded_subformula L m (n + 1)) : p.push.pull = p :=
by apply ind_succ_on p; intros; simp[*, (∘)]

end pull

section cast_le
variables {m₁ m₂} (h : m₁ ≤ m₂)

def cast_le (h : m₁ ≤ m₂) : bounded_subformula L m₁ n →ₗ bounded_subformula L m₂ n :=
map (fin.cast_le h)

@[simp] lemma cast_le_inj (p q : bounded_subformula L m₁ n) : cast_le h p = cast_le h q ↔ p = q :=
⟨λ h, map_inj_of_inj _ (rel_embedding.injective _) h, λ h, by simp[h]⟩

@[simp] lemma cast_le_function {k} (r : L.pr k) (v : fin k → bounded_subterm L m₁ n) :
  cast_le h (relation r v) = relation r (λ i, subterm.cast_le h (v i)) :=
by simp[cast_le]; refl

@[simp] lemma cast_le_neg_function {k} (r : L.pr k) (v : fin k → bounded_subterm L m₁ n) :
  cast_le h (neg_relation r v) = neg_relation r (λ i, subterm.cast_le h (v i)) :=
by simp[cast_le]; refl

@[simp] lemma cast_le_fal (p : bounded_subformula L m₁ (n + 1)) :
  cast_le h (∀'p) = ∀'(cast_le h p) :=
by simp[cast_le]; refl

@[simp] lemma cast_le_ex (p : bounded_subformula L m₁ (n + 1)) :
  cast_le h (∃'p) = ∃'(cast_le h p) :=
by simp[cast_le]; refl

@[simp] lemma cast_le_cast_le {m₁ m₂ m₃ : ℕ} (h₁ : m₁ ≤ m₂) (h₂ : m₂ ≤ m₃) (p : bounded_subformula L m₁ n) :
  cast_le h₂ (cast_le h₁ p) = cast_le (le_trans h₁ h₂) p :=
by simp[cast_le]

@[simp] lemma uniform_subst (u : bounded_subterm L m₁ n) (p : bounded_subformula L m₁ (n + 1)) :
  cast_le h (subst u p) = subst (subterm.cast_le h u) (cast_le h p) :=
by simp[cast_le, subterm.cast_le, map_subst]

variables {m₁ m₂} (f : fin (m₁ + 1) → fin m₂)

@[simp] lemma cast_eq_id (h : m ≤ m) :
  (cast_le h : bounded_subformula L m n→ bounded_subformula L m n) = id :=
by { ext p, simp[cast_le, show ⇑(fin.cast_le h) = id, by funext x; simp; ext; simp],  }

lemma cast_le_eq_mlift (p : bounded_subformula L m n) (h : m ≤ m + 1) :
  cast_le h p = mlift p :=
by simp[cast_le, mlift]; refine eq_map_of_eq (by ext x; simp)

@[simp] lemma cast_le_mlift (p : bounded_subformula L m₁ n) (h : m₁ + 1 ≤ m₂) :
  cast_le h (mlift p) = cast_le (nat.le_of_succ_le h) p :=
by simp[cast_le, mlift]; congr

@[simp] lemma mlift_cast_le (p : bounded_subformula L m₁ n) (h : m₁ ≤ m₂) :
  mlift (cast_le h p) = cast_le (le_add_right h) p :=
by simp[cast_le, mlift]; congr

lemma push_eq_subst_mlift (p : bounded_subformula L m (n + 1)) :
  push p = subst &(fin.last m) p.mlift :=
by apply ind_succ_on p; intros; simp*

@[simp] lemma uniform_push (h : m₁ + 1 ≤ m₂) (p : bounded_subformula L m₁ (n + 1)) :
  cast_le h (push p) = subst &(fin.cast_le h $ fin.last m₁) (cast_le (nat.le_of_succ_le h) p) :=
by simp[push_eq_subst_mlift]

end cast_le

section of_tait

lemma of_tait_mlift (p : bounded_subformula L m n) : of_tait (mlift p) = fol.subformula.mlift (of_tait p) :=
by induction p using fol.Tait.subformula.ind_on; simp*

lemma of_tait_push (p : bounded_subformula L m (n + 1)) : of_tait (push p) = fol.subformula.push (of_tait p) :=
by apply ind_succ_on p; intros; simp*

lemma of_tait_pull (p : bounded_subformula L (m + 1) n) : of_tait (pull p) = fol.subformula.pull (of_tait p) :=
by induction p using fol.Tait.subformula.ind_on; simp*

end of_tait

end bounded

section nat

@[simp] def arity : Π {n}, subformula L ℕ n → ℕ
| n verum              := 0
| n falsum             := 0
| n (relation r v)     := ⨆ᶠ i, (v i).arity
| n (neg_relation r v) := ⨆ᶠ i, (v i).arity
| n (and p q)          := max p.arity q.arity
| n (or p q)           := max p.arity q.arity
| n (fal p)            := p.arity
| n (ex p)             := p.arity

@[simp] lemma arity_verum : (⊤ : subformula L ℕ n).arity = 0 := rfl
@[simp] lemma arity_falsum : (⊥ : subformula L ℕ n).arity = 0 := rfl
@[simp] lemma arity_and (p q : subformula L ℕ n) : (p ⊓ q).arity = max p.arity q.arity := rfl
@[simp] lemma arity_or (p q : subformula L ℕ n) : (p ⊔ q).arity = max p.arity q.arity := rfl
@[simp] lemma arity_fal (p : subformula L ℕ (n + 1)) : (∀'p).arity = p.arity := rfl
@[simp] lemma arity_ex (p : subformula L ℕ (n + 1)) : (∃'p).arity = p.arity := rfl

@[simp] lemma arity_not (p : subformula L ℕ n) : (∼p).arity = p.arity :=
by simp[←not_eq]; induction p; simp*

@[simp] def to_bform {m} : Π {n} (p : subformula L ℕ n), p.arity ≤ m → bounded_subformula L m n
| n verum              h := verum
| n falsum             h := falsum
| n (relation r v)     h := relation r (λ i, (v i).to_bterm (by simp at h; exact h i))
| n (neg_relation r v) h := neg_relation r (λ i, (v i).to_bterm (by simp at h; exact h i))
| n (and p q)          h := have p.arity ≤ m ∧ q.arity ≤ m, by simpa using h, and (p.to_bform this.1) (q.to_bform this.2)
| n (or p q)           h := have p.arity ≤ m ∧ q.arity ≤ m, by simpa using h, or (p.to_bform this.1) (q.to_bform this.2)
| n (fal p)            h := fal (p.to_bform (by simpa using h))
| n (ex p)             h := ex (p.to_bform (by simpa using h))

@[simp] lemma to_bform_verum (h) : ((⊤ : subformula L ℕ n).to_bform h : bounded_subformula L m n) = ⊤ := rfl
@[simp] lemma to_bform_falsum (h) : ((⊥ : subformula L ℕ n).to_bform h : bounded_subformula L m n) = ⊥ := rfl
@[simp] lemma to_bform_and (p q : subformula L ℕ n) (h) : 
  ((p ⊓ q).to_bform h : bounded_subformula L m n) = p.to_bform (by simp at h; exact h.1) ⊓ q.to_bform (by simp at h; exact h.2) := rfl
@[simp] lemma to_bform_or (p q : subformula L ℕ n) (h) :
  ((p ⊔ q).to_bform h : bounded_subformula L m n) = p.to_bform (by simp at h; exact h.1) ⊔ q.to_bform (by simp at h; exact h.2) := rfl
@[simp] lemma to_bform_fal (p : subformula L ℕ (n + 1)) (h) : 
  ((∀'p).to_bform h : bounded_subformula L m n) = ∀'p.to_bform (by simpa using h) := rfl
@[simp] lemma to_bform_ex (p : subformula L ℕ (n + 1)) (h) :
  ((∃'p).to_bform h : bounded_subformula L m n) = ∃'p.to_bform (by simpa using h) := rfl

@[simp] lemma to_bform_not (p : subformula L ℕ n) {h} : (to_bform (∼p) h : bounded_subformula L m n) = ∼(to_bform p (by simpa using h)) :=
by { simp[←not_eq], induction p; simp[*], 
  case and : n p q IH₁ IH₂ { refine ⟨IH₁, IH₂⟩ },
  case or  : n p q IH₁ IH₂ { refine ⟨IH₁, IH₂⟩ },
  case fal : n p IH { exact IH },
  case ex : n p IH { exact IH } }

end nat

variables (T : bounded_preTheory L m)

open axiomatic_classical_logic' axiomatic_classical_logic

lemma to_tait_not_equiv : ∀ {m} (p : Tait.bounded_formula L m), ∅ ⊢ (∼p).of_tait ⟷ ∼p.of_tait
| m verum := by simp[verum_eq]
| m falsum := by apply equiv_symm; simp[falsum_eq]
| m (relation r v) := by simp
| m (neg_relation r v) := by simp
| m (and p q) := by { simp[and_eq],
    have : ∅ ⊢ (∼p).of_tait ⊔ (∼q).of_tait ⟷ ∼p.of_tait ⊔ ∼q.of_tait,
    from equiv_or_of_equiv (to_tait_not_equiv p) (to_tait_not_equiv q),
    refine equiv_trans this (equiv_symm (neg_and_equiv_or_neg _ _)) }
| m (or p q) := by { simp[or_eq],
    have : ∅ ⊢ (∼p).of_tait ⊓ (∼q).of_tait ⟷ ∼p.of_tait ⊓ ∼q.of_tait,
    from equiv_and_of_equiv (to_tait_not_equiv p) (to_tait_not_equiv q),
    refine equiv_trans this (equiv_symm (neg_or_equiv_and_neg _ _)) }
| m (fal p) :=
    begin
      simp[fal_eq],
      have : ∅ ⊢ ∃'(∼p).of_tait ⟷ ∃'∼p.of_tait,
      from provable.equiv_exists_of_equiv (by simpa[←of_tait_push] using to_tait_not_equiv (push p)),
      refine equiv_trans this (equiv_symm $ provable.neg_forall_pnf p.of_tait)
    end
| m (ex p) :=
    begin
      simp[ex_eq],
      have : ∅ ⊢ ∀'(∼p).of_tait ⟷ ∀'∼p.of_tait,
      from provable.equiv_forall_of_equiv (by simpa[←of_tait_push] using to_tait_not_equiv (push p)),
      refine equiv_trans this (equiv_symm $ provable.neg_exists_pnf p.of_tait)
    end
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.complexity)⟩]}

end subformula

end Tait

namespace subformula
variables {L μ m n}

@[simp] def to_tait : Π {n}, subformula L μ n → Tait.subformula L μ n
| n verum          := Tait.subformula.verum
| n (relation r v) := Tait.subformula.relation r v
| n (imply p q)    := p.to_tait.imply q.to_tait
| n (neg p)        := p.to_tait.not
| n (fal p)        := p.to_tait.fal

@[simp] lemma to_tait_verum : to_tait (⊤ : subformula L μ n) = ⊤ := rfl
@[simp] lemma to_tait_imply (p q : subformula L μ n) : to_tait (p ⟶ q) = to_tait p ⟶ to_tait q := rfl
@[simp] lemma to_tait_neg (p : subformula L μ n) : to_tait (∼p) = ∼to_tait p := rfl
@[simp] lemma to_tait_fal (p : subformula L μ (n + 1)) : to_tait (∀'p) = ∀'to_tait p := rfl

variables (T : bounded_preTheory L m)

lemma to_tait_push (p : bounded_subformula L m (n + 1)) : to_tait (push p) = Tait.subformula.push (to_tait p) :=
by apply ind_succ_on p; intros; simp*

open axiomatic_classical_logic' axiomatic_classical_logic

lemma to_tait_of_tait_aux : ∀ {m} (p : bounded_formula L m), ∅ ⊢ p.to_tait.of_tait ⟷ p
| m verum := by simp[top_eq]
| m (relation r v) := by simp
| m (imply p q) :=
    begin
      simp[imply_eq, Tait.subformula.imply_def],
      have : ∅ ⊢ ∼p ⊔ q ⟷ p ⟶ q, from equiv_symm impl_iff_or,
      refine equiv_of_equiv this _ (by simp),
      refine equiv_or_of_equiv
      (equiv_symm $ equiv_trans (Tait.subformula.to_tait_not_equiv p.to_tait) (equiv_neg_of_equiv $ to_tait_of_tait_aux p))
      (equiv_symm $ to_tait_of_tait_aux q),
    end
| m (neg p) :=
    by simp[neg_eq]; refine equiv_trans (Tait.subformula.to_tait_not_equiv p.to_tait) (equiv_neg_of_equiv $ to_tait_of_tait_aux p)
| m (fal p) := by { simp[fal_eq], refine provable.equiv_forall_of_equiv
    (by { simpa[←Tait.subformula.of_tait_push, to_tait_push] using to_tait_of_tait_aux (push p) }) }
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.complexity)⟩]}

lemma to_tait_of_tait  {T : bounded_preTheory L m} (p : bounded_formula L m) : T ⊢ p.to_tait.of_tait ⟷ p :=
weakening (by simp) (to_tait_of_tait_aux p)

end subformula

end fol