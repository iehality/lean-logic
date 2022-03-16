import tactic lib data.set_like.basic

universe u

namespace fopl

structure language : Type (u+1) :=
(fn : ℕ → Type u)
(pr : ℕ → Type u)

class has_zero_symbol (L : language) := (zero : L.fn 0)

class has_succ_symbol (L : language) := (succ : L.fn 1)

class has_add_symbol (L : language) := (add : L.fn 2)

class has_mul_symbol (L : language) := (mul : L.fn 2)

class has_le_symbol (L : language) := (le : L.pr 2)

class has_mem_symbol (L : language) := (mem : L.pr 2)

variables (L : language.{u})

inductive term : Type u
| var {} : ℕ → term
| app    : ∀ {n : ℕ}, L.fn n → (fin n → term) → term

variables {L}

prefix `#`:max := term.var

notation `❨` c `❩ ` v :84 := term.app c v

def term.const (f : L.fn 0) : term L := term.app f finitary.nil

instance : inhabited (term L) := ⟨#0⟩

instance [has_zero_symbol L] : has_zero (term L) := ⟨term.app has_zero_symbol.zero finitary.nil⟩

instance [has_succ_symbol L] : has_succ (term L) := ⟨λ t, term.app has_succ_symbol.succ ‹t›⟩

instance [has_add_symbol L] : has_add (term L) := ⟨λ t u, term.app has_add_symbol.add ‹t, u›⟩

instance [has_mul_symbol L] : has_mul (term L) := ⟨λ t u, term.app has_mul_symbol.mul ‹t, u›⟩

postfix `˙`:max := numeral


@[reducible] def idvar (n : ℕ) : finitary (term L) n := λ i, #i

notation `##` := idvar _

@[simp] lemma idvar_app (n : ℕ) (i : fin n) : (## : finitary (term L) n) i = #i := rfl

variables (L)

def term_to_string [∀ n, has_to_string (L.fn n)] : term L → string
| #n := "#" ++ has_to_string.to_string n
| (@term.app _ 0 c v) := has_to_string.to_string c
| (@term.app _ 1 c v) := has_to_string.to_string c ++ "(" ++ term_to_string (v 0) ++ ")"
| (@term.app _ 2 c v) := term_to_string (v 0) ++ has_to_string.to_string c ++ term_to_string (v 1)
| (@term.app _ (n + 3) c v) :=
    has_to_string.to_string c ++ "(" ++ @has_to_string.to_string (finitary _ _) _ (λ i, term_to_string (v i)) ++ ")"

instance [∀ n, has_to_string (L.fn n)] : has_to_string (term L) := ⟨term_to_string L⟩

inductive formula : Type u
| verum : formula
| app   : ∀ {n : ℕ}, L.pr n → (fin n → term L) → formula
| equal : term L → term L → formula
| imply : formula → formula → formula
| neg   : formula → formula
| fal   : formula → formula

notation `❴` c `❵` := formula.app c

instance [has_le_symbol L] : has_preceq (term L) (formula L) := ⟨λ t u, formula.app has_le_symbol.le ‹t, u›⟩

instance [has_mem_symbol L] : has_elem (term L) (formula L) := ⟨λ t u, formula.app has_mem_symbol.mem ‹t, u›⟩

attribute [pattern]  has_eq.eq has_negation.neg has_arrow.arrow has_univ_quantifier.univ has_exists_quantifier.ex

instance : has_top (formula L) := ⟨formula.verum⟩

instance : has_arrow (formula L) := ⟨formula.imply⟩

instance : has_eq (term L) (formula L) := ⟨formula.equal⟩

local infix ` ≃₁ `:80 := ((≃) : term L → term L → formula L)

instance : has_negation (formula L) := ⟨formula.neg⟩

instance : has_univ_quantifier (formula L) := ⟨formula.fal⟩

instance : has_bot (formula L) := ⟨⁻⊤⟩

def formula_to_string [has_to_string (term L)] [∀ n, has_to_string (L.pr n)] : formula L → string
| ⊤                      := "⊤"
| (@formula.app _ 0 p v) := has_to_string.to_string p
| (@formula.app _ 1 p v) := has_to_string.to_string p ++ "(" ++ has_to_string.to_string (v 0) ++ ")"
| (@formula.app _ 2 p v) := has_to_string.to_string (v 0) ++ has_to_string.to_string p ++ has_to_string.to_string (v 1)
| (@formula.app _ (n + 3) p v) :=
    has_to_string.to_string p ++ "(" ++ @has_to_string.to_string (finitary _ _) _ v ++ ")"
| (t ≃₁ u) := has_to_string.to_string t ++ " = " ++ has_to_string.to_string u
| (p ⟶ q) := formula_to_string p ++ " → " ++ formula_to_string q
| (⁻p) := "¬(" ++ formula_to_string p ++ ")"
| (∏ p) := "∀(" ++ formula_to_string p ++ ")"

instance [has_to_string (term L)] [∀ n, has_to_string (L.pr n)] : has_to_string (formula L) := ⟨formula_to_string L⟩

@[simp] lemma formula.top_eq : @formula.verum L = (⊤) := rfl
@[simp] lemma formula.imply_eq : @formula.imply L = (⟶) := rfl
@[simp] lemma formula.equal_eq : @formula.equal L = (≃) := rfl
@[simp] lemma formula.neg_eq : @formula.neg L = has_negation.neg := rfl
@[simp] lemma formula.fal_eq : @formula.fal L = has_univ_quantifier.univ := rfl

instance : inhabited (formula L) := ⟨(#0 : term L) ≃ #0⟩

@[reducible] def theory (L : language.{u}) := set (formula L)

variables {L}

def formula.and (p : formula L) (q : formula L) : formula L := ⁻(p ⟶ ⁻q)

instance : has_inf (formula L) := ⟨formula.and⟩

def formula.or (p : formula L) (q : formula L) : formula L := ⁻p ⟶ q

instance : has_sup (formula L) := ⟨formula.or⟩

def formula.ex (p : formula L) : formula L := ⁻∏⁻p

instance : has_exists_quantifier (formula L) := ⟨formula.ex⟩

lemma formula.ex_eq (p : formula L) : (∐ p) = ⁻∏⁻p := rfl

@[simp] lemma formula.equal.inj' (t₁ u₁ t₂ u₂ : term L) : (t₁ ≃ t₂ : formula L) = (u₁ ≃ u₂) ↔ t₁ = u₁ ∧ t₂ = u₂ :=
⟨formula.equal.inj, by simp; exact congr_arg2 (≃)⟩

@[simp] lemma formula.imply.inj' (p₁ q₁ p₂ q₂ : formula L) : p₁ ⟶ p₂ = q₁ ⟶ q₂ ↔ p₁ = q₁ ∧ p₂ = q₂ :=
⟨formula.imply.inj, by simp; exact congr_arg2 (⟶)⟩

@[simp] lemma formula.neg.inj' (p q : formula L) : ⁻p = ⁻q ↔ p = q := ⟨formula.neg.inj, congr_arg _⟩

@[simp] lemma formula.and.inj' (p₁ q₁ p₂ q₂ : formula L) : p₁ ⊓ p₂ = q₁ ⊓ q₂ ↔ p₁ = q₁ ∧ p₂ = q₂ :=
by simp[has_inf.inf, formula.and]

@[simp] lemma formula.or.inj' (p₁ q₁ p₂ q₂ : formula L) : p₁ ⊔ p₂ = q₁ ⊔ q₂ ↔ p₁ = q₁ ∧ p₂ = q₂ :=
by simp[has_sup.sup, formula.or]

@[simp] lemma formula.fal.inj' (p q : formula L) : (∏ p : formula L) = ∏ q ↔ p = q := ⟨formula.fal.inj, congr_arg _⟩

@[simp] lemma formula.ex.inj' (p q : formula L) : (∐ p : formula L) = ∐ q ↔ p = q := 
by simp[has_exists_quantifier.ex, formula.ex]

@[simp] lemma formula.verum_ne_predicate {n} (r : L.pr n) (v : finitary (term L) n) :
 ⊤ ≠ formula.app r v.

@[simp] lemma formula.verum_ne_equal (t u : term L) : (⊤ : formula L) ≠ (t ≃ u).

@[simp] lemma formula.verum_ne_imply (p q : formula L) : ⊤ ≠ (p ⟶ q).

@[simp] lemma formula.verum_ne_neg (p : formula L) : ⊤ ≠ ⁻p.

@[simp] lemma formula.verum_ne_fal (p : formula L) : ⊤ ≠ ∏ p.

@[simp] lemma formula.predicate_ne_verum {n} (r : L.pr n) (v : finitary (term L) n) :
  formula.app r v ≠ ⊤.

@[simp] lemma formula.predicate_ne_equal {n} (r : L.pr n) (v : finitary (term L) n) (t u : term L) :
  formula.app r v ≠ (t ≃ u).

@[simp] lemma formula.predicate_ne_imply {n} (r : L.pr n) (v : finitary (term L) n) (p q : formula L) :
  formula.app r v ≠ p ⟶ q.

@[simp] lemma formula.predicate_ne_neg {n} (r : L.pr n) (v : finitary (term L) n) (p : formula L) :
  formula.app r v ≠ ⁻p.

@[simp] lemma formula.predicate_ne_fal {n} (r : L.pr n) (v : finitary (term L) n) (p : formula L) :
  formula.app r v ≠ ∏ p.

@[simp] lemma formula.equal_ne_verum (t u : term L) :
  (t ≃ u : formula L) ≠ ⊤.

@[simp] lemma formula.equal_ne_predivate (t u : term L) {n} (r : L.pr n) (v : finitary (term L) n) :
  (t ≃ u) ≠ formula.app r v.

@[simp] lemma formula.equal_ne_imply (t u : term L) (p q : formula L) :
  (t ≃ u) ≠ p ⟶ q.

@[simp] lemma formula.equal_ne_neg (t u : term L) (p : formula L) :
  (t ≃ u) ≠ ⁻p.

@[simp] lemma formula.equal_ne_fal (t u : term L) (p : formula L) :
  (t ≃ u : formula L) ≠ ∏ p.

@[simp] lemma formula.imply_ne_verum (p q : formula L) :
  p ⟶ q ≠ ⊤.

@[simp] lemma formula.imply_ne_predicate (p q : formula L) {n} (r : L.pr n) (v : finitary (term L) n) :
  p ⟶ q ≠ formula.app r v.

@[simp] lemma formula.imply_ne_equal (p q : formula L) (t u : term L) :
  p ⟶ q ≠ (t ≃ u).

@[simp] lemma formula.imply_ne_neg (p q r : formula L) : p ⟶ q ≠ ⁻r.

@[simp] lemma formula.imply_ne_fal (p q r : formula L) : p ⟶ q ≠ ∏ r.

@[simp] lemma formula.neg_ne_verum (p : formula L) : ⁻p ≠ ⊤.

@[simp] lemma formula.neg_ne_predicate (p : formula L) {n} (r : L.pr n) (v : finitary (term L) n) :
 ⁻p ≠ formula.app r v.

@[simp] lemma formula.neg_ne_equal (p : formula L) (t u : term L) : ⁻p ≠ (t ≃ u).

@[simp] lemma formula.neg_ne_imply (p q r : formula L) : ⁻p ≠ (q ⟶ r).

@[simp] lemma formula.neg_ne_fal (p q : formula L) : ⁻p ≠ ∏ q.

@[simp] lemma formula.fal_ne_verum (p : formula L) :
  ∏ p ≠ ⊤.

@[simp] lemma formula.fal_ne_predicate (p : formula L) {n} (r : L.pr n) (v : finitary (term L) n) :
  ∏ p ≠ formula.app r v.

@[simp] lemma formula.fal_ne_equal (p : formula L) (t u : term L) :
  (∏ p : formula L) ≠ (t ≃ u).

@[simp] lemma formula.fal_ne_imp (p q r : formula L) : (∏ p : formula L) ≠ (q ⟶ r).

@[simp] lemma formula.fal_ne_neg (p q : formula L) : (∏ p : formula L) ≠ ⁻q.

@[simp] lemma formula.fal_ne_ex (p q : formula L) : (∏ p : formula L) ≠ ∐ q.

@[simp] lemma formula.ex_ne_fal (p q : formula L) : (∐ p : formula L) ≠ ∏ q.

@[simp] def nfal (p : formula L) : ℕ → formula L
| 0     := p
| (n+1) := ∏ (nfal n)

notation `∏[` i `] `:90 p := nfal p i

@[simp] lemma nfal_fal (p : formula L) (i : ℕ) : nfal (∏ p : formula L) i = ∏ (nfal p i) :=
by { induction i with i IH; simp, exact IH }

@[simp] def conjunction' : ∀ n, (fin n → formula L) → formula L
| 0 _        := ⊤
| (n + 1) f  := (f ⟨n, lt_add_one n⟩) ⊓ conjunction' n (λ i, f ⟨i.val, nat.lt.step i.property⟩)

notation `⋀` binders `, ` r:(scoped p, conjunction' _ p) := r

@[simp] def disjunction' : ∀ n, (fin n → formula L) → formula L
| 0 _        := ⊥
| (n + 1) f  := (f ⟨n, lt_add_one n⟩) ⊔ disjunction' n (λ i, f ⟨i.val, nat.lt.step i.property⟩)

notation `⋁` binders `, ` r:(scoped p, disjunction' _ p) := r

def conjunction : list (formula L) → formula L
| []        := ⊤
| (p :: ps) := p ⊓ conjunction ps

notation `ı` := term.var

def slide {α : Type*} (s : ℕ → α) (a : α) (n : ℕ) : ℕ → α :=
λ x, if x < n then s x else if n < x then s (x - 1) else a
notation s `[`:1200 n ` ⇝ `:95 t `]`:0 := slide s t n

@[simp] lemma slide_eq {α : Type*} (s : ℕ → α) (a : α) (n) : s[n ⇝ a] n = a := by simp[slide]

@[simp] lemma slide_lt {α : Type*} (s : ℕ → α) (a : α) (n m) (h : m < n) : s[n ⇝ a] m = s m := by simp[slide, h]

@[simp] lemma slide_gt {α : Type*} (s : ℕ → α) (a : α) (n m) (h : n < m) : s[n ⇝ a] m = s (m - 1) :=
by {simp[slide, h], intros hh, exfalso, exact nat.lt_asymm h hh }

def concat {α : Type*} (s : ℕ → α) (a : α) : ℕ → α := s [0 ⇝ a]
notation a ` ⌢ `:90 s := concat s a

@[simp] lemma concat_0 {α : Type*} (s : ℕ → α) (a : α) : (a ⌢ s) 0 = a := rfl
@[simp] lemma concat_succ {α : Type*} (s : ℕ → α) (a : α) (n : ℕ) :
  (a ⌢ s) (n + 1) = s n := rfl

lemma slide_perm (i : ℕ) (t : term L) : ∀ n, ∃ m, ı[i ⇝ t] m = #n := λ n,
by { have C : n < i ∨ i ≤ n, exact lt_or_ge n i,
     cases C, refine ⟨n, by simp[C]⟩, 
     refine ⟨n + 1, _⟩, simp[nat.lt_succ_iff.mpr C] }

def discard {α : Type*} (s : ℕ → α) (n : ℕ) : ℕ → α :=
λ x, if x < n then s x else s (x + 1)

notation s `-{`:1200 n `}`:0 := discard s n

@[simp] lemma discard_of_lt {α : Type*} (s : ℕ → α) {m n} (h : m < n) :
 s-{n} m = s m := by simp[discard, h]

@[simp] lemma discard_of_le {α : Type*} (s : ℕ → α) {m n} (h : n ≤ m) :
 s-{n} m = s (m + 1) := by {simp[discard, h],  intros hlt, exfalso, exact nat.lt_le_antisymm hlt h }

lemma discard_0_eq_add_one {α : Type*} (s : ℕ → α) : s-{0} = λ x, s (x + 1) :=
by funext x; simp

namespace term

@[simp] def rew (s : ℕ → term L) : term L → term L
| (#x)      := s x
| (❨f❩ v) := ❨f❩ (λ i, (v i).rew)

@[reducible] def rew_var (s : ℕ → ℕ) : term L → term L := λ t, t.rew (λ x, #(s x))

@[simp] lemma constant_rew (c : L.fn 0) (s : ℕ → term L) {v : finitary (term L) 0} : (app c v).rew s = app c finitary.nil :=
by simp

@[simp] lemma unary_rew (f : L.fn 1) (s : ℕ → term L) (v : finitary (term L) 1) :
  (app f v).rew s = app f ‹(v 0).rew s› :=
by simp; ext; simp

@[simp] lemma binary_rew (f : L.fn 2) (s : ℕ → term L) (v : finitary (term L) 2) :
  (app f v).rew s = app f ‹(v 0).rew s, (v 1).rew s› :=
by simp; ext; simp

@[simp] lemma zero_rew [has_zero_symbol L] (s : ℕ → term L) : (0 : term L).rew s = 0 :=
by unfold has_zero.zero; simp

@[simp] lemma succ_rew [has_succ_symbol L] (t : term L) (s : ℕ → term L) : (Succ t : term L).rew s = Succ (t.rew s) :=
by unfold has_succ.succ; simp; ext; simp

@[simp] lemma numeral_rew [has_zero_symbol L] [has_succ_symbol L] (n : ℕ) (s : ℕ → term L) :
  (n˙ : term L).rew s = n˙ :=
by induction n; simp[*, numeral]

@[simp] lemma add_rew [has_add_symbol L] (t u : term L) (s : ℕ → term L) : (t + u : term L).rew s = t.rew s + u.rew s :=
by unfold has_add.add; simp; ext; simp

@[simp] lemma mul_rew [has_mul_symbol L] (t u : term L) (s : ℕ → term L) : (t * u : term L).rew s = t.rew s * u.rew s :=
by unfold has_mul.mul; simp; ext; simp

instance : has_pow (term L) ℕ := ⟨λ t i, t.rew (λ x, #(x + i))⟩

instance finitary_pow {n : ℕ} : has_pow (fin n → term L) ℕ := ⟨λ v m, (λ i, (v i^m))⟩

lemma pow_eq (v : term L) (i : ℕ) : v^i = v.rew (λ x, #(x + i)) := rfl

@[simp] lemma finitary_pow_app {n} (v : fin n → term L) (i : fin n) (m : ℕ) : (v^m) i = (v i)^m := rfl

@[simp] lemma var_pow (n i : ℕ) : (#n : term L)^i = #(n + i) := rfl

@[simp] lemma app_pow {n} (f : L.fn n) (v : fin n → (term L)) (i : ℕ) : (❨f❩ v)^i = ❨f❩ (v^i) := rfl

@[simp] lemma unary_pow (f : L.fn 1) (v : finitary (term L) 1) (i : ℕ) :
  (app f v)^ i = app f ‹(v 0)^i› :=
by simp[pow_eq]

@[simp] lemma binary_pow(f : L.fn 2) (v : finitary (term L) 2) (i : ℕ):
  (app f v)^i = app f ‹(v 0)^i, (v 1)^i› :=
by simp[pow_eq]

@[simp] lemma zero_pow [has_zero_symbol L] (i : ℕ) : (0 : term L)^i = 0 := by simp[pow_eq]

@[simp] lemma succ_pow [has_succ_symbol L] (t : term L) (i : ℕ) : (Succ t : term L)^i = Succ (t^i) :=
by simp[pow_eq]

@[simp] lemma numeral_pow [has_zero_symbol L] [has_succ_symbol L] (n : ℕ) (i : ℕ) :
  (n˙ : term L)^i = n˙ :=
by simp[pow_eq]

@[simp] lemma add_pow [has_add_symbol L] (t u : term L) (i : ℕ) : (t + u : term L)^i = t^i + u^i :=
by simp[pow_eq]

@[simp] lemma mul_pow [has_mul_symbol L] (t u : term L) (i : ℕ) : (t * u : term L)^i = t^i * u^i :=
by simp[pow_eq]

@[simp] lemma rew_var_inj_of_inj :
  ∀ {t u : term L} {s : ℕ → ℕ} (I : function.injective s),
  t.rew_var s = u.rew_var s ↔ t = u
| #x               #y               s I := by { simp[rew_var], exact ⟨@I x y, congr_arg (λ (x : ℕ), s x)⟩ }
| #x               (term.app f v)   s I := by simp[rew_var]
| (term.app f v)   #x               s I := by simp[rew_var]
| (term.app f₁ v₁) (term.app f₂ v₂) s I :=
    begin
      simp[rew_var], rintros rfl rfl, simp, split,
      { intros h, funext j,
        have : (v₁ j).rew_var s = (v₂ j).rew_var s,
        { have := congr_fun h j, simp at this, exact this },
        exact (@rew_var_inj_of_inj (v₁ j) (v₂ j) s I).mp this },
      { rintros rfl, simp }
    end

@[simp] lemma pow_inj : ∀ {t u : term L} {i : ℕ}, t^i = u^i ↔ t = u :=
λ t u i, by { simp[has_pow.pow], refine rew_var_inj_of_inj (λ x y, by simp) }

@[simp] lemma finitary_pow_inj {n} {v w : fin n → term L} {i : ℕ} : v^i = w^i ↔ v = w :=
⟨λ h, funext (λ j, by { have := congr_fun h j, simp at this, exact this }),
  by { rintros rfl, simp }⟩

@[simp] def arity : term L → ℕ
| (#n)    := n + 1
| (❨f❩ v) := finitary.Max 0 (λ i, (v i).arity)

@[simp] lemma constant_arity (c : L.fn 0) {v : finitary (term L) 0} : (app c v).arity = 0 :=
by simp

@[simp] lemma unary_arity (f : L.fn 1) {v : finitary (term L) 1} : (❨f❩ v).arity = (v 0).arity :=
by simp[finitary.cons, finitary.Max]

@[simp] lemma binary_arity (f : L.fn 2) (v : finitary (term L) 2) :
  (❨f❩ v).arity = max (v 0).arity (v 1).arity :=
by simp[finitary.Max, finitary.cons, fin.add']; exact max_comm _ _

@[simp] lemma zero_arity [has_zero_symbol L] : (0 : term L).arity = 0 :=
by unfold has_zero.zero; simp

@[simp] lemma succ_arity [has_succ_symbol L] (t : term L) : (Succ t : term L).arity = t.arity :=
by unfold has_succ.succ; simp

@[simp] lemma numeral_arity [has_zero_symbol L] [has_succ_symbol L] (n : ℕ) :
  (n˙ : term L).arity = 0 :=
by induction n; simp[*, numeral]

@[simp] lemma add_arity [has_add_symbol L] (t u : term L) : (t + u : term L).arity = max t.arity u.arity :=
by unfold has_add.add; simp

@[simp] lemma mul_arity [has_mul_symbol L] (t u : term L) : (t * u : term L).arity = max t.arity u.arity :=
by unfold has_mul.mul; simp

@[simp] lemma nested_rew (s₀ s₁) : ∀ (t : term L),
  (t.rew s₀).rew s₁ = t.rew (λ x, (s₀ x).rew s₁)
| (#x)       := by simp[rew]
| (❨f❩ v)  := by simp[rew, nested_rew]

@[simp] lemma rew_id (t : term L) : t.rew ı = t :=
by induction t; simp[rew]; simp*

lemma rew_rew {s₀ s₁ : ℕ → term L} : ∀ (t : term L),
  (∀ m, m < t.arity → s₀ m = s₁ m) → t.rew s₀ = t.rew s₁
| (#x)            h := by simp[rew, arity] at h ⊢; simp*
| (@app _ n f v)  h := by simp[rew, arity] at h ⊢; refine
  funext (λ i, rew_rew (v i) (λ m eqn, h m (lt_of_lt_of_le eqn (finitary.Max_le 0 (λ i, (v i).arity) i))))

lemma pow_add (t : term L) (i j : ℕ) : (t^i)^j = t^(i + j) :=
by simp[pow_eq, nested_rew, add_assoc]

@[simp] lemma arity0_rew {t : term L} (h : t.arity = 0) (s : ℕ → term L) : t.rew s = t :=
by { suffices : rew s t = rew ı t, { simp* },
     refine rew_rew _ _, simp[h] }

@[simp] lemma arity0_sf {v : term L} (h : v.arity = 0) (i : ℕ) : v^i = v := by simp[has_pow.pow, h]

lemma total_rew_inv
  (s : ℕ → term L) (h : ∀ n, ∃ m, s m = #n) : ∀ (p : term L) , ∃ q : term L, q.rew s = p
| (#x) := by rcases h x with ⟨q, h_q⟩; refine ⟨#q, _⟩; simp[h_q]
| (@app _ n f v) := by rcases classical.skolem.mp (λ i, total_rew_inv (v i)) with ⟨w, w_eqn⟩;
    refine ⟨❨f❩ w, by simp[w_eqn]⟩

@[simp] lemma pow_0 (t : term L) : t^0 = t := by simp[has_pow.pow]

@[simp] lemma sf_subst_eq (v : term L) (t : term L) (i j : ℕ) (h : j ≤ i) :
  (v^(i + 1)).rew (ı [j ⇝ t]) = v^i :=
by { simp[has_pow.pow, rew, nested_rew, h], congr, funext x,
     have : j < x + (i + 1), from nat.lt_add_left _ _ _ (nat.lt_succ_iff.mpr h),
     simp[this] }

@[simp] lemma concat_pow_eq (v : term L) (t : term L) (s : ℕ → term L) :
  (v^1).rew (t ⌢ s) = v.rew s :=
by simp[concat, rew, pow_eq, nested_rew]

def vector_vars {n} : vector (term L) n := vector.of_fn $ λ i, #i

@[simp] def symbols : term L → set (Σ n, L.fn n)
| #n        := ∅ 
| (app f v) := insert ⟨_, f⟩ (⋃ i, symbols (v i))

lemma symbols_finite : ∀ t : term L, set.finite t.symbols
| #n        := by simp
| (app f v) := set.finite.insert ⟨_, f⟩ (set.finite_Union (λ i, symbols_finite (v i)))

inductive subterm : term L → term L → Prop
| app   : ∀ {n} (f : L.fn n) (v : finitary (term L) n) (i), subterm (v i) (app f v)

@[simp] def complexity : term L → ℕ
| #n             := 0
| (@app L n f v) := (⨆ᶠ i, (v i).complexity) + 1

instance : wf_lt (term L) :=
{ prelt := subterm,
  wt := complexity,
  mono' := λ a b h, by { induction h with n f v i, simp,
  have : (v i).complexity ≤ ⨆ᶠ i, (v i).complexity, from le_fintype_sup (λ i, (v i).complexity) i,
  exact nat.lt_succ_iff.mpr this } }

@[simp] lemma not_lt_var (t : term L) (n : ℕ) : ¬t < #n := λ h,
by { rcases wf_lt.lt_iff.mp h with ⟨u, prelt, le⟩, rcases prelt }

@[simp] lemma le_var {t : term L} {n : ℕ} : t ≤ #n ↔ t = #n := by simp[le_iff_lt_or_eq]

@[simp] lemma lt_app {n} (f : L.fn n) (v : fin n → term L) (i) : v i < app f v :=
by { have : wf_lt.prelt (v i) (app f v), from subterm.app f v i,
     exact wf_lt.lt_of_prelt this }

@[simp] lemma lt_app_iff {t : term L} {n} {f : L.fn n} {v} : t < app f v ↔ ∃ i, t ≤ v i :=
⟨by { simp[wf_lt.lt_iff], rintros u prelt le, rcases prelt, refine ⟨_, le⟩ },
 by { rintros ⟨i, le⟩, refine lt_of_le_of_lt le (by simp) }⟩

@[simp] lemma le_app {n} (f : L.fn n) (v : fin n → term L) (i) : v i ≤ app f v :=
le_of_lt (lt_app f v i)

lemma symbols_ss_of_le {t u : term L} (h : t ≤ u) : t.symbols ⊆ u.symbols :=
by { induction h,
  case refl { refl },
  case of_prelt : a b prelt
  { induction prelt with n f v i, simp,
    exact set.subset.trans (show (v i).symbols ⊆ ⋃ i, (v i).symbols, from set.subset_Union _ i) (set.subset_insert _ _) },
  case trans : s t u _ _ IH_st IH_tu  { exact set.subset.trans IH_st IH_tu } } 

lemma prelt_finite (t : term L) : set.finite {u | subterm u t} :=
begin
  induction t,
  case var 
  { have : {u : term L | u.subterm #t} = ∅, { ext u, simp, intros h, rcases h },
    simp[this] },
  case app : n f v IH
  { have : {u : term L | u.subterm (❨f❩ v)} = set.range v,
    { ext u, simp, refine ⟨λ h, _, λ h, _⟩,
      { rcases h, simp }, { rcases h with ⟨i, rfl⟩, exact subterm.app f v i } },
    simp[this, set.finite_range] }  
end

lemma le_finite (t : term L) : set.finite {u | u ≤ t} :=
wf_lt.le_finite (show ∀ (a : term L), {b : term L | wf_lt.prelt b a}.finite, from prelt_finite) t

@[simp] lemma ite_pow (p : Prop) [decidable p] (t u : term L) (k : ℕ) :
  (ite p t u)^k = ite p (t^k) (u^k) :=
by by_cases C : p; simp[C]

lemma rew_inversion_or_le_of_le_rew {t u : term L} {s} (h : t ≤ u.rew s) : (∃ t' ≤ u, t = t'.rew s) ∨ (∃ n, t ≤ s n) :=
begin
  induction u,
  case var : n { simp at h, refine or.inr ⟨n, h⟩ },
  case app : n f v IH
  { rcases (eq_or_lt_of_le h) with (rfl | lt),
    { refine or.inl ⟨app f v, by refl, by refl⟩ },
    { simp at lt, rcases lt with ⟨i, le⟩,
      rcases IH i le with (⟨t', le', rfl⟩ | ⟨n, le⟩),
      { refine or.inl ⟨t', (le_trans le' (by simp)), rfl⟩ },
      { refine or.inr ⟨n, le⟩ } } }
end

end term

def rewriting_sf_itr (s : ℕ → term L) : ℕ → ℕ → term L
| 0     := s
| (n+1) := #0 ⌢ λ x, (rewriting_sf_itr n x)^1

instance : has_pow (ℕ → term L) ℕ := ⟨rewriting_sf_itr⟩

@[simp] lemma rewriting_sf_pow0 (s : ℕ → term L) : (s^0) = s := rfl
@[simp] lemma rewriting_sf_0 (s : ℕ → term L) (i : ℕ) : (s^(i + 1)) 0 = #0 := rfl
@[simp] lemma rewriting_sf_1_0 (s : ℕ → term L) (i : ℕ) : (s^1) 0 = #0 := rfl
@[simp] lemma rewriting_sf_succ (s : ℕ → term L) (n : ℕ) (i : ℕ) : (s^(i + 1)) (n + 1) = (s^i $ n)^1 :=
by simp[concat, has_pow.pow, rewriting_sf_itr]

lemma rewriting_sf_itr.pow_eq (s : ℕ → term L) (i : ℕ) : (s^(i + 1)) = #0 ⌢ λ x, (s^i $ x)^1 := rfl

lemma rewriting_sf_itr.pow_add (s : ℕ → term L) (i j : ℕ) : (s^i)^j = s^(i + j) :=
by { induction j with j IH generalizing s i, { simp },
     simp[←nat.add_one, ←add_assoc, rewriting_sf_itr.pow_eq, IH] }

@[simp] lemma rewriting_sf_itr_0 (s : ℕ → term L) : s^0 = s := rfl

lemma rewriting_sf_itr_succ (s : ℕ → term L) (n) : s^(n+1) = (s^n)^1 := rfl

lemma rewriting_sf_itr.pow_eq' (s : ℕ → term L) (i : ℕ) :
  (s^i) = (λ x, if x < i then #x else (s (x - i))^i) :=
by { induction i with i IH generalizing s, { simp },
     simp[←nat.add_one, rewriting_sf_itr.pow_eq, IH], funext x,
     cases x; simp[concat, ←nat.add_one],
     by_cases C : x < i; simp[C, term.pow_add] }

@[simp] lemma rewriting_sf_itr.pow_app_lt (s : ℕ → term L) {i : ℕ} {x : ℕ} (h : x < i) :
  (s^i $ x) = #x := by simp[rewriting_sf_itr.pow_eq', h]

@[simp] lemma rewriting_sf_itr.pow_app_ge (s : ℕ → term L) {i : ℕ} {x : ℕ} (h : i ≤ x) :
  (s^i $ x) = (s (x - i))^i :=
by {simp[rewriting_sf_itr.pow_eq'], intros lt, exfalso, exact nat.lt_le_antisymm lt h}

@[simp] lemma id_pow (i : ℕ) : (ı : ℕ → term L)^i = ı :=
by { induction i with i IH, { simp },
     { simp[rewriting_sf_itr_succ _ i, IH], funext x, cases x; simp } }

lemma id_discard_pow (k i : ℕ) : ((ı-{k})^i : ℕ → term L) = ı-{k + i} :=
begin
  funext x,
  have C : x < i ∨ i ≤ x, from lt_or_ge x i,
  cases C; simp[C],
  { have : x < k + i, from nat.lt_add_left x i k C, simp[this] },
  { have C' : x < k + i ∨ k + i ≤ x, from lt_or_ge x (k + i),
    cases C'; simp[C'],
    { have : x - i < k, from (tsub_lt_iff_right C).mpr C',
      have : x - i + i = x, from nat.sub_add_cancel C,
      simp* },
    { have : k ≤ x - i, from (le_tsub_iff_right C).mpr C', simp*, 
      calc x - i + 1 + i = 1 + (x - i + i) : by simp[add_comm (x - i) 1, add_assoc]
                     ... = 1 + x : by simp[nat.sub_add_cancel C]
                     ... = x + 1 : by simp[add_comm 1 x] } }
end

lemma rewriting_sf_perm {s : ℕ → term L} (h : ∀ n, ∃ m, s m = #n) : ∀ n, ∃ m, (s^1) m = #n :=
λ n, by { cases n, refine ⟨0, by simp⟩,
          rcases h n with ⟨m, e_m⟩, refine ⟨m+1, _⟩, simp[e_m] }

@[simp] def formula.arity : formula L → ℕ
| ⊤                 := 0
| (formula.app p v) := finitary.Max 0 (λ i, (v i).arity)
| (t ≃₁ u)          := max t.arity u.arity
| (p ⟶ q)           := max p.arity q.arity
| (⁻p)              := p.arity
| (∏ p)             := p.arity - 1

@[reducible] def sentence : formula L → Prop := λ p, p.arity = 0

@[simp] lemma formula.and_arity (p q : formula L) : (p ⊓ q).arity = max p.arity q.arity :=
by simp[has_inf.inf, formula.and]

@[simp] lemma formula.or_arity (p q : formula L) : (p ⊔ q).arity = max p.arity q.arity :=
by simp[has_sup.sup, formula.or]

@[simp] lemma formula.iff_arity (p q : formula L) : (p ⟷ q).arity = max p.arity q.arity :=
by {simp[lrarrow_def], exact le_total _ _ }

@[simp] lemma formula.bot_arity : (⊥ : formula L).arity = 0 :=
by simp[has_bot.bot]

@[simp] lemma formula.ex_arity (p : formula L) : (∐ p : formula L).arity = p.arity - 1 :=
by simp[has_exists_quantifier.ex, formula.ex]

lemma subst_pow (t : term L) (n i : ℕ) : ı[n ⇝ t]^i = ı[n + i ⇝ t^i] :=
begin
  induction i with i IH, { simp }, funext x,
  cases x; simp[←nat.add_one, ←add_assoc, IH],
  { have T : x < n + i ∨ x = n + i ∨ n + i < x, exact trichotomous _ _,
    cases T, { simp[T], }, cases T; simp[T, pow_add, term.pow_add],
    { have : 0 < x, exact pos_of_gt T, exact (nat.pos_succ this).symm} }
end

lemma term.pow_rew_distrib (t : term L) (s : ℕ → term L) (i : ℕ): (t.rew s)^i = (t^i).rew (s^i) :=
by { induction i with i IH generalizong s i, { simp, },
     { simp[←nat.add_one, term.pow_add, rewriting_sf_itr.pow_add, rewriting_sf_itr.pow_eq',
         IH, term.pow_eq, term.nested_rew] } }

@[simp] lemma rew_subst_id : (λ x, (((λ x, #(x + 1)) ^ 1) x).rew ı[0 ⇝ #0]  : ℕ → term L) = ı :=
by { funext x, cases x; simp }

@[simp] lemma rew_slide_eq_concat (s : ℕ → term L) (t : term L) :
  (λ x, ((s^1) x).rew ı[0 ⇝ t]) = t ⌢ s :=
funext (λ y, by cases y; simp)

@[simp] lemma concat_eq_id :
  (#0 ⌢ (λ x, #(x + 1)) : ℕ → term L) = ı :=
funext (λ x, by cases x; simp)

namespace formula

@[simp] lemma constant_arity (c : L.pr 0) {v : finitary (term L) 0} : (❴c❵ v).arity = 0 :=
by simp

@[simp] lemma unary_arity (p : L.pr 1) (v : finitary (term L) 1) : (❴p❵ v).arity = (v 0).arity :=
by simp[finitary.cons, finitary.Max]

@[simp] lemma binary_arity (p : L.pr 2) (v : finitary (term L) 2) :
  (❴p❵ v).arity = max (v 0).arity (v 1).arity :=
by simp[finitary.Max, finitary.cons, fin.add']; exact max_comm _ _

@[simp] lemma le_arity [has_le_symbol L] (t u : term L) : (t ≼ u : formula L).arity = max t.arity u.arity :=
by unfold has_preceq.preceq; simp

@[simp] lemma mem_arity [has_mem_symbol L] (t u : term L) : (t ∊ u : formula L).arity = max t.arity u.arity :=
by unfold has_elem.elem; simp

@[simp] def rew : (ℕ → term L) → formula L → formula L
| s ⊤         := ⊤
| s (app p v) := app p (λ i, (v i).rew s)
| s (t ≃₁ u)  := (t.rew s) ≃ (u.rew s)
| s (p ⟶ q)  := p.rew s ⟶ q.rew s
| s (⁻p)      := ⁻(p.rew s)
| s (∏ p)   := ∏ (p.rew (s^1))

@[reducible] def rew_var (s : ℕ → ℕ) : formula L → formula L := λ p, p.rew (λ x, #(s x))

@[simp] lemma constant_rew (p : L.pr 0) (s : ℕ → term L) {v : finitary (term L) 0} :
  (❴p❵ v).rew s = ❴p❵ finitary.nil :=
by simp

@[simp] lemma unary_rew (p : L.pr 1) (s : ℕ → term L) (v : finitary (term L) 1) : (❴p❵ v).rew s = ❴p❵ ‹(v 0).rew s› :=
by simp; ext; simp

@[simp] lemma binary_rew (p : L.pr 2) (s : ℕ → term L) (v : finitary (term L) 2) :
  (❴p❵ v).rew s = ❴p❵ ‹(v 0).rew s, (v 1).rew s› :=
by simp; ext; simp

@[simp] lemma le_rew [has_le_symbol L] (t u : term L) (s : ℕ → term L) :
  (t ≼ u : formula L).rew s = (t.rew s ≼ u.rew s) :=
by unfold has_preceq.preceq; simp

@[simp] lemma mem_rew [has_mem_symbol L] (t u : term L) (s : ℕ → term L) :
  (t ∊ u : formula L).rew s = (t.rew s ∊ u.rew s) :=
by unfold has_elem.elem; simp

@[simp] lemma and_rew (p q : formula L) (s) : (p ⊓ q).rew s = p.rew s ⊓ q.rew s := by simp[has_inf.inf, and, formula.rew]
@[simp] lemma or_rew (p q : formula L) (s) : (p ⊔ q).rew s = p.rew s ⊔ q.rew s := by simp[has_sup.sup, or, formula.rew]
@[simp] lemma iff_rew (p q : formula L) (s) : (p ⟷ q).rew s = p.rew s ⟷ q.rew s := by simp[lrarrow_def, formula.rew]
@[simp] lemma nfal_rew (p : formula L) (i : ℕ) (s) : (nfal p i).rew s = nfal (p.rew (s^i)) i :=
by { induction i with i IH generalizing s, { simp },
     simp[←nat.add_one, IH, rewriting_sf_itr.pow_add, add_comm 1 i] }
@[simp] lemma ex_rew (p : formula L) (s) : (∐ p).rew s = ∐ p.rew (s^1) :=by simp[has_exists_quantifier.ex, ex]
@[simp] lemma bot_rew (s) : (⊥ : formula L).rew s = ⊥ := by simp[has_bot.bot]

@[simp] lemma rew_id (p : formula L) : p.rew ı = p :=
by { induction p; try { simp[rew] }; try {simp*} }

@[simp] lemma conjunction'_rew {n} (P : finitary (formula L) n) (s) :
  (conjunction' n P).rew s = conjunction' n (λ i, (P i).rew s) :=
by { induction n with n IH; simp* }

@[simp] lemma disjunction'_rew {n} (P : finitary (formula L) n) (s) :
  (disjunction' n P).rew s = disjunction' n (λ i, (P i).rew s) :=
by { induction n with n IH; simp* }

instance : has_pow (formula L) ℕ := ⟨λ p i, p.rew (λ x, #(x + i))⟩

lemma pow_eq (p : formula L) (i : ℕ) : p^i = p.rew (λ x, #(x + i)) := rfl

@[simp] lemma formula_pow_0 (p : formula L) : p^0 = p := by simp[has_pow.pow]

@[simp] lemma app_pow {n} (p : L.pr n) (v : finitary (term L) n) (i : ℕ) : (❴p❵ v)^i = ❴p❵ (v^i) := rfl

@[simp] lemma constant_pow (c : L.pr 0) (i : ℕ) {v : finitary (term L) 0} : (app c v)^i = app c finitary.nil :=
by simp

@[simp] lemma unary_pow (p : L.pr 1) (i : ℕ) (t : term L) : (❴p❵ ‹t›)^i = ❴p❵ ‹t^i› :=
by simp[pow_eq]; refl

@[simp] lemma binary_pow (p : L.pr 2) (i : ℕ) (t₁ t₂ : term L) :
  (❴p❵ ‹t₁, t₂›)^i = ❴p❵ ‹t₁^i, t₂^i› :=
by simp[pow_eq]; refl

@[simp] lemma le_pow [has_le_symbol L] (t u : term L) (i : ℕ) :
  (t ≼ u : formula L)^i = (t^i ≼ u^i) :=
by simp[pow_eq]; refl

@[simp] lemma mem_pow [has_mem_symbol L] (t u : term L) (i : ℕ) :
  (t ∊ u : formula L)^i = (t^i ∊ u^i) :=
by simp[pow_eq]; refl

@[simp] lemma eq_pow (t u : term L) (i : ℕ) : (t ≃₁ u)^i = (t^i ≃ u^i) := rfl
@[simp] lemma imply_pow (p q : formula L) (i : ℕ) : (p ⟶ q)^i = p^i ⟶ q^i := rfl
@[simp] lemma neg_pow (p : formula L) (i : ℕ) : (⁻p)^i = ⁻(p^i) := rfl
@[simp] lemma and_pow (p q : formula L) (i : ℕ) : (p ⊓ q)^i = (p^i) ⊓ (q^i) := rfl
@[simp] lemma or_pow (p q : formula L) (i : ℕ) : (p ⊔ q)^i = (p^i) ⊔ (q^i) := rfl
@[simp] lemma top_pow (i : ℕ) : (⊤ : formula L)^i = ⊤ := by refl
@[simp] lemma bot_pow (i : ℕ) : (⊥ : formula L)^i = ⊥ := by refl

lemma fal_pow (p : formula L) (i : ℕ) : (∏ p)^i = ∏ p.rew (#0 ⌢ λ x, #(x + i + 1)) :=
by simp[formula.pow_eq, rewriting_sf_itr.pow_eq]

lemma fal_pow_discard (p : formula L) : (∏ p)^1 = ∏ p.rew ı-{1} :=
by { simp[formula.pow_eq, rewriting_sf_itr.pow_eq, discard], congr, funext x, cases x; simp }

lemma ex_pow_discard (p : formula L) : (∐ p)^1 = ∐ p.rew ı-{1} :=
by { simp[formula.pow_eq, rewriting_sf_itr.pow_eq, discard], congr, funext x, cases x; simp }

lemma nfal_pow (p : formula L) (n i : ℕ) :
  (nfal p n)^i = nfal (p.rew (λ x, if x < n then #x else #(x + i))) n :=
by { simp[formula.pow_eq, rewriting_sf_itr.pow_eq'], congr, funext x,
     by_cases C : x < n; simp[C], omega }

lemma nested_rew : ∀ (p : formula L) (s₀ s₁),
  (p.rew s₀).rew s₁ = p.rew (λ x, (s₀ x).rew s₁)
| ⊤         _ _ := by simp
| (❴p❵ v) _ _ := by simp[rew]
| (t ≃₁ u)  _ _ := by simp[rew]
| (p ⟶ q)   _ _ := by simp[rew, nested_rew p, nested_rew q]
| (⁻p)      _ _ := by simp[rew]; refine nested_rew p _ _
| (∏ p)     _ _ := by { simp[rew, nested_rew p], congr,
    funext n, cases n; simp, simp[concat, rewriting_sf_itr.pow_eq, term.pow_eq] }

lemma rew_rew : ∀ (p : formula L) {s₀ s₁ : ℕ → term L},
  (∀ m, m < p.arity → s₀ m = s₁ m) → p.rew s₀ = p.rew s₁
| ⊤         _ _ _ := by simp
| (❴p❵ v) _ _ h := by simp[rew, arity] at h ⊢; refine funext
    (λ i, term.rew_rew (v i) (λ m eqn, h _ $ lt_of_lt_of_le eqn (finitary.Max_le 0 _ i)))
| (t ≃₁ u)  _ _ h := by simp[rew, arity] at h ⊢;
    { refine ⟨term.rew_rew _ (λ _ e, h _ (or.inl e)), term.rew_rew _ (λ _ e, h _ (or.inr e))⟩ }
| (p ⟶ q)   _ _ h := by simp[rew, arity] at h ⊢;
    refine ⟨rew_rew _ (λ _ e, h _ (or.inl e)), rew_rew _ (λ _ e, h _ (or.inr e))⟩
| (⁻p)      _ _ h := by simp[rew, arity] at h ⊢; refine rew_rew _ h
| (∏ p)     _ _ h := by { simp[rew, arity] at h ⊢,
    refine rew_rew _ (λ m e, _), cases m; simp,
    cases p.arity, { exfalso, simp* at* },
    { simp at h, simp[h _ (nat.succ_lt_succ_iff.mp e)] } }

lemma pow_add (p : formula L) (i j : ℕ) : (p^i)^j = p^(i + j) :=
by simp[pow_eq, nested_rew, add_assoc]

@[simp] lemma sentence_rew {p : formula L} (h : sentence p) (s : ℕ → term L) : p.rew s = p :=
by { suffices : rew s p = rew ı p, { simp* },
     refine rew_rew _ _, simp[show p.arity = 0, from h] }

@[simp] lemma sentence_sf {p : formula L} (h : sentence p) (i : ℕ) : p^i = p :=
by simp[has_pow.pow, sentence_rew h]

@[simp] lemma sf_subst_eq (p : formula L) (t : term L) (i j : ℕ) (h : j ≤ i) : (p^(i + 1)).rew ı[j ⇝ t] = p^i :=
by { simp[has_pow.pow, nested_rew, h], congr, funext x,
     have : j < x + (i + 1), from nat.lt_add_left _ _ _ (nat.lt_succ_iff.mpr h),
     simp[this] }

lemma subst_sf_rew (p : formula L) (t : term L) (s : ℕ → term L) :
  (p.rew ı[0 ⇝ t]).rew s = (p.rew (s^1)).rew ı[0 ⇝ t.rew s] :=
by { simp[formula.rew, nested_rew], congr, ext n, cases n; simp }

@[simp] lemma sf_subst_eq_0 (p : formula L) (t) : (p^1).rew ı[0 ⇝ t] = p :=
by simp[nested_rew]

lemma pow_rew_distrib  (p : formula L) (s : ℕ → term L) (i : ℕ): (p.rew s)^i = (p^i).rew (s^i) :=
by { induction i with i IH generalizong s i, { simp },
     { simp[←nat.add_one, ←pow_add, ←rewriting_sf_itr.pow_add, IH, formula.pow_eq _ 1, nested_rew],
       refl } }

lemma total_rew_inv :
  ∀ (s : ℕ → term L) (h : ∀ n, ∃ m, s m = #n) (p : formula L), ∃ q : formula L, q.rew s = p
| _ _ ⊤              := ⟨⊤, by simp⟩
| s h (@app _ n p v) := by rcases classical.skolem.mp (λ i : fin n, @term.total_rew_inv _ s h (v i : term L)) with ⟨w, w_p⟩;
    refine ⟨❴p❵ w, by simp[w_p]⟩
| s h (t ≃₁ u)       := 
    by rcases term.total_rew_inv s h t with ⟨w₁, e_w₁⟩;
       rcases term.total_rew_inv s h u with ⟨w₂, e_w₂⟩; refine ⟨w₁ ≃ w₂, by simp[e_w₁, e_w₂]⟩
| s h (p ⟶ q)        := 
    by rcases total_rew_inv s h p with ⟨p', e_p'⟩;
       rcases total_rew_inv s h q with ⟨q', e_q'⟩; refine ⟨p' ⟶ q', by simp*⟩
| s h (⁻p)           := by rcases total_rew_inv s h p with ⟨q, e_q⟩; refine ⟨⁻q, by simp*⟩
| s h (∏ p)          := by rcases total_rew_inv _ (rewriting_sf_perm h) p with ⟨q, e_q⟩; refine ⟨∏q, by simp[e_q]⟩

@[simp] lemma rew_var_inj_of_inj :
  ∀ {p q : formula L} {s : ℕ → ℕ} (I : function.injective s),
  p.rew_var s = q.rew_var s ↔ p = q
| ⊤                   p                   s I := by {cases p; simp[rew_var], }
| (formula.app p v)   ⊤                   s I := by simp[rew_var]
| (formula.app p₁ v₁) (formula.app p₂ v₂) s I := by { simp[rew_var], rintros rfl rfl,
    simp, split,
    { intros h, funext i,
      have : term.rew_var s (v₁ i) = term.rew_var s (v₂ i), from congr_fun h i,
      exact (term.rew_var_inj_of_inj I).mp this },
    { rintros rfl, simp } }
| (formula.app p v)   (t ≃₁ u)            s I := by simp[rew_var]
| (formula.app r v)   (p ⟶ q)             s I := by simp[rew_var]
| (formula.app r v)   (⁻p)                s I := by simp[rew_var]
| (formula.app r v)   (∏ p)               s I := by simp[rew_var, fal_pow]
| (t ≃₁ u)            p                   s I := by cases p; simp[rew_var, fal_pow, I]
| (p ⟶ q)             r                   s I :=
    by cases r; simp[rew_var, fal_pow, @rew_var_inj_of_inj p _ s I, @rew_var_inj_of_inj q _ s I]
| (⁻p)                q                   s I :=
    by cases q; simp[rew_var, fal_pow, @rew_var_inj_of_inj p _ s I]
| (∏ p)               ⊤                   s I := by simp[rew_var]
| (∏ p)               (formula.app r v)   s I := by simp[rew_var]
| (∏ p)               (t ≃₁ u)            s I := by simp[rew_var]
| (∏ p)               (q ⟶ r)             s I := by simp[rew_var]
| (∏ p)               (⁻q)                s I := by simp[rew_var]
| (∏ p)               (∏ q)               s I := by {simp[rew_var, fal_pow], 
    have : ∀ p : formula L, p.rew ((λ x, #(s x))^1) = p.rew_var (λ x, if x = 0 then 0 else s (x - 1) + 1),
    { intros p, simp[rewriting_sf_itr.pow_eq', rew_var, nested_rew], congr, funext x, cases x; simp },
    
    have I' : function.injective (λ x, if x = 0 then 0 else s (x - 1) + 1),
    { intros x y, cases x; cases y; simp,
      { intros h, exfalso, exact (nat.succ_ne_zero _).symm h }, { exact (@I x y) } },
    simp[this, @rew_var_inj_of_inj p q _ I'] }
  
@[simp] lemma pow_inj : ∀ {p q : formula L} {i : ℕ}, p^i = q^i ↔ p = q :=
λ p q i, by { simp[has_pow.pow], refine rew_var_inj_of_inj (λ x y, by simp) }

@[simp] def is_open : formula L → bool
| ⊤          := tt
| (❴p❵ v)  := tt
| (t ≃₁ u)   := tt
| (p ⟶ q)    := p.is_open && q.is_open
| (⁻p)       := p.is_open
| (∏ p)      := ff

@[simp] lemma op.and (p q : formula L) : (p ⊓ q).is_open = p.is_open && q.is_open := rfl

@[simp] lemma op.or (p q : formula L) : (p ⊔ q).is_open = p.is_open && q.is_open := rfl

@[simp] def is_open_rew : ∀ {p : formula L} {s}, (p.rew s).is_open ↔ p.is_open
| ⊤        s := by simp
| (❴p❵ v)  s := by simp
| (t ≃₁ u) s := by simp
| (p ⟶ q) s  := by simp[@is_open_rew p s, @is_open_rew q s]
| (⁻p)     s := by simp[@is_open_rew p s]
| (∏ p)  s   := by simp

@[simp] def is_open_pow : ∀ {p : formula L} {i : ℕ}, (p^i).is_open ↔ p.is_open :=
by simp[pow_eq]

@[simp] lemma nfal_arity : ∀ (n) (p : formula L), (nfal p n).arity = p.arity - n
| 0     p := by simp[formula.arity]
| (n+1) p := by {simp[formula.arity, nfal_arity n], exact (arity p).sub_sub _ _ }

lemma nfal_sentence (p : formula L) : sentence (nfal p p.arity) :=
by simp[sentence]

@[simp] lemma conjunction_arity {n} {v : finitary (formula L) n} :
  (conjunction' n v).arity = finitary.Max 0 (λ i, (v i).arity) :=
by { induction n with n IH; simp[finitary.Max, fin.add'], simp[IH] }

def fal_complete (p : formula L) := ∏[p.arity] p

prefix `∏* `:64 := fal_complete

lemma fal_complete_sentence (p : formula L) : sentence (∏* p) :=
by simp[sentence, fal_complete]

@[simp] def fn_symbols : formula L → set (Σ n, L.fn n)
| ⊤         := ∅
| (app r v) := ⋃ i, (v i).symbols
| (t ≃₁ u)  := t.symbols ∪ u.symbols
| (p ⟶ q)   := fn_symbols p ∪ q.fn_symbols
| (⁻p)      := p.fn_symbols
| (∏ p)     := p.fn_symbols

def fn_symbols' (p : formula L) (n : ℕ) : set (L.fn n) := {f | (⟨n, f⟩ : Σ n, L.fn n) ∈ p.fn_symbols }

lemma mem_fn_symbols'_iff {n : ℕ} {f : L.fn n} {p : formula L} :
  f ∈ p.fn_symbols' n ↔ (⟨n, f⟩ : Σ n, L.fn n) ∈ p.fn_symbols :=
by simp[fn_symbols']

@[simp] def pr_symbols : formula L → set (Σ n, L.pr n)
| ⊤         := ∅
| (app r v) := {⟨_, r⟩}
| (t ≃₁ u)  := ∅
| (p ⟶ q)   := p.pr_symbols ∪ q.pr_symbols
| (⁻p)      := p.pr_symbols
| (∏ p)     := p.pr_symbols

def pr_symbols' (p : formula L) (n : ℕ) : set (L.pr n) := {r | (⟨n, r⟩ : Σ n, L.pr n) ∈ p.pr_symbols }

lemma mem_pr_symbols'_iff {n : ℕ} {r : L.pr n} {p : formula L} :
  r ∈ p.pr_symbols' n ↔ (⟨n, r⟩ : Σ n, L.pr n) ∈ p.pr_symbols :=
by simp[pr_symbols']

lemma fn_symbols_finite : ∀ p : formula L, p.fn_symbols.finite
| ⊤         := by simp
| (app r v) := set.finite_Union (λ i, (v i).symbols_finite)
| (t ≃₁ u)  := set.finite.union t.symbols_finite u.symbols_finite
| (p ⟶ q)   := set.finite.union p.fn_symbols_finite q.fn_symbols_finite
| (⁻p)      := p.fn_symbols_finite
| (∏ p)     := p.fn_symbols_finite

lemma fn_symbols'_finite (p : formula L) (n : ℕ) : (p.fn_symbols' n).finite :=
by { have : p.fn_symbols' n = (λ f : L.fn n, (⟨n, f⟩ : Σ n, L.fn n))⁻¹' p.fn_symbols, { refl },
     rw this, refine set.finite.preimage (λ f, by simp) p.fn_symbols_finite  }

lemma pr_symbols_finite : ∀ p : formula L, p.pr_symbols.finite
| ⊤         := by simp
| (app r v) := by simp
| (t ≃₁ u)  := by simp
| (p ⟶ q)   := set.finite.union p.pr_symbols_finite q.pr_symbols_finite
| (⁻p)      := p.pr_symbols_finite
| (∏ p)     := p.pr_symbols_finite

lemma pr_symbols'_finite (p : formula L) (n : ℕ) : (p.pr_symbols' n).finite :=
by { have : p.pr_symbols' n = (λ r : L.pr n, (⟨n, r⟩ : Σ n, L.pr n))⁻¹' p.pr_symbols, { refl },
     rw this, refine set.finite.preimage (λ r, by simp) p.pr_symbols_finite  }

inductive subformula : formula L → formula L → Prop
| neg    : ∀ {p}, subformula p (⁻p)
| implyl : ∀ {p q}, subformula p (p ⟶ q)
| implyr : ∀ {p q}, subformula q (p ⟶ q)
| fal    : ∀ {p}, subformula p (∏ p)

@[simp] def complexity : formula L → ℕ
| ⊤         := 0
| (app r v) := 0
| (t ≃₁ u)  := 0
| (⁻p)      := p.complexity + 1
| (p ⟶ q)  := max p.complexity q.complexity + 1
| (∏ p)     := p.complexity + 1

instance : wf_lt (formula L) :=
{ prelt := subformula,
  wt := complexity,
  mono' := λ a b h, by { induction h; try { simp },
  case implyl : p q { exact nat.lt_succ_iff.mpr (le_max_left p.complexity q.complexity) },
  case implyr : p q { exact nat.lt_succ_iff.mpr (le_max_right p.complexity q.complexity) } } }

@[simp] lemma lt_app {p : formula L} {n} {r : L.pr n} {v} : ¬p < app r v :=
by { simp [wf_lt.lt_iff], intros p h, rcases h }

@[simp] lemma le_app {p : formula L} {n} {r : L.pr n} {v} : p ≤ app r v ↔ p = app r v := by simp[le_iff_lt_or_eq]

@[simp] lemma lt_equal {p : formula L} {t u : term L} : ¬p < t ≃₁ u :=
by { simp [wf_lt.lt_iff], intros p h, rcases h }

@[simp] lemma le_equal {p : formula L} {t u : term L} : p ≤ t ≃₁ u ↔ p = t ≃₁ u := by simp[le_iff_lt_or_eq]

@[simp] lemma lt_verum {p : formula L} : ¬p < ⊤ :=
by { simp [wf_lt.lt_iff], intros p h, rcases h }

@[simp] lemma le_verum {p : formula L} : p ≤ ⊤ ↔ p = ⊤ := by simp[le_iff_lt_or_eq]

@[simp] lemma lt_imply {p q r : formula L} :
  p < q ⟶ r ↔ p ≤ q ∨ p ≤ r :=
begin
  simp [wf_lt.lt_iff], split,
  { rintros ⟨p', h, le⟩, rcases h, { exact or.inl le }, { exact or.inr le } },
  rintros (le | le),
  { refine ⟨q, subformula.implyl, le⟩ }, { refine ⟨r, subformula.implyr, le⟩ }
end

@[simp] lemma lt_neg {p q : formula L} :
  p < ⁻q ↔ p ≤ q :=
begin
  simp [wf_lt.lt_iff], split,
  { rintros ⟨p', h, le⟩, rcases h, exact le },
  rintros le,
  { refine ⟨q, subformula.neg, le⟩ }
end

@[simp] lemma lt_fal {p q : formula L} :
  p < ∏ q ↔ p ≤ q :=
begin
  simp [wf_lt.lt_iff], split,
  { rintros ⟨p', h, le⟩, rcases h, exact le },
  rintros le,
  { refine ⟨q, subformula.fal, le⟩ }
end

lemma rew_inversion_of_le_rew {p q : formula L} {s} (le : p ≤ q.rew s) : ∃ (p' ≤ q) (k : ℕ), p = p'.rew (s^k) :=
begin
  induction q generalizing p s; try { simp* },
  case app : n r v { simp at le, rcases le with rfl, refine ⟨0, by simp⟩ },
  case equal : t u { simp at le, rcases le with rfl, refine ⟨0, by simp⟩ },
  case verum { simp at le, exact le },
  case imply : q₁ q₂ IH₁ IH₂
  { rcases le_iff_lt_or_eq.mp le with (lt | rfl),
    { simp at lt, rcases lt with (le | le),
      { rcases IH₁ le with ⟨p', le_p', k, rfl⟩, refine ⟨p', le_trans le_p' (le_of_lt (by simp)), k, by refl⟩ },
      { rcases IH₂ le with ⟨p', le_p', k, rfl⟩, refine ⟨p', le_trans le_p' (le_of_lt (by simp)), k, by refl⟩ } },
    { refine ⟨q₁ ⟶ q₂, by simp, 0, by simp⟩ } },
  case neg : q IH
  { rcases le_iff_lt_or_eq.mp le with (lt | rfl),
    { simp at lt, rcases IH lt with ⟨p', le_p', k, rfl⟩, refine ⟨p', le_trans le_p' (le_of_lt (by simp)), k, by refl⟩ },
    { refine ⟨⁻q, by refl, 0, by refl⟩ } },
  case fal : q IH
  { rcases le_iff_lt_or_eq.mp le with (lt | rfl),
    { simp at lt, rcases IH lt with ⟨p', le_p', k, rfl⟩, 
      refine ⟨p', le_trans le_p' (le_of_lt (by simp)), k + 1, by simp[rewriting_sf_itr.pow_add, add_comm 1]⟩ },
    { refine ⟨∏ q, by refl, 0, by simp⟩ } }
end

lemma fn_symbols_ss_of_le {p q : formula L} (h : p ≤ q) : p.fn_symbols ⊆ q.fn_symbols :=
by { induction h; try { simp },
     case refl { refl },
     case trans : p q r _ _ IH_pq IH_qr { exact set.subset.trans IH_pq IH_qr },
     case of_prelt : p q prelt { induction prelt; try { simp } } }

lemma pr_symbols_ss_of_le {p q : formula L} (h : p ≤ q) : p.pr_symbols ⊆ q.pr_symbols :=
by { induction h; try { simp },
     case refl { refl },
     case trans : p q r _ _ IH_pq IH_qr { exact set.subset.trans IH_pq IH_qr },
     case of_prelt : p q prelt { induction prelt; try { simp } } }

inductive subterm : term L → formula L → Prop
| app    : ∀ {n} (r : L.pr n) (v : finitary (term L) n) (i), subterm (v i) (app r v)
| equall : ∀ {t u : term L}, subterm t (t ≃₁ u)
| equalr : ∀ {t u : term L}, subterm u (t ≃₁ u)

instance : has_mem (term L) (formula L) := ⟨λ t p, ∃ (t' ≥ t) (p' ≤ p), subterm t' p'⟩

lemma mem_def {t : term L} {p : formula L} : t ∈ p ↔ ∃ (t' ≥ t) (p' ≤ p), subterm t' p' := by refl

@[simp] lemma mem_equall (t u : term L) : t ∈ (t ≃₁ u) := ⟨t, by simp, t ≃₁ u, by simp, subterm.equall⟩ 

@[simp] lemma mem_equalr (t u : term L) : u ∈ (t ≃₁ u) := ⟨u, by simp, t ≃₁ u, by simp, subterm.equalr⟩ 

lemma mem_of_formula_le_mem {t : term L} {p q : formula L} : t ∈ p → p ≤ q → t ∈ q :=
by { rintros ⟨t', ht', p', hp', sb⟩ le, refine ⟨t', ht', p', (le_trans hp' le), sb⟩ }

lemma mem_of_term_le_mem {t u : term L} {p : formula L} : u ∈ p → t ≤ u → t ∈ p :=
by { rintros ⟨t', ht', p', hp', sb⟩ le, refine ⟨t', le_trans le ht', p', hp', sb⟩ }

@[simp] lemma mem_app {t : term L} {n} {r : L.pr n} {v : finitary (term L) n} :
  t ∈ app r v ↔ ∃ i, t ≤ v i :=
⟨by { rintros ⟨t', ht', p', hp', sb⟩,
      have hp' : p' = app r v ∨ p' < app r v, exact eq_or_lt_of_le hp', simp at hp',
      rcases hp' with rfl, cases sb with i, refine ⟨_, ht'⟩ },
 by { rintros ⟨i, le⟩, refine mem_of_term_le_mem ⟨v i, by simp, app r v, by simp, subterm.app r v i⟩ le }⟩

@[simp] lemma mem_equal {s t u : term L} :
  s ∈ t ≃₁ u ↔ s ≤ t ∨ s ≤ u :=
⟨by { rintros ⟨t', ht', p', hp', sb⟩,
      have hp' : p' = t ≃₁ u ∨ p' <t ≃₁ u, exact eq_or_lt_of_le hp', simp at hp',
      rcases hp' with rfl, cases sb, { exact or.inl ht' }, { exact or.inr ht' } },
 by { rintros (le | le),
      { refine mem_of_term_le_mem ⟨t, by simp, t ≃₁ u, by simp, subterm.equall⟩ le },
      { refine mem_of_term_le_mem ⟨u, by simp, t ≃₁ u, by simp, subterm.equalr⟩ le } }⟩

@[simp] lemma mem_verum {t : term L} :
  ¬t ∈ (⊤ : formula L) :=
by { rintros ⟨t', ht', p', hp', sb⟩, 
      have hp' : p' = ⊤ ∨ p' < ⊤, exact eq_or_lt_of_le hp', simp at hp',
      rcases hp' with rfl, rcases sb }

@[simp] lemma mem_imply {t : term L} {p q : formula L} :
  t ∈ p ⟶ q ↔ t ∈ p ∨ t ∈ q :=
⟨by { rintros ⟨t', ht', p', hp', sb⟩, 
      have hp' : p' = p ⟶ q ∨ p' < p ⟶ q, exact eq_or_lt_of_le hp', simp at hp',
      rcases hp' with (rfl | (hp' | hp')),
      { rcases sb }, { refine or.inl ⟨t', ht', p', hp', sb⟩ }, { refine or.inr ⟨t', ht', p', hp', sb⟩ }  },
 by { rintros (h | h); refine mem_of_formula_le_mem h (le_of_lt (by simp)) }⟩

@[simp] lemma mem_neg {t : term L} {p : formula L} :
  t ∈ ⁻p ↔ t ∈ p :=
⟨by { rintros ⟨t', ht', p', hp', sb⟩, 
      have hp' : p' = ⁻p ∨ p' < ⁻p, exact eq_or_lt_of_le hp', simp at hp',
      rcases hp' with (rfl | hp'),
      { rcases sb }, { refine ⟨t', ht', p', hp', sb⟩ }  },
 by { rintros h, refine mem_of_formula_le_mem h (le_of_lt (by simp)) }⟩

@[simp] lemma mem_fal {t : term L} {p : formula L} :
  t ∈ ∏ p ↔ t ∈ p :=
⟨by { rintros ⟨t', ht', p', hp', sb⟩, 
      have hp' : p' = ∏ p ∨ p' < ∏ p, exact eq_or_lt_of_le hp', simp at hp',
      rcases hp' with (rfl | hp'),
      { rcases sb }, { refine ⟨t', ht', p', hp', sb⟩ }  },
 by { rintros h, refine mem_of_formula_le_mem h (le_of_lt (by simp)) }⟩

@[simp] lemma mem_ex {t : term L} {p : formula L} :
  t ∈ ∐ p ↔ t ∈ p := by simp[ex_eq]

lemma rew_inversion_or_le_of_mem_rew {t : term L} {p : formula L} {s} (mem : t ∈ p.rew s) :
 (∃ (t' : term L) (mem : t' ∈ p) (k : ℕ), t = t'.rew (s^k)) ∨ (∃ (k n : ℕ), t ≤ (s^k) n) :=
begin
  induction p generalizing t s,
  case app : n r v
  { simp at mem, rcases mem with ⟨i, le⟩,
    rcases term.rew_inversion_or_le_of_le_rew le with (⟨t', le_t', rfl⟩ | h),
    { refine or.inl ⟨t', by { simp; exact ⟨i, le_t'⟩ }, 0, rfl⟩ },
    { exact or.inr ⟨0, h⟩ } },
  case equal : u₁ u₂
  { simp at mem, rcases mem with (le | le),
    { rcases term.rew_inversion_or_le_of_le_rew le with (⟨t', le_t', rfl⟩ | h),
      { refine or.inl ⟨t', by simp[le_t'], 0, rfl⟩ },
      { exact or.inr ⟨0, h⟩ } },
    { rcases term.rew_inversion_or_le_of_le_rew le with (⟨t', le_t', rfl⟩ | h),
      { refine or.inl ⟨t', by simp[le_t'], 0, rfl⟩ },
      { exact or.inr ⟨0, h⟩ } } },
  case verum { simp at mem, contradiction },
  case imply : p q IH_p IH_q
  { simp at mem, rcases mem with (mem | mem),
    { rcases IH_p mem with (⟨t', mem', k, rfl⟩ | h),
      { refine or.inl ⟨t', by simp[mem'], k, rfl⟩ }, { exact or.inr h } },
    { rcases IH_q mem with (⟨t', mem', k, rfl⟩ | h),
      { refine or.inl ⟨t', by simp[mem'], k, rfl⟩ }, { exact or.inr h } } },
  case neg : p IH
  { simp at mem,
    { rcases IH mem with (⟨t', mem', k, rfl⟩ | h),
      { refine or.inl ⟨t', by simp[mem'], k, rfl⟩ }, { exact or.inr h } }, },
  case fal : p IH
  { simp at mem, rcases IH mem with (⟨t', mem', k, rfl⟩ | h),
    { refine or.inl ⟨t', by simp[mem'], k + 1, by simp[rewriting_sf_itr.pow_add, add_comm 1]⟩ },
    { rcases h with ⟨k, h⟩, simp[rewriting_sf_itr.pow_add, add_comm 1] at h,
      refine or.inr ⟨k+1, h⟩ } }
end

lemma fn_symbols_ss_of_mem {t : term L} {p : formula L} (h : t ∈ p) : t.symbols ⊆ p.fn_symbols :=
begin
  have ss : ∀ {t : term L} {p : formula L}, subterm t p → t.symbols ⊆ p.fn_symbols,
  { intros t p sub, induction sub; try { simp },
    case app : n r v i { refine set.subset_Union _ i } },
  rcases h with ⟨t', le_t, p', le_p, sub⟩,
  have t_ss_t' : t.symbols ⊆ t'.symbols, from term.symbols_ss_of_le le_t,
  have p'_ss_p : p'.fn_symbols ⊆ p.fn_symbols, from fn_symbols_ss_of_le le_p,
  exact set.subset.trans (set.subset.trans t_ss_t' (ss sub)) p'_ss_p
end

lemma prelt_finite (p : formula L) : set.finite {q | subformula q p} :=
begin
  induction p,
  case verum { have : {q : formula L | q.subformula ⊤} = ∅, { ext q, simp, intros h, rcases h }, simp[this] },
  case app : n r v { have : {q : formula L | q.subformula (app r v)} = ∅, { ext q, simp, intros h, rcases h }, simp[this] },
  case equal : t u { have : {q : formula L | q.subformula (t ≃ u)} = ∅, { ext q, simp, intros h, rcases h }, simp[this] },
  case imply : p q { have : {r : formula L | r.subformula (p ⟶ q)} = {p, q},
    { ext r, simp, split, { rintros h, rcases h; simp }, { rintros (rfl | rfl), exact subformula.implyl, exact subformula.implyr } },
    simp[this] },
  case neg : p IH
  { have : {q : formula L | q.subformula (⁻p)} = {p},
    { ext q, simp, split, { intros h, rcases h, simp }, { rintros rfl, exact subformula.neg } },
    simp[this] },
  case fal : p IH
  { have : {q : formula L | q.subformula (∏ p)} = {p},
    { ext q, simp, split, { intros h, rcases h, simp }, { rintros rfl, exact subformula.fal } },
    simp[this] }
end

lemma le_finite (p : formula L) : set.finite {q | q ≤ p} :=
wf_lt.le_finite (show ∀ (a : formula L), {b : formula L | wf_lt.prelt b a}.finite, from prelt_finite) p

lemma subterm_finite (p : formula L) : set.finite {t : term L | subterm t p} :=
begin
  induction p,
  case verum { have : {t : term L | subterm t ⊤} = ∅, { ext t, simp, intros h, rcases h }, simp[this] },
  case app : n r v
  { have : {t : term L | subterm t (app r v)} = set.range v,
    { ext t, simp, split,
      { intros h, rcases h, simp }, { rintros ⟨i, rfl⟩, exact subterm.app r v i } },
    simp[this, set.finite_range] },
  case equal : t u
  { have : {s : term L | subterm s (t ≃ u)} = {t, u},
    { ext s, simp, split,
      { intros h, rcases h; simp }, { rintros (rfl | rfl), exact subterm.equall, exact subterm.equalr } },
    simp[this] },
  case imply : p q
  { have : {t : term L | subterm t (p ⟶ q)} = ∅, { ext r, simp, intros h, rcases h }, simp[this] },
  case neg : p IH
  { have : {t : term L | subterm t (⁻p)} = ∅, { ext r, simp, intros h, rcases h }, simp[this] },
  case fal : p IH
  { have : {t : term L | subterm t (∏ p)} = ∅, { ext r, simp, intros h, rcases h }, simp[this] }
end

lemma mem_finite (p : formula L) : set.finite {t : term L | t ∈ p} :=
begin
  let s := ⋃ q ∈ {q | q ≤ p}, {t : term L | subterm t q},
  let b := ⋃ t ∈ s, {u | u ≤ t},
  have : {t : term L | t ∈ p} = b,
  { ext t, simp[b, s, mem_def], split,
    { rintros ⟨t', t_le_t', ⟨p', p'_le_p, t'_st_p'⟩⟩, refine ⟨p', p'_le_p, t', t'_st_p', t_le_t'⟩ },
    { rintros ⟨p', p'_le_p, t', t'_st_p', t_le_t'⟩, exact ⟨t', t_le_t', ⟨p', p'_le_p, t'_st_p'⟩⟩ } },
  simp[this],
  have : s.finite, from set.finite.bUnion (le_finite p) (λ q h, subterm_finite q),
  refine set.finite.bUnion this (λ u h, term.le_finite u),
end

@[simp] lemma formula.ite_pow (p : Prop) [decidable p] (q r : formula L) (k : ℕ) :
  (ite p q r)^k = ite p (q^k) (r^k) :=
by by_cases C : p; simp[C]

end formula

namespace language

class predicate (L : language.{u}) :=
(fun_empty : ∀ n, is_empty (L.fn n))

end language

end fopl
