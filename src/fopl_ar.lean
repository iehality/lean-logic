import tactic lib

/- 焼き直し -/

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

variables (L : language.{u}) (β : ℕ)

inductive term : ℕ → Type u
| var : ∀ {β}, fin β → term β
| app : ∀ {β n}, L.fn n → (fin n → term β) → term β

variables {L} {β}

prefix `#`:max := term.var

notation `❨` c `❩ ` v :84 := term.app c v

instance {n} : inhabited (term L (n + 1)) := ⟨#0⟩

instance [has_zero_symbol L] : has_zero (term L β) := ⟨term.app has_zero_symbol.zero finitary.nil⟩

instance [has_succ_symbol L] : has_succ (term L β) := ⟨λ t, term.app has_succ_symbol.succ ‹t›⟩

instance [has_add_symbol L] {β} : has_add (term L β) := ⟨λ t u, term.app has_add_symbol.add ‹t, u›⟩

instance [has_mul_symbol L] {β} : has_mul (term L β) := ⟨λ t u, term.app has_mul_symbol.mul ‹t, u›⟩

postfix `˙`:max := numeral

@[reducible] def idvar (β : ℕ) : finitary (term L β) β := λ i, #i

notation `##` := idvar _

@[simp] lemma idvar_app (β : ℕ) (i : fin β) : (## : finitary (term L β) β) i = #i := rfl

variables (L) (β)

def term_to_string [∀ n, has_to_string (L.fn n)] : Π {β}, term L β → string
| β #n := "#" ++ has_to_string.to_string n
| β (@term.app _ _ n c v) :=
    has_to_string.to_string c ++ "(" ++ @has_to_string.to_string (finitary _ _) _ (λ i, term_to_string (v i)) ++ ")"

instance [∀ n, has_to_string (L.fn n)] {β} : has_to_string (term L β) := ⟨term_to_string L⟩

inductive formula : ℕ → Type u
| verum : Π {β}, formula β
| app   : ∀ {β n : ℕ}, L.pr n → (fin n → term L β) → formula β
| equal : ∀ {β}, term L β → term L β → formula β
| imply : ∀ {β}, formula β → formula β → formula β
| neg   : ∀ {β}, formula β → formula β
| fal   : ∀ {β}, formula (β + 1) → formula β

notation `❴` c `❵` := formula.app c

instance [has_le_symbol L] {β} : has_preceq (term L β) (formula L β) := ⟨λ t u, formula.app has_le_symbol.le ‹t, u›⟩

instance [has_mem_symbol L] {β} : has_elem (term L β) (formula L β) := ⟨λ t u, formula.app has_mem_symbol.mem ‹t, u›⟩

attribute [pattern]  has_eq.eq has_negation.neg has_arrow.arrow has_univ_quantifier.univ has_exists_quantifier.ex

instance : has_top (formula L β) := ⟨formula.verum⟩

instance : has_arrow (formula L β) := ⟨formula.imply⟩

instance : has_eq (term L β) (formula L β) := ⟨formula.equal⟩

local infix ` ≃₁ `:80 := ((≃) : term L β → term L β → formula L β)

instance {β} : has_negation (formula L β) := ⟨formula.neg⟩

instance : has_univ_quantifier' (formula L) := ⟨λ β, formula.fal⟩

prefix `ℿ`:64 := formula.fal

instance {β} : has_bot (formula L β) := ⟨⁻⊤⟩

def formula_to_string [∀ β, has_to_string (term L β)] [∀ n, has_to_string (L.pr n)] :
  Π {β}, formula L β → string
| β formula.verum                  := "⊤"
| β (@formula.app _ _ 0 p v)       := has_to_string.to_string p
| β (@formula.app _ _ 1 p v)       := has_to_string.to_string p ++ "(" ++ has_to_string.to_string (v 0) ++ ")"
| β (@formula.app _ _ 2 p v)       :=
    has_to_string.to_string (v 0) ++ has_to_string.to_string p ++ has_to_string.to_string (v 1)
| β (@formula.app _ _ (n + 3) p v) :=
    has_to_string.to_string p ++ "(" ++ @has_to_string.to_string (finitary _ _) _ v ++ ")"
| β (formula.equal t u)            := has_to_string.to_string t ++ " = " ++ has_to_string.to_string u
| β (formula.imply p q)            := formula_to_string p ++ " → " ++ formula_to_string q
| β (formula.neg p)                := "¬(" ++ formula_to_string p ++ ")"
| β (formula.fal p)                := "∀(" ++ formula_to_string p ++ ")"

instance [∀ β, has_to_string (term L β)] [∀ n, has_to_string (L.pr n)] : has_to_string (formula L β) :=
⟨formula_to_string L⟩

@[simp] lemma formula.top_eq : @formula.verum L = (⊤) := rfl
@[simp] lemma formula.imply_eq : @formula.imply L β = (⟶) := rfl
@[simp] lemma formula.equal_eq : @formula.equal L β = (≃) := rfl
@[simp] lemma formula.neg_eq : @formula.neg L β = has_negation.neg := rfl
@[simp] lemma formula.fal_eq : @formula.fal L β = has_univ_quantifier'.univ := rfl

instance : inhabited (formula L β) := ⟨⊤⟩

@[reducible] def theory (L : language.{u}) (β) := set (formula L β)

variables {L} {β} {γ : ℕ}

def formula.and (p : formula L β) (q : formula L β) : formula L β := ⁻(p ⟶ ⁻q)

instance : has_inf (formula L β) := ⟨formula.and⟩

def formula.or (p : formula L β) (q : formula L β) : formula L β := ⁻p ⟶ q

instance : has_sup (formula L β) := ⟨formula.or⟩

def formula.ex (p : formula L (β + 1)) : formula L β := ⁻𝚷⁻p

instance : has_exists_quantifier' (formula L) := ⟨λ _, formula.ex⟩

lemma formula.ex_eq (p : formula L (β + 1)) : (𝚺 p : formula L β) = ⁻𝚷⁻p := rfl

@[simp] lemma formula.equal.inj' (t₁ u₁ t₂ u₂ : term L β) : (t₁ ≃ t₂ : formula L β) = (u₁ ≃ u₂) ↔ t₁ = u₁ ∧ t₂ = u₂ :=
⟨formula.equal.inj, by simp; exact congr_arg2 (≃)⟩

@[simp] lemma formula.imply.inj' (p₁ q₁ p₂ q₂ : formula L β) : p₁ ⟶ p₂ = q₁ ⟶ q₂ ↔ p₁ = q₁ ∧ p₂ = q₂ :=
⟨formula.imply.inj, by simp; exact congr_arg2 (⟶)⟩

@[simp] lemma formula.neg.inj' (p q : formula L β) : ⁻p = ⁻q ↔ p = q := ⟨formula.neg.inj, congr_arg _⟩

@[simp] lemma formula.and.inj' (p₁ q₁ p₂ q₂ : formula L β) : p₁ ⊓ p₂ = q₁ ⊓ q₂ ↔ p₁ = q₁ ∧ p₂ = q₂ :=
by simp[has_inf.inf, formula.and]

@[simp] lemma formula.or.inj' (p₁ q₁ p₂ q₂ : formula L β) : p₁ ⊔ p₂ = q₁ ⊔ q₂ ↔ p₁ = q₁ ∧ p₂ = q₂ :=
by simp[has_sup.sup, formula.or]

@[simp] lemma formula.fal.inj' (p q : formula L (β + 1)) : 𝚷 p = 𝚷 q ↔ p = q := ⟨formula.fal.inj, congr_arg _⟩

@[simp] lemma formula.ex.inj' (p q : formula L (β + 1)) : 𝚺 p = 𝚺 q ↔ p = q := 
by simp[has_exists_quantifier'.ex, formula.ex]

@[simp] lemma formula.verum_ne_predicate {n} (r : L.pr n) (v : finitary (term L β) n) :
 ⊤ ≠ formula.app r v.

@[simp] lemma formula.verum_ne_equal (t u : term L β) : (⊤ : formula L β) ≠ (t ≃ u).

@[simp] lemma formula.verum_ne_imply (p q : formula L β) : ⊤ ≠ (p ⟶ q).

@[simp] lemma formula.verum_ne_neg (p : formula L β) : ⊤ ≠ ⁻p.

@[simp] lemma formula.verum_ne_fal (p : formula L (β + 1)) : ⊤ ≠ 𝚷 p.

@[simp] lemma formula.predicate_ne_verum {n} (r : L.pr n) (v : finitary (term L β) n) :
  formula.app r v ≠ ⊤.

@[simp] lemma formula.predicate_ne_equal {n} (r : L.pr n) (v : finitary (term L β) n) (t u : term L β) :
  formula.app r v ≠ (t ≃ u).

@[simp] lemma formula.predicate_ne_imply {n} (r : L.pr n) (v : finitary (term L β) n) (p q : formula L β) :
  formula.app r v ≠ p ⟶ q.

@[simp] lemma formula.predicate_ne_neg {n} (r : L.pr n) (v : finitary (term L β) n) (p : formula L β) :
  formula.app r v ≠ ⁻p.

@[simp] lemma formula.predicate_ne_fal {n} (r : L.pr n) (v : finitary (term L β) n) (p) :
  formula.app r v ≠ 𝚷 p.

@[simp] lemma formula.equal_ne_verum (t u : term L β) :
  (t ≃ u : formula L β) ≠ ⊤.

@[simp] lemma formula.equal_ne_predivate (t u : term L β) {n} (r : L.pr n) (v : finitary (term L β) n) :
  (t ≃ u) ≠ formula.app r v.

@[simp] lemma formula.equal_ne_imply (t u : term L β) (p q : formula L β) :
  (t ≃ u) ≠ p ⟶ q.

@[simp] lemma formula.equal_ne_neg (t u : term L β) (p : formula L β) :
  (t ≃ u) ≠ ⁻p.

@[simp] lemma formula.equal_ne_fal (t u : term L β) (p) :
  (t ≃ u : formula L β) ≠ 𝚷 p.

@[simp] lemma formula.imply_ne_verum (p q : formula L β) :
  p ⟶ q ≠ ⊤.

@[simp] lemma formula.imply_ne_predicate (p q : formula L β) {n} (r : L.pr n) (v : finitary (term L β) n) :
  p ⟶ q ≠ formula.app r v.

@[simp] lemma formula.imply_ne_equal (p q : formula L β) (t u : term L β) :
  p ⟶ q ≠ (t ≃ u).

@[simp] lemma formula.imply_ne_neg (p q r : formula L β) : p ⟶ q ≠ ⁻r.

@[simp] lemma formula.imply_ne_fal (p q : formula L β) (r) : p ⟶ q ≠ 𝚷 r.

@[simp] lemma formula.neg_ne_verum (p : formula L β) : ⁻p ≠ ⊤.

@[simp] lemma formula.neg_ne_predicate (p : formula L β) {n} (r : L.pr n) (v : finitary (term L β) n) :
 ⁻p ≠ formula.app r v.

@[simp] lemma formula.neg_ne_equal (p : formula L β) (t u : term L β) : ⁻p ≠ (t ≃ u).

@[simp] lemma formula.neg_ne_imply (p q r : formula L β) : ⁻p ≠ (q ⟶ r).

@[simp] lemma formula.neg_ne_fal (p : formula L β) (q) : ⁻p ≠ 𝚷 q.

@[simp] lemma formula.fal_ne_verum (p : formula L (β + 1)) :
  𝚷 p ≠ ⊤.

@[simp] lemma formula.fal_ne_predicate (p : formula L (β + 1)) {n} (r : L.pr n) (v : finitary (term L β) n) :
  𝚷 p ≠ formula.app r v.

@[simp] lemma formula.fal_ne_equal (p : formula L (β + 1)) (t u : term L β) :
  (𝚷 p : formula L β) ≠ (t ≃ u).

@[simp] lemma formula.fal_ne_imp (p : formula L (β + 1)) (q r : formula L β) : 𝚷 p ≠ (q ⟶ r).

@[simp] lemma formula.fal_ne_neg (p : formula L (β + 1)) (q : formula L β) : 𝚷 p ≠ ⁻q.

@[simp] lemma formula.fal_ne_ex (p q : formula L (β + 1)) : 𝚷 p ≠ 𝚺 q.

@[simp] lemma formula.ex_ne_fal (p q : formula L (β + 1)) : 𝚺 p ≠ 𝚷 q.

@[simp] def nfal_complete : Π {β}, formula L β → formula L 0
| 0     p := p
| (n+1) p := nfal_complete (𝚷 p)

prefix `𝚷* `:64 := nfal_complete

@[simp] def nfal : Π n, formula L (β + n) → formula L β
| 0     p := p
| (n+1) p := nfal n (𝚷 p)

notation `𝚷[` k `] `:90 p := nfal k p

@[simp] def conjunction' : ∀ n, (fin n → formula L β) → formula L β
| 0 _        := ⊤
| (n + 1) f  := (f ⟨n, lt_add_one n⟩) ⊓ conjunction' n (λ i, f ⟨i.val, nat.lt.step i.property⟩)

notation `⋀` binders `, ` r:(scoped p, conjunction' _ p) := r

@[simp] def disjunction' : ∀ n, (fin n → formula L β) → formula L β
| 0 _        := ⊥
| (n + 1) f  := (f ⟨n, lt_add_one n⟩) ⊔ disjunction' n (λ i, f ⟨i.val, nat.lt.step i.property⟩)

notation `⋁` binders `, ` r:(scoped p, disjunction' _ p) := r

def conjunction : list (formula L β) → formula L β
| []        := ⊤
| (p :: ps) := p ⊓ conjunction ps

@[reducible] def ι {β : ℕ} : fin β → term L β := term.var

namespace term

@[simp] def rew : Π {β γ}, (finitary (term L γ) β) → term L β → term L γ
| β γ s (#x)           := s x
| β γ s (term.app f v) := ❨f❩ (λ i, rew s (v i))

@[simp] lemma nested_rew : ∀ {β γ δ} (t : term L β) (s₀ : finitary (term L γ) β) (s₁ : finitary (term L δ) γ),
  (t.rew s₀).rew s₁ = t.rew (λ x, (s₀ x).rew s₁)
| β γ δ (#x)     := by simp[rew]
| β γ δ (❨f❩ v)  := by simp[rew, nested_rew]

@[simp] lemma rew_ι (t : term L β) : t.rew ι = t :=
by induction t; simp[rew]; simp*

def shift : Π {β}, term L β → term L (β + 1) := λ β t, t.rew (λ i, #(i + 1))

instance : has_shift (term L) := ⟨@shift L⟩

lemma shift_eq (t : term L β) : ⤉t = t.rew (λ i, #(i + 1)) := rfl

lemma pow_eq (t : term L β) (k) : t ↟ k = t.rew (λ x, #(⟨x + k, by simp⟩)) :=
by { induction k with k IH; simp[*, shift_eq, nested_rew , ←nat.add_one, add_assoc], refl }

def lift : Π {β}, term L β → term L (β + 1) := λ β t, t.rew (λ i, #i)

instance : has_shift' (term L) := ⟨@lift L⟩

@[simp] lemma shift_var (x : fin β) : ⤉(#x : term L β) = #x.succ := by simp[has_shift.shift, shift]

@[simp] lemma lift_var (x : fin β) : ⤉'(#x : term L β) = #x := by simp[has_shift'.shift', lift]

@[simp] lemma shift_function {n} (f : L.fn n) (v : finitary (term L β) n) :
  ⤉(term.app f v : term L β) = term.app f (λ i, ⤉(v i)) := by simp[has_shift.shift, shift]

@[simp] lemma lift_function {n} (f : L.fn n) (v : finitary (term L β) n) :
  ⤉'(term.app f v : term L β) = term.app f (λ i, ⤉'(v i)) := by simp[has_shift'.shift', lift]

@[reducible] def rew_var (s : fin β → fin γ) : term L β → term L γ := λ t, t.rew (λ x, #(s x))

@[simp] lemma constant_rew (c : L.fn 0) (s : finitary (term L γ) β) {v : finitary (term L β) 0} :
  (app c v : term L β).rew s = app c finitary.nil :=
by simp

@[simp] lemma unary_rew (f : L.fn 1) (s : finitary (term L γ) β) (v : finitary (term L β) 1) :
  (app f v).rew s = app f ‹(v 0).rew s› :=
by simp; ext; simp

@[simp] lemma binary_rew (f : L.fn 2) (s : finitary (term L γ) β) (v : finitary (term L β) 2) :
  (app f v).rew s = app f ‹(v 0).rew s, (v 1).rew s› :=
by simp; ext; simp

@[simp] lemma zero_rew [h : has_zero_symbol L] (s : finitary (term L γ) β) : (0 : term L β).rew s = 0 :=
by unfold has_zero.zero; simp

@[simp] lemma succ_rew [h : has_succ_symbol L] (t : term L β) (s : finitary (term L γ) β) :
  (Succ t : term L β).rew s = Succ (t.rew s) :=
by unfold has_succ.succ; simp; ext; simp

@[simp] lemma numeral_rew [h : has_zero_symbol L] [h : has_succ_symbol L] (n : ℕ) (s : finitary (term L γ) β) :
  (n˙ : term L β).rew s = n˙ :=
by induction n; simp[*, numeral]

@[simp] lemma add_rew [h : has_add_symbol L] (t u : term L β) (s : finitary (term L γ) β) :
  (t + u : term L β).rew s = t.rew s + u.rew s :=
by unfold has_add.add; simp; ext; simp

@[simp] lemma mul_rew [h : has_mul_symbol L] (t u : term L β) (s : finitary (term L γ) β) :
  (t * u : term L β).rew s = t.rew s * u.rew s :=
by unfold has_mul.mul; simp; ext; simp

@[simp] lemma var_pow (n : fin β) (k : ℕ) : (#n : term L β) ↟ k = #⟨n + k, by simp⟩ :=
by induction k with k IH; simp[*, ←nat.add_one, add_assoc]

@[simp] lemma app_pow {n} (f : L.fn n) (v : finitary' (term L) n β) (k : ℕ) :
  (❨f❩ v) ↟ k = ❨f❩ (v ↟ k) :=
by {induction k with k IH; simp*, funext i, simp }

@[simp] lemma app_lift_pow {n} (f : L.fn n) (v : finitary' (term L) n β) (k : ℕ) :
  (❨f❩ v) ↟' k = ❨f❩ (v ↟' k) :=
by {induction k with k IH; simp*, funext i, simp }

@[simp] lemma unary_pow (f : L.fn 1) (v : finitary (term L β) 1) (k : ℕ) :
  (app f v) ↟ k = app f ‹(v 0) ↟ k› :=
by simp; ext; simp

@[simp] lemma unary_lift_pow (f : L.fn 1) (v : finitary (term L β) 1) (k : ℕ) :
  (app f v) ↟ k = app f ‹(v 0) ↟ k› :=
by simp; ext; simp

@[simp] lemma binary_pow (f : L.fn 2) (v : finitary (term L β) 2) (k : ℕ) :
  (app f v) ↟ k = app f ‹(v 0) ↟ k, (v 1) ↟ k› :=
by simp; ext; simp

@[simp] lemma zero_pow [h : has_zero_symbol L] (k : ℕ) : (0 : term L β) ↟ k = 0 :=
by { unfold has_zero.zero, induction k with k IH; simp* }

@[simp] lemma succ_pow [h : has_succ_symbol L] (t : term L β) (k : ℕ) : (Succ t : term L β) ↟ k = Succ (t ↟ k) :=
by unfold has_succ.succ; simp

@[simp] lemma numeral_pow [h : has_zero_symbol L] [h : has_succ_symbol L] (n : ℕ) (k : ℕ) :
  (n˙ : term L β) ↟ k = n˙ :=
by induction n with n IH; simp[*, numeral]

@[simp] lemma add_pow [h : has_add_symbol L] (t u : term L β) (k : ℕ) : (t + u : term L β) ↟ k = t ↟ k + u ↟ k :=
by unfold has_add.add; simp

@[simp] lemma mul_pow [h : has_mul_symbol L] (t u : term L β) (k : ℕ) : (t * u : term L β) ↟ k = t ↟ k * u ↟ k :=
by unfold has_mul.mul; simp

@[simp] lemma rew_var_inj_of_inj :
  ∀ {β} {t u : term L β} {s : fin β → fin γ} (I : function.injective s),
  t.rew_var s = u.rew_var s ↔ t = u
| β #x               #y               s I := by { simp[rew_var], exact ⟨@I x y, congr_arg (λ x, s x)⟩ }
| β #x               (term.app f v)   s I := by simp[rew_var]
| β (term.app f v)   #x               s I := by simp[rew_var]
| β (term.app f₁ v₁) (term.app f₂ v₂) s I :=
    begin
      simp[rew_var], rintros rfl rfl, simp, split,
      { intros h, funext j,
        have : (v₁ j).rew_var s = (v₂ j).rew_var s,
        { have := congr_fun h j, simp at this, exact this },
        exact (@rew_var_inj_of_inj β (v₁ j) (v₂ j) s I).mp this },
      { rintros rfl, simp }
    end

@[simp] lemma pow_inj :
  ∀ {β} {t u : term L β} {k : ℕ}, t ↟ k = u ↟ k ↔ t = u
| β #x               #y               k := by { simp, exact set_coe.ext_iff }
| β #x               (term.app f v)   k := by simp
| β (term.app f v)   #x               k := by simp
| β (term.app f₁ v₁) (term.app f₂ v₂) k :=
    begin
      simp, rintros rfl, simp, intros, split,
      { intros h, funext i,
        have : (v₁ i) ↟ k = (v₂ i) ↟ k,
        { have := congr_fun h i, simp at this, exact this },
        exact (@pow_inj β (v₁ i) (v₂ i) k).mp this },
      { rintros rfl, simp }
    end

@[simp] lemma finitary_pow_inj {n} {v w : finitary' (term L) n β} {i : ℕ} : v ↟ i = w ↟ i ↔ v = w :=
⟨λ h, funext (λ i, by { have := congr_fun h i, simp at this, exact this }),
  by { rintros rfl, simp }⟩

lemma total_rew_inv :
  ∀ {β γ} (s : finitary (term L γ) β) (h : ∀ n, ∃ m, s m = #n), ∀ (p : term L γ) , ∃ q : term L β, q.rew s = p
| β γ s h (#x) := by rcases h x with ⟨q, h_q⟩; refine ⟨#q, _⟩; simp[h_q]
| β γ s h (@app _ _ n f v) := by rcases classical.skolem.mp (λ i, total_rew_inv s h (v i)) with ⟨w, w_eqn⟩;
    refine ⟨❨f❩ w, by simp[w_eqn]⟩

@[simp] lemma rew_rew {β γ} {s₀ s₁ : finitary (term L γ) β} (t : term L β) : s₀ = s₁ → t.rew s₀ = t.rew s₁ :=
by { rintros rfl, refl }

@[simp] lemma concat_pow_eq (t : term L β) (s : finitary (term L γ) (β + 1)) :
  (⤉t).rew s = t.rew s.tail := by simp[shift_eq, finitary.tail]

end term

def rewsf (s : finitary' (term L) β γ) : finitary (term L (γ + 1)) (β + 1) := #0 ::ᶠ ⤉s

@[simp] lemma rewsf_ι : rewsf (@ι L β) = ι :=
by { simp[rewsf], ext ⟨i, h⟩, cases i; simp }

@[simp] def rewsf_itr (s : finitary (term L γ) β) : Π k, finitary (term L (γ + k)) (β + k)
| 0     := s
| (n+1) := rewsf (rewsf_itr n)

namespace formula

@[simp] def rew : Π {β γ}, (finitary (term L γ) β) → formula L β → formula L γ
| β γ s formula.verum         := ⊤
| β γ s (app p v) := app p (λ i, (v i).rew s)
| β γ s (formula.equal t u)  := (t.rew s) ≃ (u.rew s)
| β γ s (formula.imply p q)  := p.rew s ⟶ q.rew s
| β γ s (formula.neg p)      := ⁻(p.rew s)
| β γ s (formula.fal p)      := 𝚷 (rew (rewsf s) p)

@[reducible] def rew_var (s : fin β → fin γ) : formula L β → formula L γ := λ p, p.rew (λ x, #(s x))

@[simp] lemma constant_rew (p : L.pr 0) (s : finitary (term L γ) β) {v : finitary (term L β) 0} :
  (❴p❵ v).rew s = ❴p❵ finitary.nil := by simp

@[simp] lemma unary_rew (p : L.pr 1) (s : finitary (term L γ) β) (v : finitary (term L β) 1) :
  (❴p❵ v).rew s = ❴p❵ ‹(v 0).rew s› :=
by simp; ext; simp

@[simp] lemma binary_rew (p : L.pr 2) (s : finitary (term L γ) β) (v : finitary (term L β) 2) :
  (❴p❵ v).rew s = ❴p❵ ‹(v 0).rew s, (v 1).rew s› :=
by simp; ext; simp

@[simp] lemma le_rew [c : has_le_symbol L] (t u : term L β) (s : finitary (term L γ) β) :
  (t ≼ u : formula L β).rew s = (t.rew s ≼ u.rew s) :=
by unfold has_preceq.preceq; simp

@[simp] lemma mem_rew [c : has_mem_symbol L] (t u : term L β) (s : finitary (term L γ) β) :
  (t ∊ u : formula L β).rew s = (t.rew s ∊ u.rew s) :=
by unfold has_elem.elem; simp

@[simp] lemma equal_rew (t u : term L β) (s : finitary (term L γ) β) :
  (t ≃ u : formula L β).rew s = (t.rew s ≃ u.rew s) := rfl
@[simp] lemma verum_rew (s : finitary (term L γ) β) :
  (⊤ : formula L β).rew s = ⊤ := rfl
@[simp] lemma neg_rew (p : formula L β) (s : finitary (term L γ) β) :
  (⁻p).rew s = ⁻(p.rew s) := rfl
@[simp] lemma imply_rew (p q : formula L β) (s : finitary (term L γ) β) :
  (p ⟶ q).rew s = p.rew s ⟶ q.rew s := rfl
@[simp] lemma fal_rew (p : formula L (β + 1)) (s : finitary (term L γ) β) :
  (𝚷 p).rew s = 𝚷 (rew (rewsf s) p) := rfl
@[simp] lemma and_rew (p q : formula L β) (s : finitary (term L γ) β) :
  (p ⊓ q).rew s = p.rew s ⊓ q.rew s := rfl
@[simp] lemma or_rew (p q : formula L β) (s : finitary (term L γ) β) :
  (p ⊔ q).rew s = p.rew s ⊔ q.rew s := rfl
@[simp] lemma iff_rew (p q : formula L β) (s : finitary (term L γ) β) :
  (p ⟷ q).rew s = p.rew s ⟷ q.rew s := rfl

@[simp] lemma nfal_rew (k : ℕ) (p : formula L (β + k)) (s : finitary' (term L) β γ) :
  (𝚷[k] p).rew s = 𝚷[k] (p.rew (rewsf_itr s k)) :=
by { induction k with k IH generalizing s, { simp },
     simp[←nat.add_one, IH] }

@[simp] lemma ex_rew (p : formula L (β + 1)) (s : finitary (term L γ) β) :
  (𝚺 p).rew s = 𝚺 p.rew (rewsf s) :=by simp[has_exists_quantifier'.ex, formula.ex, rewsf]
@[simp] lemma bot_rew (s : finitary (term L γ) β) : (⊥ : formula L β).rew s = ⊥ := by simp[has_bot.bot]

@[simp] lemma rew_ι (p : formula L β) : p.rew ι = p :=
by induction p; simp*

@[simp] lemma conjunction'_rew {n} (P : finitary (formula L β) n) (s : finitary (term L γ) β) :
  (conjunction' n P).rew s = conjunction' n (λ i, (P i).rew s) :=
by { induction n with n IH; simp* }

@[simp] lemma disjunction'_rew {n} (P : finitary (formula L β) n) (s : finitary (term L γ) β) :
  (disjunction' n P).rew s = disjunction' n (λ i, (P i).rew s) :=
by { induction n with n IH; simp* }

lemma nested_rew : ∀ {β γ δ} (p : formula L β) (s₀ : finitary (term L γ) β) (s₁ : finitary (term L δ) γ),
  (p.rew s₀).rew s₁ = p.rew (λ x, (s₀ x).rew s₁)
| β γ δ formula.verum         _ _ := by simp
| β γ δ (❴p❵ v) _ _ := by simp[rew]
| β γ δ (formula.equal t u)  _ _ := by simp[rew]
| β γ δ (formula.imply p q)   _ _ := by simp[rew, nested_rew p, nested_rew q]
| β γ δ (formula.neg p)      _ _ := by simp[rew]; refine nested_rew p _ _
| β γ δ (formula.fal p)     _ _ := by { simp[rew, nested_rew p], congr,
    ext ⟨n, h⟩, cases n; simp[rewsf, term.shift_eq] }

@[simp] def shift : Π {β}, formula L β → formula L (β + 1) := λ β t, t.rew (λ i, #i.succ)

instance : has_shift (formula L) := ⟨@shift L⟩

lemma shift_eq (p : formula L β) : ⤉p = p.rew (λ x, #x.succ) := rfl

lemma pow_eq (p : formula L β) (k) : p ↟ k = p.rew (λ x, #(⟨x + k, by simp⟩)) :=
by { induction k with k IH; simp[*, shift_eq, nested_rew , ←nat.add_one, add_assoc], refl }

lemma pow_eq_rew_var (p : formula L β) (k) : p ↟ k = p.rew_var (λ x, ⟨x + k, by simp⟩) :=
by simp[pow_eq]

@[simp] lemma app_shift {n} (p : L.pr n) (v : finitary' (term L) n β) :
  ⤉(app p v) = app p (⤉v) := by simp[has_shift.shift, term.shift]

@[simp] lemma constant_pow (c : L.pr 0) (k : ℕ) {v : finitary (term L β) 0} :
  (app c v) ↟ k = app c finitary.nil :=
by induction k; simp*

@[simp] lemma unary_pow (p : L.pr 1) (k : ℕ) (t : term L β) : (❴p❵ ‹t›) ↟ k = ❴p❵ ‹t ↟ k› :=
by induction k with k IH; simp*

@[simp] lemma binary_pow (p : L.pr 2) (k : ℕ) (t₁ t₂ : term L β) :
  (❴p❵ ‹t₁, t₂›) ↟ k = ❴p❵ ‹t₁ ↟ k, t₂ ↟ k› :=
by induction k with k IH; simp*

@[simp] lemma le_pow [c : has_le_symbol L] (t u : term L β) (k : ℕ) :
  (t ≼ u : formula L β) ↟ k = (t ↟ k ≼ u ↟ k) :=
by unfold has_preceq.preceq; induction k with k IH; simp*

@[simp] lemma mem_pow [c : has_mem_symbol L] (t u : term L β) (k : ℕ) :
  (t ∊ u : formula L β) ↟ k = (t ↟ k ∊ u ↟ k) :=
by unfold has_elem.elem; induction k with k IH; simp*

@[simp] lemma eq_pow (t u : term L β) (k : ℕ) : (t ≃₁ u) ↟ k = (t ↟ k ≃ u ↟ k) := by simp[term.pow_eq, pow_eq]
@[simp] lemma imply_pow (p q : formula L β) (k : ℕ) : (p ⟶ q) ↟ k = p ↟ k ⟶ q ↟ k := by simp[pow_eq]
@[simp] lemma neg_pow (p : formula L β) (k : ℕ) : (⁻p) ↟ k = ⁻(p ↟ k) := by simp[pow_eq]
@[simp] lemma and_pow (p q : formula L β) (k : ℕ) : (p ⊓ q) ↟ k = (p ↟ k) ⊓ (q ↟ k) := by simp[pow_eq]
@[simp] lemma or_pow (p q : formula L β) (k : ℕ) : (p ⊔ q) ↟ k = (p ↟ k) ⊔ (q ↟ k) := by simp[pow_eq]
@[simp] lemma top_pow (k : ℕ) : (⊤ : formula L β) ↟ k = ⊤ := by simp[pow_eq]
@[simp] lemma bot_pow (k : ℕ) : (⊥ : formula L β) ↟ k = ⊥ := by simp[pow_eq]

lemma fal_shift_discard (p : formula L (β + 1)) : ⤉(𝚷 p) = 𝚷 (p.rew (rewsf (λ x, #x.succ))) :=
by simp[shift_eq]

lemma fal_pow (p : formula L (β + 1)) (k : ℕ) :
  (𝚷 p) ↟ k = 𝚷 (p.rew (rewsf (λ x, #(⟨x + k, by simp⟩ : fin (β + k))))) :=
by simp[pow_eq]

lemma ex_shift_discard (p : formula L (β + 1)) : ⤉(𝚺 p) = 𝚺 (p.rew (rewsf (λ x, #x.succ))) :=
by simp[shift_eq]

lemma ex_pow (p : formula L (β + 1)) (k : ℕ) :
  (𝚺 p) ↟ k = 𝚺 (p.rew (rewsf (λ x, #(⟨x + k, by simp⟩ : fin (β + k))))) :=
by simp[pow_eq]


lemma rew_rew (p : formula L β) {s₀ s₁ : finitary (term L γ) β} : s₀ = s₁ → p.rew s₀ = p.rew s₁ :=
by { rintros rfl, refl }

@[simp] lemma sentence_rew {p : formula L 0} (s : finitary (term L 0) 0) : p.rew s = p :=
by { suffices : p.rew s = p.rew ι, { simp at this, exact this }, refine rew_rew p (finitary.fin_0_ext _ _) }

@[simp] lemma concat_pow_eq (p : formula L β) (s : finitary (term L γ) (β + 1)) :
  (⤉p).rew s = p.rew s.tail := by simp[shift_eq, finitary.tail, nested_rew]

lemma pow_rew_distrib  (p : formula L β) (s : finitary' (term L) β γ) (k : ℕ) :
  (p.rew s) ↟ k = (p ↟ k).rew (rewsf_itr s k) :=
by { induction k with k IH generalizong s, { simp },
     { simp[←nat.add_one, nested_rew, IH, shift_eq],
       refine rew_rew _ (funext (λ i, _)), simp[rewsf, term.shift_eq] } }

lemma rewriting_sf_perm {s : finitary (term L γ) β} (h : ∀ n, ∃ m, s m = #n) : ∀ n, ∃ m, (rewsf s) m = #n :=
λ ⟨n, lt⟩, by { cases n, refine ⟨0, by simp[rewsf]⟩,
  simp[←nat.add_one] at lt,
          rcases h ⟨n, lt⟩ with ⟨m, e_m⟩, refine ⟨m+1, _⟩, simp[e_m, rewsf] }

lemma total_rew_inv :
  ∀ {β} {γ} (s : finitary (term L γ) β) (h : ∀ n, ∃ m, s m = #n) (p : formula L γ), ∃ q : formula L β, q.rew s = p
| β γ _ _ formula.verum := ⟨⊤, by simp⟩
| β γ s h (@app _ _ n p v) :=
    by rcases classical.skolem.mp (λ i : fin n, @term.total_rew_inv _ β γ s h (v i : term L γ)) with ⟨w, w_p⟩;
    refine ⟨❴p❵ w, by simp[w_p]⟩
| β γ s h (formula.equal t u)       := 
    by rcases term.total_rew_inv s h t with ⟨w₁, e_w₁⟩;
       rcases term.total_rew_inv s h u with ⟨w₂, e_w₂⟩; refine ⟨w₁ ≃ w₂, by simp[e_w₁, e_w₂]⟩
| β γ s h (formula.imply p q)        := 
    by rcases total_rew_inv s h p with ⟨p', e_p'⟩;
       rcases total_rew_inv s h q with ⟨q', e_q'⟩; refine ⟨p' ⟶ q', by simp*⟩
| β γ s h (formula.neg p)           := by rcases total_rew_inv s h p with ⟨q, e_q⟩; refine ⟨⁻q, by simp*⟩
| β γ s h (formula.fal p)          :=
  by rcases total_rew_inv _ (rewriting_sf_perm h) p with ⟨q, e_q⟩; refine ⟨𝚷 q, by simp[e_q]⟩

@[simp] lemma rew_var_inj_of_inj :
  ∀ {β} {γ} {p q : formula L β} {s : fin β → fin γ} (I : function.injective s),
  p.rew_var s = q.rew_var s ↔ p = q
| β γ verum       p           s I := by {cases p; simp[rew_var], }
| β γ (app p v)   verum       s I := by simp[rew_var]
| β γ (app p₁ v₁) (app p₂ v₂) s I := by { simp[rew_var], rintros rfl rfl,
    simp, split,
    { intros h, funext i, refine (term.rew_var_inj_of_inj I).mp (congr_fun h i) },
    { rintros rfl, simp } }
| β γ (app p v)   (equal t u) s I := by simp[rew_var]
| β γ (app r v)   (imply p q) s I := by simp[rew_var]
| β γ (app r v)   (neg p)     s I := by simp[rew_var]
| β γ (app r v)   (fal p)     s I := by simp[rew_var, fal_pow]
| β γ (equal t u) p           s I := by cases p; simp[rew_var, fal_pow, I]
| β γ (imply p q) r           s I :=
    by cases r; simp[rew_var, fal_pow, @rew_var_inj_of_inj β γ p _ s I, @rew_var_inj_of_inj β γ q _ s I]
| β γ (neg p)     q           s I :=
    by cases q; simp[rew_var, fal_pow, @rew_var_inj_of_inj β γ p _ s I]
| β γ (fal p)     verum                   s I := by simp[rew_var]
| β γ (fal p)     (app r v)   s I := by simp[rew_var]
| β γ (fal p)     (equal t u) s I := by simp[rew_var]
| β γ (fal p)     (imply q r) s I := by simp[rew_var]
| β γ (fal p)     (neg q)     s I := by simp[rew_var]
| β γ (fal p)     (fal q)     s I := by { simp[rew_var, fal_pow], 
    have : ∀ p : formula L (β + 1),
      p.rew (rewsf (λ (x : fin β), #(s x))) = p.rew_var (0 ::ᶠ (λ i, (s i).succ)),
    { intros p, simp[rewsf, nested_rew], congr, ext ⟨i, h⟩, cases i; simp },
    have I' : function.injective (0 ::ᶠ (λ i, (s i).succ)),
    { rintros ⟨x, x_lt⟩ ⟨y, y_lt⟩, cases x with x; cases y with y; simp[fin.succ_ne_zero, λ k, ne.symm (fin.succ_ne_zero k)],
      { intros h, exact fin.mk.inj_iff.mp (I (congr_arg s (I h)))} },
    simp[this, @rew_var_inj_of_inj _ _ p q _ I'] }
  
@[simp] lemma pow_inj : ∀ {p q : formula L β} {i : ℕ}, p ↟ i = q ↟ i ↔ p = q :=
λ p q i, by { simp[pow_eq_rew_var], refine rew_var_inj_of_inj (λ x y, by { simp, exact fin.ext }) }

@[simp] def is_open : Π {β}, formula L β → bool
| β verum       := tt
| β (❴p❵ v)     := tt
| β (equal t u) := tt
| β (imply p q) := p.is_open && q.is_open
| β (neg p)     := p.is_open
| β (fal p)     := ff

@[simp] lemma is_open.verum : (⊤ : formula L β).is_open = tt := rfl

@[simp] lemma is_open.equal (t u : term L β) : (t ≃ u : formula L β).is_open = tt := rfl

@[simp] lemma is_open.imply (p q : formula L β) : (p ⟶ q : formula L β).is_open = p.is_open && q.is_open := rfl

@[simp] lemma is_open.neg (p : formula L β) : (⁻p : formula L β).is_open = p.is_open := rfl

@[simp] lemma is_open.fal (p : formula L (β + 1)) : (𝚷 p).is_open = ff := rfl

@[simp] lemma is_open.and (p q : formula L β) : (p ⊓ q).is_open = p.is_open && q.is_open := rfl

@[simp] lemma is_open.or (p q : formula L β) : (p ⊔ q).is_open = p.is_open && q.is_open := rfl

@[simp] def is_open_rew : ∀ {β γ} {p : formula L β} {s : finitary (term L γ) β}, (p.rew s).is_open ↔ p.is_open
| β γ verum       s := by simp
| β γ (❴p❵ v)     s := by simp
| β γ (equal t u) s := by simp
| β γ (imply p q) s  := by simp[@is_open_rew β γ p s, @is_open_rew β γ q s]
| β γ (neg p)     s := by simp[@is_open_rew β γ p s]
| β γ (fal p)     s   := by simp

@[simp] def is_open_pow : ∀ {p : formula L β} {k : ℕ}, (p ↟ k).is_open ↔ p.is_open :=
by simp[pow_eq]

end formula

namespace language

class predicate (L : language.{u}) :=
(fun_empty : ∀ n, is_empty (L.fn n))

end language

end fopl
