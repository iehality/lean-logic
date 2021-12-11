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

variables (L : language.{u})

inductive term : Type u
| var {} : ℕ → term
| app    : ∀ {n : ℕ}, L.fn n → (fin n → term) → term

variables {L}

prefix `#`:max := term.var

notation `❨` c `❩ ` v :84 := term.app c v

instance : inhabited (term L) := ⟨#0⟩

instance [has_zero_symbol L] : has_zero (term L) := ⟨term.app has_zero_symbol.zero finitary.nil⟩

instance [has_succ_symbol L] : has_succ (term L) := ⟨λ t, term.app has_succ_symbol.succ ‹t›⟩

instance [has_add_symbol L] : has_add (term L) := ⟨λ t u, term.app has_add_symbol.add ‹t, u›⟩

instance [has_mul_symbol L] : has_mul (term L) := ⟨λ t u, term.app has_mul_symbol.mul ‹t, u›⟩

def numeral [has_zero_symbol L] [has_succ_symbol L] : ℕ → term L
| 0       := 0
| (n + 1) := Succ (numeral n)

postfix `˙`:max := numeral

variables (L)

inductive formula : Type u
| app   : ∀ {n : ℕ}, L.pr n → (fin n → term L) → formula
| equal : term L → term L → formula
| imply : formula → formula → formula
| neg   : formula → formula
| fal   : formula → formula

notation `❴` c `❵` := formula.app c

notation `❴❴` c `❵❵` := @formula.app _ 0 c finitary.nil

notation t ` ❴`:66 c `❵ `:66 u :66 := @formula.app _ 2 c ‹t, u›

instance [has_le_symbol L] : has_preceq (term L) (formula L) := ⟨λ t u, formula.app has_le_symbol.le ‹t, u›⟩

instance [has_mem_symbol L] : has_elem (term L) (formula L) := ⟨λ t u, formula.app has_mem_symbol.mem ‹t, u›⟩

attribute [pattern]  has_eq.eq has_negation.neg has_arrow.arrow has_univ_quantifier.univ

instance : has_arrow (formula L) := ⟨formula.imply⟩

instance : has_eq (term L) (formula L) := ⟨formula.equal⟩

local infix ` ≃₁ `:80 := ((≃) : term L → term L → formula L)

instance : has_negation (formula L) := ⟨formula.neg⟩

instance : has_univ_quantifier (formula L) (formula L) := ⟨formula.fal⟩

local prefix `∏₁ `:64 := (has_univ_quantifier.univ : formula L → formula L)

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

instance : has_exists_quantifier (formula L) (formula L) := ⟨formula.ex⟩

local prefix `∐₁ `:64 := (has_exists_quantifier.ex : formula L → formula L)

lemma formula.ex_eq (p : formula L) : (∐₁ p) = ⁻∏⁻p := rfl

@[irreducible] def formula.top : formula L := ∏((#0 : term L) ≃₁ #0)

instance : has_top (formula L) := ⟨formula.top⟩

@[irreducible] def formula.bot : formula L := ⁻⊤

instance : has_bot (formula L) := ⟨formula.bot⟩

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

@[simp] lemma formula.ex.inj' (p q : formula L) : (∐ p : formula L) = ∐ q ↔ p = q := by simp[has_exists_quantifier.ex, formula.ex]

@[simp] def nfal (p : formula L) : ℕ → formula L
| 0     := p
| (n+1) := ∏ (nfal n)

notation `∏[` i `] `:90 p := nfal p i

@[simp] lemma nfal_fal (p : formula L) (i : ℕ) : nfal (∏ p : formula L) i = ∏ (nfal p i) :=
by { induction i with i IH; simp, exact IH }

@[simp] def conjunction' : ∀ n, (fin n → formula L) → formula L
| 0 _        := ⊤
| (n + 1) f  := (f ⟨n, lt_add_one n⟩) ⊓ conjunction' n (λ i, f ⟨i.val, nat.lt.step i.property⟩)

def conjunction : list (formula L) → formula L
| []        := ⊤
| (p :: ps) := p ⊓ conjunction ps

@[reducible] def ι : ℕ → term L := term.var

def slide' {α : Type*} (s : ℕ → α) (a : α) (n : ℕ) : ℕ → α :=
λ x, if x < n then s x else if n < x then s (x - 1) else a
notation s `[`:1200 n ` ⇝ `:95 t `]`:0 := slide' s t n

@[simp] lemma slide_eq {α : Type*} (s : ℕ → α) (a : α) (n) : s [n ⇝ a] n = a := by simp[slide']

@[simp] lemma slide_lt {α : Type*} (s : ℕ → α) (a : α) (n m) (h : m < n) : s [n ⇝ a] m = s m := by simp[slide', h]

@[simp] lemma slide_gt {α : Type*} (s : ℕ → α) (a : α) (n m) (h : n < m) : s [n ⇝ a] m = s (m - 1) :=
by {simp[slide', h], intros hh, exfalso, exact nat.lt_asymm h hh }

def concat {α : Type*} (s : ℕ → α) (a : α) : ℕ → α := s [0 ⇝ a]
notation a ` ⌢ `:90 s := concat s a

@[simp] lemma concat_0 {α : Type*} (s : ℕ → α) (a : α) : (a ⌢ s) 0 = a := rfl
@[simp] lemma concat_succ {α : Type*} (s : ℕ → α) (a : α) (n : ℕ) :
  (a ⌢ s) (n + 1) = s n := rfl

lemma slide_perm (i : ℕ) (t : term L) : ∀ n, ∃ m, ι[i ⇝ t] m = #n := λ n,
by { have C : n < i ∨ i ≤ n, exact lt_or_ge n i,
     cases C, refine ⟨n, by simp[C]⟩, 
     refine ⟨n + 1, _⟩, simp[nat.lt_succ_iff.mpr C] }

namespace term

@[simp] def rew (s : ℕ → term L) : term L → term L
| (#x)      := s x
| (❨f❩ v) := ❨f❩ (λ i, (v i).rew)

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

@[simp] lemma app_pow {n} (f : L.fn n) (v : fin n → term L) (i : ℕ) : (❨f❩ v)^i = ❨f❩ (v^i) := rfl

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

@[simp] lemma rew_ι (t : term L) : t.rew ι = t :=
by induction t; simp[rew]; simp*

lemma rew_rew {s₀ s₁ : ℕ → term L} : ∀ (t : term L),
  (∀ m, m < t.arity → s₀ m = s₁ m) → t.rew s₀ = t.rew s₁
| (#x)            h := by simp[rew, arity] at h ⊢; simp*
| (@app _ n f v)  h := by simp[rew, arity] at h ⊢; refine
  funext (λ i, rew_rew (v i) (λ m eqn, h m (lt_of_lt_of_le eqn (finitary.Max_le 0 (λ i, (v i).arity) i))))

lemma pow_add (t : term L) (i j : ℕ) : (t^i)^j = t^(i + j) :=
by simp[pow_eq, nested_rew, add_assoc]

@[simp] lemma arity0_rew {t : term L} (h : t.arity = 0) (s : ℕ → term L) : t.rew s = t :=
by { suffices : rew s t = rew ι t, { simp* },
     refine rew_rew _ _, simp[h] }

@[simp] lemma arity0_sf {v : term L} (h : v.arity = 0) (i : ℕ) : v^i = v := by simp[has_pow.pow, h]

lemma total_rew_inv
  (s : ℕ → term L) (h : ∀ n, ∃ m, s m = #n) : ∀ (p : term L) , ∃ q : term L, q.rew s = p
| (#x) := by rcases h x with ⟨q, h_q⟩; refine ⟨#q, _⟩; simp[h_q]
| (@app _ n f v) := by rcases classical.skolem.mp (λ i, total_rew_inv (v i)) with ⟨w, w_eqn⟩;
    refine ⟨❨f❩ w, by simp[w_eqn]⟩

@[simp] lemma pow_0 (t : term L) : t^0 = t := by simp[has_pow.pow]

@[simp] lemma sf_subst_eq (v : term L) (t : term L) (i j : ℕ) (h : j ≤ i) :
  (v^(i + 1)).rew (ι [j ⇝ t]) = v^i :=
by { simp[has_pow.pow, rew, nested_rew, h], congr, funext x,
     have : j < x + (i + 1), from nat.lt_add_left _ _ _ (nat.lt_succ_iff.mpr h),
     simp[this] }

@[simp] lemma concat_pow_eq (v : term L) (t : term L) (s : ℕ → term L) :
  (v^1).rew (t ⌢ s) = v.rew s :=
by simp[concat, rew, pow_eq, nested_rew]

def vector_vars {n} : vector (term L) n := vector.of_fn $ λ i, #i
notation `##` := vector_vars

end term

def rewriting_sf_itr (s : ℕ → term L) : ℕ → ℕ → term L
| 0     := s
| (n+1) := #0 ⌢ λ x, (rewriting_sf_itr n x)^1

instance : has_pow (ℕ → term L) ℕ := ⟨rewriting_sf_itr⟩

@[simp] lemma rewriting_sf_pow0 (s : ℕ → term L) : (s^0) = s := rfl
@[simp] lemma rewriting_sf_0 (s : ℕ → term L) (i : ℕ) : (s^(i + 1)) 0 = #0 := rfl
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

lemma rewriting_sf_perm {s : ℕ → term L} (h : ∀ n, ∃ m, s m = #n) : ∀ n, ∃ m, (s^1) m = #n :=
λ n, by { cases n, refine ⟨0, by simp⟩,
          rcases h n with ⟨m, e_m⟩, refine ⟨m+1, _⟩, simp[e_m] }

@[simp] def formula.arity : formula L → ℕ
| (formula.app p v) := finitary.Max 0 (λ i, (v i).arity)
| (t ≃₁ u) := max t.arity u.arity
| (p ⟶ q)  := max p.arity q.arity
| (⁻p)     := p.arity
| (∏₁ p)    := p.arity - 1

@[reducible] def sentence : formula L → Prop := λ p, p.arity = 0

@[simp] lemma formula.and_arity (p q : formula L) : (p ⊓ q).arity = max p.arity q.arity :=
by simp[has_inf.inf, formula.and]

@[simp] lemma formula.or_arity (p q : formula L) : (p ⊔ q).arity = max p.arity q.arity :=
by simp[has_sup.sup, formula.or]

@[simp] lemma formula.top_arity : (⊤ : formula L).arity = 0 :=
by simp[has_top.top, formula.top]

@[simp] lemma formula.bot_arity : (⊥ : formula L).arity = 0 :=
by simp[has_bot.bot, formula.bot]

@[simp] lemma formula.ex_arity (p : formula L) : (∐ p : formula L).arity = p.arity - 1 :=
by simp[has_exists_quantifier.ex, formula.ex]

lemma subst_pow (t : term L) (n i : ℕ) : ι[n ⇝ t]^i = ι[n + i ⇝ t^i] :=
begin
  induction i with i IH, { simp }, funext x,
  cases x; simp[←nat.add_one, ←add_assoc, IH],
  { have T : x < n + i ∨ x = n + i ∨ n + i < x, exact trichotomous _ _,
    cases T, { simp[T], }, cases T; simp[T, pow_add, term.pow_add],
    { have : 0 < x, exact pos_of_gt T, congr, exact (nat.pos_succ this).symm} }
end

lemma slide'_perm (t : term L) (k) : ∀ n, ∃ m, ι[k ⇝ t] m = #n := λ n,
by { have T : n < k ∨ k ≤ n, exact lt_or_ge _ _,
     cases T, refine ⟨n, by simp[T]⟩,
     { refine ⟨n + 1, _⟩, simp[show k < n + 1, from nat.lt_succ_iff.mpr T] }, }

lemma term.pow_rew_distrib (t : term L) (s : ℕ → term L) (i : ℕ): (t.rew s)^i = (t^i).rew (s^i) :=
by { induction i with i IH generalizong s i, { simp, },
     { simp[←nat.add_one, term.pow_add, rewriting_sf_itr.pow_add, rewriting_sf_itr.pow_eq',
         IH, term.pow_eq, term.nested_rew] } }

@[simp] lemma rew_subst_ι : (λ x, (((λ x, #(x + 1)) ^ 1) x).rew ι[0 ⇝ #0]  : ℕ → term L) = ι :=
by { funext x, cases x; simp }

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
| s (app p v) := app p (λ i, (v i).rew s)
| s (t ≃₁ u)  := (t.rew s) ≃ (u.rew s)
| s (p ⟶ q)  := p.rew s ⟶ q.rew s
| s (⁻p)      := ⁻(p.rew s)
| s (∏₁ p)   := ∏ (p.rew (s^1))

@[simp] lemma constant_rew (p : L.pr 0) (s : ℕ → term L) {v : finitary (term L) 0} : (❴p❵ v).rew s = ❴❴p❵❵ :=
by simp

@[simp] lemma unary_rew (p : L.pr 1) (s : ℕ → term L) (v : finitary (term L) 1) : (❴p❵ v).rew s = ❴p❵ ‹(v 0).rew s› :=
by simp; ext; simp

@[simp] lemma binary_rew (p : L.pr 2) (s : ℕ → term L) (v : finitary (term L) 2) :
  (❴p❵ v).rew s = (v 0).rew s ❴p❵ (v 1).rew s :=
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
@[simp] lemma ex_rew (p : formula L) (s) : (∐₁ p).rew s = ∐ p.rew (s^1) :=by simp[has_exists_quantifier.ex, ex]
@[simp] lemma top_rew (s) : (⊤ : formula L).rew s = ⊤ := by simp[has_top.top, formula.top]
@[simp] lemma bot_rew (s) : (⊥ : formula L).rew s = ⊥ := by simp[has_bot.bot, formula.bot]

@[simp] lemma rew_ι (p : formula L) : p.rew ι = p :=
by { induction p; try {simp[rew]}; try {simp*},
     have : ι^1 = ι,
     { funext n, cases n, rw[@rewriting_sf_0 L], simp }, rw[this], simp* }

@[simp] lemma conjunction'_rew {n} (P : finitary (formula L) n) (s) : (conjunction' n P).rew s = conjunction' n (λ i, (P i).rew s) :=
by { induction n with n IH; simp, simp[IH] }

instance : has_pow (formula L) ℕ := ⟨λ p i, p.rew (λ x, #(x + i))⟩

lemma pow_eq (p : formula L) (i : ℕ) : p^i = p.rew (λ x, #(x + i)) := rfl

@[simp] lemma formula_pow_0 (p : formula L) : p^0 = p := by simp[has_pow.pow]

@[simp] lemma app_pow {n} (p : L.pr n) (v : finitary (term L) n) (i : ℕ) : (❴p❵ v)^i = ❴p❵ (v^i) := rfl

@[simp] lemma constant_pow (c : L.pr 0) (i : ℕ) {v : finitary (term L) 0} : (app c v)^i = app c finitary.nil :=
by simp

@[simp] lemma unary_pow (p : L.pr 1) (i : ℕ) (t : term L) : (❴p❵ ‹t›)^i = ❴p❵ ‹t^i› :=
by simp[pow_eq]; refl

@[simp] lemma binary_pow (p : L.pr 2) (i : ℕ) (t₁ t₂ : term L) :
  (t₁ ❴p❵ t₂)^i = t₁^i ❴p❵ t₂^i :=
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
@[simp] lemma top_pow (i : ℕ) : (⊤ : formula L)^i = ⊤ := by simp[has_top.top, top]; refl
@[simp] lemma bot_pow (i : ℕ) : (⊥ : formula L)^i = ⊥ := by simp[has_bot.bot, bot]; refl
lemma fal_pow (p : formula L) (i : ℕ) : (∏₁ p)^i = ∏ p.rew (#0 ⌢ λ x, #(x + i + 1)) :=
by simp[formula.pow_eq, rewriting_sf_itr.pow_eq]

lemma nfal_pow (p : formula L) (n i : ℕ) :
  (nfal p n)^i = nfal (p.rew (λ x, if x < n then #x else #(x + i))) n :=
by { simp[formula.pow_eq, rewriting_sf_itr.pow_eq'], congr, funext x,
     by_cases C : x < n; simp[C], omega }

lemma nested_rew : ∀ (p : formula L) (s₀ s₁),
  (p.rew s₀).rew s₁ = p.rew (λ x, (s₀ x).rew s₁)
| (❴p❵ v) _ _ := by simp[rew]
| (t ≃₁ u)   _ _ := by simp[rew]
| (p ⟶ q)  _ _ := by simp[rew, nested_rew p, nested_rew q]
| (⁻p)      _ _ := by simp[rew]; refine nested_rew p _ _
| (∏₁ p)    _ _ := by { simp[rew, nested_rew p], congr,
    funext n, cases n; simp, simp[concat, rewriting_sf_itr.pow_eq, term.pow_eq] }

lemma rew_rew : ∀ (p : formula L) {s₀ s₁ : ℕ → term L},
  (∀ m, m < p.arity → s₀ m = s₁ m) → p.rew s₀ = p.rew s₁
| (❴p❵ v) _ _ h := by simp[rew, arity] at h ⊢; refine funext
    (λ i, term.rew_rew (v i) (λ m eqn, h _ $ lt_of_lt_of_le eqn (finitary.Max_le 0 _ i)))
| (t ≃₁ u)   _ _ h := by simp[rew, arity] at h ⊢;
    { refine ⟨term.rew_rew _ (λ _ e, h _ (or.inl e)), term.rew_rew _ (λ _ e, h _ (or.inr e))⟩ }
| (p ⟶ q)  _ _ h := by simp[rew, arity] at h ⊢;
    refine ⟨rew_rew _ (λ _ e, h _ (or.inl e)), rew_rew _ (λ _ e, h _ (or.inr e))⟩
| (⁻p)      _ _ h := by simp[rew, arity] at h ⊢; refine rew_rew _ h
| (∏₁ p)    _ _ h := by { simp[rew, arity] at h ⊢,
    refine rew_rew _ (λ m e, _), cases m; simp,
    cases p.arity, { exfalso, simp* at* },
    { simp at h, simp[h _ (nat.succ_lt_succ_iff.mp e)] } }

lemma pow_add (p : formula L) (i j : ℕ) : (p^i)^j = p^(i + j) :=
by simp[pow_eq, nested_rew, add_assoc]

@[simp] lemma sentence_rew {p : formula L} (h : sentence p) (s : ℕ → term L) : p.rew s = p :=
by { suffices : rew s p = rew ι p, { simp* },
     refine rew_rew _ _, simp[show p.arity = 0, from h] }

@[simp] lemma sentence_sf {p : formula L} (h : sentence p) (i : ℕ) : p^i = p :=
by simp[has_pow.pow, sentence_rew h]

@[simp] lemma sf_subst_eq (p : formula L) (t : term L) (i j : ℕ) (h : j ≤ i) : (p^(i + 1)).rew ι[j ⇝ t] = p^i :=
by { simp[has_pow.pow, nested_rew, h], congr, funext x,
     have : j < x + (i + 1), from nat.lt_add_left _ _ _ (nat.lt_succ_iff.mpr h),
     simp[this] }

lemma subst_sf_rew (p : formula L) (t : term L) (s : ℕ → term L) :
  (p.rew ι[0 ⇝ t]).rew s = (p.rew (s^1)).rew ι[0 ⇝ t.rew s] :=
by { simp[formula.rew, nested_rew], congr, ext n, cases n; simp }

@[simp] lemma sf_subst_eq_0 (p : formula L) (t) : (p^1).rew ι[0 ⇝ t] = p :=
by simp[nested_rew]

lemma pow_rew_distrib  (p : formula L) (s : ℕ → term L) (i : ℕ): (p.rew s)^i = (p^i).rew (s^i) :=
by { induction i with i IH generalizong s i, { simp },
     { simp[←nat.add_one, ←pow_add, ←rewriting_sf_itr.pow_add, IH, formula.pow_eq _ 1, nested_rew],
       refl } }

lemma total_rew_inv :
  ∀ (s : ℕ → term L) (h : ∀ n, ∃ m, s m = #n) (p : formula L), ∃ q : formula L, q.rew s = p
| s h (@app _ n p v) := by rcases classical.skolem.mp (λ i : fin n, @term.total_rew_inv _ s h (v i : term L)) with ⟨w, w_p⟩;
    refine ⟨❴p❵ w, by simp[w_p]⟩
| s h (t ≃₁ u)        := 
    by rcases term.total_rew_inv s h t with ⟨w₁, e_w₁⟩;
       rcases term.total_rew_inv s h u with ⟨w₂, e_w₂⟩; refine ⟨w₁ ≃ w₂, by simp[e_w₁, e_w₂]⟩
| s h (p ⟶ q)       := 
    by rcases total_rew_inv s h p with ⟨p', e_p'⟩;
       rcases total_rew_inv s h q with ⟨q', e_q'⟩; refine ⟨p' ⟶ q', by simp*⟩
| s h (⁻p)           := by rcases total_rew_inv s h p with ⟨q, e_q⟩; refine ⟨⁻q, by simp*⟩
| s h (∏₁ p)         := by rcases total_rew_inv _ (rewriting_sf_perm h) p with ⟨q, e_q⟩; refine ⟨∏q, by simp[e_q]⟩

@[simp] def Open : formula L → bool
| (❴p❵ v) := tt
| (t ≃₁ u)   := tt
| (p ⟶ q)  := p.Open && q.Open
| (⁻p)      := p.Open
| (∏₁ p)    := ff

@[simp] lemma op.and (p q : formula L) : (p ⊓ q).Open = p.Open && q.Open := rfl

@[simp] lemma op.or (p q : formula L) : (p ⊔ q).Open = p.Open && q.Open := rfl

@[simp] lemma nfal_arity : ∀ (n) (p : formula L), (nfal p n).arity = p.arity - n
| 0     p := by simp[formula.arity]
| (n+1) p := by {simp[formula.arity, nfal_arity n], exact (arity p).sub_sub _ _ }

lemma nfal_sentence (p : formula L) : sentence (nfal p p.arity) :=
by simp[sentence]

@[simp] lemma conjunction_arity {n} {v : finitary (formula L) n} :
  (conjunction' n v).arity = finitary.Max 0 (λ i, (v i).arity) :=
by { induction n with n IH; simp[finitary.Max, fin.add'], simp[IH] }

end formula

open term formula

class translation (L₁ : language.{u}) (L₂ : language.{u}) :=
(tr_pr : ∀ {n}, L₁.pr n → (fin n → term L₁) → formula L₂)
(tr_eq : term L₁ → term L₁ → formula L₂)

@[simp] def translation.tr {L₁ L₂ : language.{u}} [translation L₁ L₂] : formula L₁ → formula L₂
| (app p v) := translation.tr_pr p v
| ((t : term L₁) ≃ u)   := translation.tr_eq t u
| (p ⟶ q)  := translation.tr p ⟶ translation.tr q
| (⁻p)      := ⁻translation.tr p
| (∏ (p : formula L₁))   := ∏ translation.tr p

notation `tr[` p `]` := translation.tr p

def translation.tr_theory {L₁ L₂ : language.{u}} [translation L₁ L₂] (T : theory L₁) : theory L₂ := translation.tr '' T

instance : has_add language := ⟨λ L₁ L₂ : language.{u}, ⟨λ n, L₁.fn n ⊕ L₂.fn n, λ n, L₁.pr n ⊕ L₂.pr n⟩⟩ 

namespace language

variables {L₁ L₂ : language.{u}} 

def fn_to_add {n} (f : L₁.fn n) : (L₁ + L₂).fn n := sum.inl f

def pr_to_add {n} (p : L₁.pr n) : (L₁ + L₂).pr n := sum.inl p

@[simp] def add_tr_v1 : term L₁ → term (L₁ + L₂)
| (#x)       := #x
| (app f v)  := app (fn_to_add f) (λ i, add_tr_v1 (v i))

instance : translation L₁ (L₁ + L₂) :=
⟨λ n p v, app (pr_to_add p) (λ i, add_tr_v1 (v i)), λ t u, (add_tr_v1 t : term (L₁ + L₂)) ≃ add_tr_v1 u⟩

instance {n} : has_coe (L₁.fn n) ((L₁ + L₂).fn n) := ⟨fn_to_add⟩

instance {n} : has_coe (L₁.pr n) ((L₁ + L₂).pr n) := ⟨pr_to_add⟩

instance : has_coe (term L₁) (term (L₁ + L₂)) := ⟨add_tr_v1⟩

instance : has_coe (formula L₁) (formula (L₁ + L₂)) := ⟨translation.tr⟩

instance : has_coe (theory L₁) (theory (L₁ + L₂)) := ⟨λ T, translation.tr '' T⟩

instance [has_zero_symbol L₁] : has_zero_symbol (L₁ + L₂) := ⟨fn_to_add has_zero_symbol.zero⟩

instance [has_succ_symbol L₁] : has_succ_symbol (L₁ + L₂) := ⟨fn_to_add has_succ_symbol.succ⟩

instance [has_add_symbol L₁] : has_add_symbol (L₁ + L₂) := ⟨fn_to_add has_add_symbol.add⟩

instance [has_mul_symbol L₁] : has_mul_symbol (L₁ + L₂) := ⟨fn_to_add has_mul_symbol.mul⟩

instance [has_le_symbol L₁] : has_le_symbol (L₁ + L₂) := ⟨pr_to_add has_le_symbol.le⟩

instance [has_mem_symbol L₁] : has_mem_symbol (L₁ + L₂) := ⟨pr_to_add has_mem_symbol.mem⟩

@[simp] lemma add_tr_v1_var (n) : ((#n : term L₁) : term (L₁ + L₂)) = #n := rfl

lemma add_tr_v1_app {n} (f : L₁.fn n) (v : finitary (term L₁) n) :
  ((❨f❩ v : term L₁) : term (L₁ + L₂)) = ❨fn_to_add f❩ (λ i, add_tr_v1 (v i)) := by unfold_coes; simp

@[simp] lemma add_tr_v1_zero [has_zero_symbol L₁] :
  ((0 : term L₁) : term (L₁ + L₂)) = 0 := by { unfold has_zero.zero, unfold_coes, simp, refl }

@[simp] lemma add_tr_v1_succ [has_succ_symbol L₁] (t : term L₁) :
  ((Succ t : term L₁) : term (L₁ + L₂)) = Succ t :=
by { unfold has_succ.succ, unfold_coes, simp, split, { refl }, { ext; simp } }

@[simp] lemma add_tr_v1_numeral [has_zero_symbol L₁] [has_succ_symbol L₁] (n : ℕ) :
  ((n˙ : term L₁) : term (L₁ + L₂)) = n˙ :=
by induction n; simp[*, numeral]

@[simp] lemma add_tr_v1_add [has_add_symbol L₁] (t u : term L₁) :
  ((t + u : term L₁) : term (L₁ + L₂)) = t + u :=
by { unfold has_add.add, unfold_coes, simp, split, { refl }, { ext; simp } }

@[simp] lemma add_tr_v1_mul [has_mul_symbol L₁] (t u : term L₁) :
  ((t * u : term L₁) : term (L₁ + L₂)) = t * u :=
by { unfold has_mul.mul, unfold_coes, simp, split, { refl }, { ext; simp } }

@[simp] lemma add_tr_v1_le [has_le_symbol L₁] (t u : term L₁) :
  ((t ≼ u : formula L₁) : formula (L₁ + L₂)) = ((t : term (L₁ + L₂)) ≼ u) :=
by { unfold has_preceq.preceq, unfold_coes, simp[translation.tr_pr], split,
     { refl }, { ext; simp } }

@[simp] lemma add_tr_v1_mem [has_mem_symbol L₁] (t u : term L₁) :
  ((t ∊ u : formula L₁) : formula (L₁ + L₂)) = ((t : term (L₁ + L₂)) ∊ u) :=
by { unfold has_elem.elem, unfold_coes, simp[translation.tr_pr], split,
     { refl }, { ext; simp } }

@[simp] lemma add_tr_v1_arity : ∀ t : term L₁, (t : term (L₁ + L₂)).arity = t.arity
| (#x)    := rfl
| (❨f❩ v) := by simp[add_tr_v1_app, show ∀ i, (add_tr_v1 (v i)).arity = (v i).arity, from λ i, (add_tr_v1_arity (v i))]

end language

end fopl
