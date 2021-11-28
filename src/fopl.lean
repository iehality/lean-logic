import tactic lib

/- 焼き直し -/

universe u

namespace fopl

structure language : Type (u+1) :=
(fn : ℕ → Type u)
(pr : ℕ → Type u)

variables (L : language.{u})

inductive term (L : language.{u}) : Type u
| var {} : ℕ → term
| app    : ∀ {n : ℕ}, L.fn n → (fin n → term) → term

prefix `#`:max := term.var

instance : inhabited (term L) := ⟨#0⟩

inductive formula : Type u
| app   : ∀ {n : ℕ}, L.pr n → (fin n → term L) → formula
| equal : term L → term L → formula
| imply : formula → formula → formula
| neg   : formula → formula
| fal   : formula → formula

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

@[simp] lemma formula.equal.inj' (t₁ u₁ t₂ u₂ : term L) : (t₁ ≃ t₂ : formula L) = u₁ ≃ u₂ ↔ t₁ = u₁ ∧ t₂ = u₂ :=
⟨formula.equal.inj, by simp; exact congr_arg2 (≃)⟩

@[simp] lemma formula.imply.inj' (p₁ q₁ p₂ q₂ : formula L) : p₁ ⟶ p₂ = q₁ ⟶ q₂ ↔ p₁ = q₁ ∧ p₂ = q₂ :=
⟨formula.imply.inj, by simp; exact congr_arg2 (⟶)⟩

@[simp] lemma formula.neg.inj' (p q : formula L) : ⁻p = ⁻q ↔ p = q := ⟨formula.neg.inj, congr_arg _⟩

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
| (app f v) := app f (λ i, (v i).rew)

@[simp] lemma constant_rew (c : L.fn 0) (s : ℕ → term L) {v : finitary (term L) 0} : (app c v).rew s = app c finitary.nil :=
by simp

@[simp] lemma unary_rew (f : L.fn 1) (s : ℕ → term L) (t : term L) : (app f fin[t]).rew s = app f fin[t.rew s] :=
by simp[finitary.cons]

@[simp] lemma binary_rew (f : L.fn 2) (s : ℕ → term L) (t₁ t₂ : term L) :
  (app f fin[t₁, t₂]).rew s = app f fin[t₁.rew s, t₂.rew s] :=
by { simp, rw ←(finitary.fin2_eq (λ i, term.rew s (fin[t₁, t₂] i))), simp,
     simp[finitary.cons] }

instance : has_pow (term L) ℕ := ⟨λ t i, t.rew (λ x, #(x + i))⟩

instance finitary_pow {n : ℕ} : has_pow (fin n → term L) ℕ := ⟨λ v m, (λ i, (v i^m))⟩

lemma pow_eq (v : term L) (i : ℕ) : v^i = v.rew (λ x, #(x + i)) := rfl

@[simp] lemma finitary_pow_app {n} (v : fin n → term L) (i : fin n) (m : ℕ) : (v^m) i = (v i)^m := rfl

@[simp] lemma var_pow (n i : ℕ) : (#n : term L)^i = #(n + i) := rfl

@[simp] lemma app_pow {n} (f : L.fn n) (v : fin n → term L) (i : ℕ) : (app f v)^i = app f (v^i) := rfl

@[simp] lemma constant_pow (c : L.fn 0) (i : ℕ) {v : finitary (term L) 0} : (app c v)^i = app c finitary.nil :=
by simp

@[simp] lemma unary_pow (f : L.fn 1) (i : ℕ) (t : term L) : (app f fin[t])^i = app f fin[t^i] :=
by simp[pow_eq]

@[simp] lemma binary_pow (f : L.fn 2) (i : ℕ) (t₁ t₂ : term L) :
  (app f fin[t₁, t₂])^i = app f fin[t₁^i, t₂^i] :=
by simp[pow_eq]

@[simp] def arity : term L → ℕ
| (#n)       := n + 1
| (app f v)  := finitary.Max 0 (λ i, (v i).arity)

@[simp] lemma constant_arity (c : L.fn 0) {v : finitary (term L) 0} : (app c v).arity = 0 :=
by simp

@[simp] lemma unary_arity (f : L.fn 1) (t : term L) : (app f fin[t]).arity = t.arity :=
by simp[finitary.cons, finitary.Max]

@[simp] lemma binary_arity (f : L.fn 2) (t₁ t₂ : term L) :
  (app f fin[t₁, t₂]).arity = max t₁.arity t₂.arity :=
by { simp[finitary.Max, finitary.cons, fin.add'], exact max_comm _ _ }

@[simp] lemma nested_rew (s₀ s₁) : ∀ (t : term L),
  (t.rew s₀).rew s₁ = t.rew (λ x, (s₀ x).rew s₁)
| (#x)       := by simp[rew]
| (app f v)  := by simp[rew, nested_rew]

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
    refine ⟨app f w, by simp[w_eqn]⟩

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

@[simp] lemma constant_arity (c : L.pr 0) {v : finitary (term L) 0} : (app c v).arity = 0 :=
by simp

@[simp] lemma unary_arity (p : L.pr 1) (t : term L) : (app p fin[t]).arity = t.arity :=
by simp[finitary.cons, finitary.Max]

@[simp] lemma binary_arity (p : L.pr 2) (t₁ t₂ : term L) :
  (app p fin[t₁, t₂]).arity = max t₁.arity t₂.arity :=
by { simp[finitary.Max, finitary.cons, fin.add'], exact max_comm _ _ }

@[simp] def rew : (ℕ → term L) → formula L → formula L
| s (app p v) := app p (λ i, (v i).rew s)
| s (t ≃₁ u)  := (t.rew s) ≃ (u.rew s)
| s (p ⟶ q)  := p.rew s ⟶ q.rew s
| s (⁻p)      := ⁻(p.rew s)
| s (∏₁ p)   := ∏ (p.rew (s^1))

@[simp] lemma constant_rew (c : L.pr 0) (s : ℕ → term L) {v : finitary (term L) 0} : (app c v).rew s = app c finitary.nil :=
by simp

@[simp] lemma unary_rew (p : L.pr 1) (s : ℕ → term L) (t : term L) : (app p fin[t]).rew s = app p fin[t.rew s] :=
by simp[finitary.cons]

@[simp] lemma binary_rew (p : L.pr 2) (s : ℕ → term L) (t₁ t₂ : term L) :
  (app p fin[t₁, t₂]).rew s = app p fin[t₁.rew s, t₂.rew s] :=
by { simp, rw ←(finitary.fin2_eq (λ i, term.rew s (fin[t₁, t₂] i))), simp,
     simp[finitary.cons] }

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

@[simp] lemma app_pow {n} (p : L.pr n) (v : finitary (term L) n) (i : ℕ) : (app p v)^i = app p (v^i) := rfl

@[simp] lemma constant_pow (c : L.pr 0) (i : ℕ) {v : finitary (term L) 0} : (app c v)^i = app c finitary.nil :=
by simp

@[simp] lemma unary_pow (p : L.pr 1) (i : ℕ) (t : term L) : (app p fin[t])^i = app p fin[t^i] :=
by simp[pow_eq]; refl

@[simp] lemma binary_pow (p : L.pr 2) (i : ℕ) (t₁ t₂ : term L) :
  (app p fin[t₁, t₂])^i = app p fin[t₁^i, t₂^i] :=
by simp[pow_eq]; refl

@[simp] lemma eq_pow (t u : term L) (i : ℕ) : (t ≃₁ u)^i = (t^i) ≃ (u^i) := rfl
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
| (app p v) _ _ := by simp[rew]
| (t ≃₁ u)   _ _ := by simp[rew]
| (p ⟶ q)  _ _ := by simp[rew, nested_rew p, nested_rew q]
| (⁻p)      _ _ := by simp[rew]; refine nested_rew p _ _
| (∏₁ p)    _ _ := by { simp[rew, nested_rew p], congr,
    funext n, cases n; simp, simp[concat, rewriting_sf_itr.pow_eq, term.pow_eq] }

lemma rew_rew : ∀ (p : formula L) {s₀ s₁ : ℕ → term L},
  (∀ m, m < p.arity → s₀ m = s₁ m) → p.rew s₀ = p.rew s₁
| (app p v) _ _ h := by simp[rew, arity] at h ⊢; refine funext
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
    refine ⟨app p w, by simp[w_p]⟩
| s h (t ≃₁ u)        := 
    by rcases term.total_rew_inv s h t with ⟨w₁, e_w₁⟩;
       rcases term.total_rew_inv s h u with ⟨w₂, e_w₂⟩; refine ⟨w₁ ≃ w₂, by simp[e_w₁, e_w₂]⟩
| s h (p ⟶ q)       := 
    by rcases total_rew_inv s h p with ⟨p', e_p'⟩;
       rcases total_rew_inv s h q with ⟨q', e_q'⟩; refine ⟨p' ⟶ q', by simp*⟩
| s h (⁻p)           := by rcases total_rew_inv s h p with ⟨q, e_q⟩; refine ⟨⁻q, by simp*⟩
| s h (∏₁ p)         := by rcases total_rew_inv _ (rewriting_sf_perm h) p with ⟨q, e_q⟩; refine ⟨∏q, by simp[e_q]⟩

@[simp] def Open : formula L → bool
| (app p v) := tt
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

@[simp] def add_tr_v1 : term L₁ → term (L₁ + L₂)
| (#x)       := #x
| (app f v)  := app (sum.inl f) (λ i, add_tr_v1 (v i))

instance : translation L₁ (L₁ + L₂) :=
⟨λ n p v, app (sum.inl p) (λ i, add_tr_v1 (v i)), λ t u, (add_tr_v1 t : term (L₁ + L₂)) ≃ add_tr_v1 u⟩

instance {L₁ L₂ : language.{u}} {n} : has_coe (L₁.fn n) ((L₁ + L₂).fn n) := ⟨sum.inl⟩

instance {L₁ L₂ : language.{u}} {n} : has_coe (L₁.pr n) ((L₁ + L₂).pr n) := ⟨sum.inl⟩

instance {L₁ L₂ : language.{u}} : has_coe (term L₁) (term (L₁ + L₂)) := ⟨add_tr_v1⟩

instance {L₁ L₂ : language.{u}} : has_coe (formula L₁) (formula (L₁ + L₂)) := ⟨translation.tr⟩

instance {L₁ L₂ : language.{u}} : has_coe (theory L₁) (theory (L₁ + L₂)) := ⟨λ T, translation.tr '' T⟩

@[simp] lemma add_tr_v1_app_var (n) : ((#n : term L₁) : term (L₁ + L₂)) = #n := rfl

@[simp] lemma add_tr_v1_app {n} (f : L₁.fn n) (v : finitary (term L₁) n) :
  ((app f v : term L₁) : term (L₁ + L₂)) = app (f : (L₁ + L₂).fn n) (λ i, (v i : term (L₁ + L₂))) := rfl

end language

end fopl
