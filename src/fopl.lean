import tactic lib

/- 焼き直し -/

universe u

namespace fopl

structure language : Type (u+1) :=
(fn : ℕ → Type u)
(pr : ℕ → Type u)

variables (L : language.{u})

inductive vecterm (L : language.{u}) : ℕ → Type u
| cons   : ∀ {n : ℕ}, vecterm 0 → vecterm n → vecterm (n+1)
| var {} : ℕ → vecterm 0
| const  : L.fn 0 → vecterm 0
| app    : ∀ {n : ℕ}, L.fn (n+1) → vecterm n → vecterm 0

prefix `#`:max := vecterm.var

notation h ` ::: ` t  := vecterm.cons h t

@[reducible] def term : Type u := vecterm L 0

inductive formula : Type u
| const : L.pr 0 → formula
| app   : ∀ {n : ℕ}, L.pr (n+1) → vecterm L n → formula
| equal : term L → term L → formula
| imply : formula → formula → formula
| neg   : formula → formula
| fal   : formula → formula

infix ` =̇ `:90 := formula.equal
infixr ` →̇ `:78 := formula.imply
prefix `¬̇`:94 := formula.neg
prefix `∀̇ `:90 := formula.fal

def theory (L : language) := set (formula L)

notation `theory `L:max := set (formula L)

variables {L}

@[reducible] def formula.neq (t : term L) (u : term L) : formula L := ¬̇(t =̇ u)
infix ` ≠̇ `:90 := formula.neq

def formula.and (p : formula L) (q : formula L) : formula L := ¬̇(p →̇ ¬̇q)
infix ` ⩑ `:86 := formula.and

def formula.or (p : formula L) (q : formula L) : formula L := ¬̇p →̇ q
infix ` ⩒ `:82 := formula.or

def formula.iff (p : formula L) (q : formula L) : formula L := (p →̇ q) ⩑ (q →̇ p)
infix ` ↔̇ `:74 := formula.iff

def formula.ex (p : formula L) : formula L := ¬̇∀̇¬̇p
prefix `∃̇ `:90 := formula.ex

@[irreducible] def formula.top : formula L := ∀̇(#0 =̇ #0)
notation `⊤̇` := formula.top

@[irreducible] def formula.bot : formula L := ¬̇⊤̇
notation `⊥̇` := formula.bot

instance : inhabited (formula L) := ⟨⊥̇⟩

@[simp] def nfal (p : formula L) : ℕ → formula L
| 0     := p
| (n+1) := ∀̇ (nfal n)

@[simp] lemma nfal_fal (p : formula L) (i : ℕ) : nfal (∀̇  p) i = ∀̇ (nfal p i) :=
by { induction i with i IH; simp, exact IH }

@[reducible] def ι : ℕ → term L := vecterm.var

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

namespace vecterm

@[simp] def rew (s : ℕ → term L) : ∀ {n}, vecterm L n → vecterm L n
| _ (cons a v) := cons a.rew v.rew
| _ (#x)       := s x
| _ (const c)  := const c
| _ (app f v)  := app f v.rew

instance {n : ℕ} : has_pow (vecterm L n) ℕ := ⟨λ t i, t.rew (λ x, #(x + i))⟩

lemma pow_eq {n : ℕ} (v : vecterm L n) (i : ℕ) : v^i = v.rew (λ x, #(x + i)) := rfl

@[simp] lemma cons_pow (a : term L) {n} (v : vecterm L n) (i : ℕ) : (cons a v)^i = cons (a^i) (v^i) := rfl

@[simp] lemma var_pow (n i : ℕ) : (#n : term L)^i = #(n + i) := rfl

@[simp] lemma const_pow (c : L.fn 0) (i : ℕ) : (const c)^i = const c := rfl

@[simp] lemma app_pow {n} (f : L.fn (n+1)) (v : vecterm L n) (i : ℕ) : (app f v)^i = app f (v^i) := rfl

def arity : ∀ {n}, vecterm L n → ℕ
| _ (cons a v) := max a.arity v.arity
| _ (#n)       := n + 1
| _ (const c)  := 0
| _ (app f v)  := v.arity

@[simp] lemma nested_rew (s₀ s₁) : ∀ {n} (t : vecterm L n),
  (t.rew s₀).rew s₁ = t.rew (λ x, (s₀ x).rew s₁)
| _ (cons a v) := by simp[rew, nested_rew]
| _ (#x)       := by simp[rew]
| _ (const c)  := by simp[rew]
| _ (app f v)  := by simp[rew, nested_rew]

@[simp] lemma rew_ι {n} (t : vecterm L n) : t.rew ι = t :=
by induction t; simp[rew]; simp*

lemma rew_rew {s₀ s₁ : ℕ → term L} : ∀ {n} (t : vecterm L n),
  (∀ m, m < t.arity → s₀ m = s₁ m) → t.rew s₀ = t.rew s₁
| _ (cons a v) h := by simp[rew, arity] at h ⊢;
    refine ⟨rew_rew _ (λ _ e, h _ (or.inl e)), rew_rew _ (λ _ e, h _ (or.inr e))⟩
| _ (#x)       h := by simp[rew, arity] at h ⊢; simp*
| _ (const c)  _ := rfl
| _ (app f v)  h := by simp[rew, arity] at h ⊢; refine rew_rew _ h

lemma pow_add {n} (v : vecterm L n) (i j : ℕ) : (v^i)^j = v^(i + j) :=
by simp[pow_eq, nested_rew, add_assoc]

@[simp] lemma arity0_rew {n} {v : vecterm L n} (h : v.arity = 0) (s : ℕ → term L) : v.rew s = v :=
by { suffices : rew s v = rew ι v, { simp* },
     refine rew_rew _ _, simp[h] }

@[simp] lemma arity0_sf {n} {v : vecterm L n} (h : v.arity = 0) (i : ℕ) : v^i = v := by simp[has_pow.pow, h]

lemma total_rew_inv :
  ∀ {n} (p : vecterm L n) {s : ℕ → term L} (h : ∀ n, ∃ m, s m = #n), ∃ q : vecterm L n, q.rew s = p
| (n+1) (cons a v) s h := by {
    rcases total_rew_inv a h with ⟨qa, IH_qa⟩,
    rcases total_rew_inv v h with ⟨qv, IH_qv⟩,
    refine ⟨cons qa qv, _⟩, simp[IH_qa, IH_qv] }
| _     (#x)       s h := by rcases h x with ⟨q, h_q⟩; refine ⟨#q, _⟩; simp[h_q]
| _     (const c)  s h := ⟨const c, rfl⟩
| _     (app f v)  s h := by rcases total_rew_inv v h with ⟨q, IH_q⟩; refine ⟨app f q, _⟩; simp[IH_q]

@[simp] lemma pow_0 {n} (t : vecterm L n) : t^0 = t := by simp[has_pow.pow]
@[simp] lemma term_pow_0 (t : term L) : t^0 = t := by simp[has_pow.pow]

@[simp] lemma sf_subst_eq {n : ℕ} (v : vecterm L n) (t : term L) (i j : ℕ) (h : j ≤ i) :
  (v^(i + 1)).rew (ι [j ⇝ t]) = v^i :=
by { simp[has_pow.pow, rew, nested_rew, h], congr, funext x,
     have : j < x + (i + 1), from nat.lt_add_left _ _ _ (nat.lt_succ_iff.mpr h),
     simp[this] }

@[simp] lemma concat_pow_eq {n : ℕ} (v : vecterm L n) (t : term L) (s : ℕ → term L) :
  (v^1).rew (t ⌢ s) = v.rew s :=
by simp[concat, rew, pow_eq, nested_rew]

end vecterm

lemma term.pow_eq (v : term L) (i : ℕ) : v^i = v.rew (λ x, #(x + i)) := rfl

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
     by_cases C : x < i; simp[C, vecterm.pow_add] }


lemma rewriting_sf_perm {s : ℕ → term L} (h : ∀ n, ∃ m, s m = #n) : ∀ n, ∃ m, (s^1) m = #n :=
λ n, by { cases n, refine ⟨0, by simp⟩,
          rcases h n with ⟨m, e_m⟩, refine ⟨m+1, _⟩, simp[e_m] }

def formula.arity : formula L → ℕ
| (formula.const c) := 0
| (formula.app p v) := v.arity
| (t =̇ u)           := max t.arity u.arity
| (p →̇ q)          := max p.arity q.arity
| (¬̇p)              := p.arity
| (∀̇ p)             := p.arity - 1

@[reducible] def sentence : formula L → Prop := λ p, p.arity = 0

lemma subst_pow (t : term L) (n i : ℕ) : ι[n ⇝ t]^i = ι[n + i ⇝ t^i] :=
begin
  induction i with i IH, { simp }, funext x,
  cases x; simp[←nat.add_one, ←add_assoc, IH],
  { have T : x < n + i ∨ x = n + i ∨ n + i < x, exact trichotomous _ _,
    cases T, { simp[T], }, cases T; simp[T, pow_add, vecterm.pow_add],
    { have : 0 < x, exact pos_of_gt T, congr, exact (nat.pos_succ this).symm} }
end

lemma slide'_perm (t : term L) (k) : ∀ n, ∃ m, ι[k ⇝ t] m = #n := λ n,
by { have T : n < k ∨ k ≤ n, exact lt_or_ge _ _,
     cases T, refine ⟨n, by simp[T]⟩,
     { refine ⟨n + 1, _⟩, simp[show k < n + 1, from nat.lt_succ_iff.mpr T] }, }

lemma vecterm.pow_rew_distrib {n} (v : vecterm L n) (s : ℕ → term L) (i : ℕ): (v.rew s)^i = (v^i).rew (s^i) :=
by { induction i with i IH generalizong s i, { simp, },
     { simp[←nat.add_one, vecterm.pow_add, rewriting_sf_itr.pow_add, rewriting_sf_itr.pow_eq',
         IH, vecterm.pow_eq, vecterm.nested_rew] } }

@[simp] lemma rew_subst_ι : (λ x, (((λ x, #(x + 1)) ^ 1) x).rew ι[0 ⇝ #0]  : ℕ → term L) = ι :=
by { funext x, cases x; simp }

namespace formula

@[simp] def rew : (ℕ → term L) → formula L → formula L
| _ (const c) := const c 
| s (app p v) := app p (v.rew s)
| s (t =̇ u)   := (t.rew s) =̇ (u.rew s)
| s (p →̇ q)  := p.rew s →̇ q.rew s
| s (¬̇p)      := ¬̇(p.rew s)
| s (∀̇ p)     := ∀̇ (p.rew (s^1))

@[simp] lemma and_rew (p q : formula L) (s) : (p ⩑ q).rew s = p.rew s ⩑ q.rew s :=by simp[and, formula.rew]
@[simp] lemma or_rew (p q : formula L) (s) : (p ⩒ q).rew s = p.rew s ⩒ q.rew s :=by simp[or, formula.rew]
@[simp] lemma iff_rew (p q : formula L) (s) : (p ↔̇ q).rew s = p.rew s ↔̇ q.rew s :=by simp[iff, formula.rew]
@[simp] lemma nfal_rew (p : formula L) (i : ℕ) (s) : (nfal p i).rew s = nfal (p.rew (s^i)) i :=
by { induction i with i IH generalizing s, { simp },
     simp[←nat.add_one, IH, rewriting_sf_itr.pow_add, add_comm 1 i] }
@[simp] lemma ex_rew (p : formula L) (s) : (∃̇p).rew s = ∃̇p.rew (s^1) :=by simp[ex]
@[simp] lemma top_rew (s) : (⊤̇ : formula L).rew s = ⊤̇ := by simp[formula.top, formula.rew, vecterm.rew]
@[simp] lemma bot_rew (s) : (⊥̇ : formula L).rew s = ⊥̇ := by simp[formula.bot, formula.rew, vecterm.rew]

@[simp] lemma rew_ι (p : formula L) : p.rew ι = p :=
by { induction p; simp[rew]; try {simp*},
     have : ι^1 = ι,
     { funext n, cases n, rw[@rewriting_sf_0 L], simp }, rw[this], simp* }

instance : has_pow (formula L) ℕ := ⟨λ p i, p.rew (λ x, #(x + i))⟩

lemma pow_eq (p : formula L) (i : ℕ) : p^i = p.rew (λ x, #(x + i)) := rfl

@[simp] lemma formula_pow_0 (p : formula L) : p^0 = p := by simp[has_pow.pow]

@[simp] lemma const_pow (c : L.pr 0) (i : ℕ) : (const c)^i = const c := rfl
@[simp] lemma app_pow {n} (p : L.pr (n+1)) (v : vecterm L n) (i : ℕ) : (app p v)^i = app p (v^i) := rfl
@[simp] lemma eq_pow (t u : term L) (i : ℕ) : (t =̇ u)^i = (t^i) =̇ (u^i) := rfl
@[simp] lemma imply_pow (p q : formula L) (i : ℕ) : (p →̇ q)^i = p^i →̇ q^i := rfl
@[simp] lemma neg_pow (p : formula L) (i : ℕ) : (¬̇p)^i = ¬̇(p^i) := rfl
@[simp] lemma and_pow (p q : formula L) (i : ℕ) : (p ⩑ q)^i = (p^i) ⩑ (q^i) := rfl
@[simp] lemma or_pow (p q : formula L) (i : ℕ) : (p ⩒ q)^i = (p^i) ⩒ (q^i) := rfl
@[simp] lemma top_pow (i : ℕ) : (⊤̇ : formula L)^i = ⊤̇ := by simp[top]; refl
@[simp] lemma bot_pow (i : ℕ) : (⊥̇ : formula L)^i = ⊥̇ := by simp[bot]; refl
lemma fal_pow (p : formula L) (i : ℕ) : (∀̇ p)^i = ∀̇ p.rew (#0 ⌢ λ x, #(x + i + 1)) :=
by simp[formula.pow_eq, rewriting_sf_itr.pow_eq]

lemma nfal_pow (p : formula L) (n i : ℕ) :
  (nfal p n)^i = nfal (p.rew (λ x, if x < n then #x else #(x + i))) n :=
by { simp[formula.pow_eq, rewriting_sf_itr.pow_eq'], congr, funext x,
     by_cases C : x < n; simp[C], omega }

lemma nested_rew : ∀ (p : formula L) (s₀ s₁),
  (p.rew s₀).rew s₁ = p.rew (λ x, (s₀ x).rew s₁)
| (const c) _ _ := rfl
| (app p v) _ _ := by simp[rew]
| (t =̇ u)   _ _ := by simp[rew]
| (p →̇ q)  _ _ := by simp[rew]; refine ⟨nested_rew p _ _, nested_rew q _ _⟩
| (¬̇p)      _ _ := by simp[rew]; refine nested_rew p _ _
| (∀̇ p)     _ _ := by { simp[rew, nested_rew p], congr,
    funext n, cases n; simp[vecterm.rew], simp[concat, rewriting_sf_itr.pow_eq, vecterm.pow_eq] }

lemma rew_rew : ∀ (p : formula L) {s₀ s₁ : ℕ → term L},
  (∀ m, m < p.arity → s₀ m = s₁ m) → p.rew s₀ = p.rew s₁
| (const c) _ _ _ := rfl
| (app p v) _ _ h := by simp[rew, arity] at h ⊢; refine vecterm.rew_rew _ h
| (t =̇ u)   _ _ h := by simp[rew, arity] at h ⊢;
    refine ⟨vecterm.rew_rew _ (λ _ e, h _ (or.inl e)), vecterm.rew_rew _ (λ _ e, h _ (or.inr e))⟩
| (p →̇ q)  _ _ h := by simp[rew, arity] at h ⊢;
    refine ⟨rew_rew _ (λ _ e, h _ (or.inl e)), rew_rew _ (λ _ e, h _ (or.inr e))⟩
| (¬̇p)      _ _ h := by simp[rew, arity] at h ⊢; refine rew_rew _ h
| (∀̇p)      _ _ h := by { simp[rew, arity] at h ⊢,
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
by { simp[has_pow.pow, vecterm.rew, nested_rew, h], congr, funext x,
     have : j < x + (i + 1), from nat.lt_add_left _ _ _ (nat.lt_succ_iff.mpr h),
     simp[this] }

lemma subst_sf_rew (p : formula L) (t : term L) (s : ℕ → term L) :
  (p.rew ι[0 ⇝ t]).rew s = (p.rew (s^1)).rew ι[0 ⇝ t.rew s] :=
by { simp[formula.rew, vecterm.rew, nested_rew], congr, ext n, cases n; simp }

@[simp] lemma sf_subst_eq_0 (p : formula L) (t) : (p^1).rew ι[0 ⇝ t] = p :=
by simp[vecterm.rew, nested_rew]

lemma pow_rew_distrib  (p : formula L) (s : ℕ → term L) (i : ℕ): (p.rew s)^i = (p^i).rew (s^i) :=
by { induction i with i IH generalizong s i, { simp },
     { simp[←nat.add_one, ←pow_add, ←rewriting_sf_itr.pow_add, IH, formula.pow_eq _ 1, nested_rew],
       refl } }

lemma total_rew_inv :
  ∀ (p : formula L) {s : ℕ → term L} (h : ∀ n, ∃ m, s m = #n), ∃ q : formula L, q.rew s = p
| (const c) s h := ⟨const c, rfl⟩
| (app p v) s h := by rcases vecterm.total_rew_inv v h with ⟨u, h_u⟩; refine ⟨app p u, by simp[h_u]⟩
| (t =̇ u)   s h := 
    by rcases vecterm.total_rew_inv t h with ⟨w₁, e_w₁⟩;
       rcases vecterm.total_rew_inv u h with ⟨w₂, e_w₂⟩; refine ⟨w₁ =̇ w₂, by simp[e_w₁, e_w₂]⟩
| (p →̇ q)  s h := 
    by rcases total_rew_inv p h with ⟨p', e_p'⟩;
       rcases total_rew_inv q h with ⟨q', e_q'⟩; refine ⟨p' →̇ q', by simp*⟩
| (¬̇p)      s h := by rcases total_rew_inv p h with ⟨q, e_q⟩; refine ⟨¬̇q, by simp*⟩
| (∀̇p)      s h := by rcases total_rew_inv p (rewriting_sf_perm h) with ⟨q, e_q⟩; refine ⟨∀̇q, by simp[e_q]⟩

@[simp] def Open : formula L → bool
| (const c) := tt
| (app p v) := tt
| (t =̇ u)   := tt
| (p →̇ q)  := p.Open && q.Open
| (¬̇p)      := p.Open
| (∀̇p)      := ff

@[simp] lemma op.and (p q : formula L) : (p ⩑ q).Open = p.Open && q.Open := rfl

@[simp] lemma op.or (p q : formula L) : (p ⩒ q).Open = p.Open && q.Open := rfl

lemma nfal_arity : ∀ (n) (p : formula L), (nfal p n).arity = p.arity - n
| 0     p := by simp[formula.arity]
| (n+1) p := by {simp[formula.arity, nfal_arity n], exact (arity p).sub_sub _ _ }

lemma nfal_sentence (p : formula L) : sentence (nfal p p.arity) :=
by { have := nfal_arity p.arity p, simp at*, refine this }

end formula

open vecterm formula

class translation (L₁ : language.{u}) (L₂ : language.{u}) :=
(tr_const : L₁.pr 0 → formula L₂)
(tr_pr : ∀ {n}, L₁.pr (n + 1) → vecterm L₁ n → formula L₂)
(tr_eq : term L₁ → term L₁ → formula L₂)

@[simp] def translation.tr {L₁ L₂ : language.{u}} [translation L₁ L₂] : formula L₁ → formula L₂
| (const c) := translation.tr_const c 
| (app p v) := translation.tr_pr p v
| (t =̇ u)   := translation.tr_eq t u
| (p →̇ q)  := translation.tr p →̇ translation.tr q
| (¬̇p)      := ¬̇translation.tr p
| (∀̇p)      := ∀̇ translation.tr p

notation `tr[` p `]` := translation.tr p

def translation.tr_theory {L₁ L₂ : language.{u}} [translation L₁ L₂] (T : theory L₁) : theory L₂ := translation.tr '' T



instance : has_add language := ⟨λ L₁ L₂ : language.{u}, ⟨λ n, L₁.fn n ⊕ L₂.fn n, λ n, L₁.pr n ⊕ L₂.pr n⟩⟩

namespace language

variables {L₁ L₂ : language.{u}} 

@[simp] def add_tr_v1 : ∀ {n}, vecterm L₁ n → vecterm (L₁ + L₂) n
| _ (cons a v) := add_tr_v1 a ::: add_tr_v1 v
| _ (#x)       := #x
| _ (const c)  := const (sum.inl c)
| _ (app f v)  := app (sum.inl f) (add_tr_v1 v)

instance : translation L₁ (L₁ + L₂) :=
⟨λ c, const (sum.inl c), λ n p v, app (sum.inl p) (add_tr_v1 v), λ t u, add_tr_v1 t =̇ add_tr_v1 u⟩

instance {L₁ L₂ : language.{u}} : has_coe (term L₁) (term (L₁ + L₂)) := ⟨add_tr_v1⟩
instance {L₁ L₂ : language.{u}} : has_coe (formula L₁) (formula (L₁ + L₂)) := ⟨translation.tr⟩
instance {L₁ L₂ : language.{u}} : has_coe (theory L₁) (theory (L₁ + L₂)) := ⟨λ T, translation.tr '' T⟩

end language

end fopl

@[simp] def dvector.to_vecterm {L : fopl.language} : ∀ {n} (v : dvector (fopl.term L) (n+1)), fopl.vecterm L n
| 0     (t :: dvector.nil) := t
| (n+1) (t :: ts)          := fopl.vecterm.cons t ts.to_vecterm 
