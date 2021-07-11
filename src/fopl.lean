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

@[reducible] def term : Type u := vecterm L 0

inductive formula : Type u
| const : L.pr 0 → formula
| app   : ∀ {n : ℕ}, L.pr (n+1) → vecterm L n → formula
| equal : term L → term L → formula
| imply : formula → formula → formula
| neg : formula → formula
| fal : formula → formula

infix ` =̇ `:90 := formula.equal
infixr ` →̇ `:78 := formula.imply
prefix `¬̇`:94 := formula.neg
prefix `∀̇`:90 := formula.fal

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
prefix `Ė`:90 := formula.ex

@[irreducible] def formula.top : formula L := ∀̇(#0 =̇ #0)
notation `⊤̇` := formula.top

@[irreducible] def formula.bot : formula L := ¬̇⊤̇
notation `⊥̇` := formula.bot

instance : inhabited (formula L) := ⟨⊥̇⟩

@[simp] def nfal (p : formula L) : ℕ → formula L
| 0     := p
| (n+1) := ∀̇(nfal n)

@[simp] def slide {α : Type*} (a : α) (s : ℕ → α) : ℕ → α
| 0     := a
| (m+1) := s m

@[simp] def embed {α : Type*} (a : α) (s : ℕ → α) : ℕ → α
| 0     := a
| (m+1) := s (m+1)

infixr ` ^ˢ `:max := slide

infixr ` ^ᵉ `:max := embed

@[reducible] def idvar : ℕ → term L := λ x, #x

namespace vecterm

@[simp] def rew (s : ℕ → term L) : ∀ {n}, vecterm L n → vecterm L n
| _ (cons a v) := cons a.rew v.rew
| _ (#x)       := s x
| _ (const c)  := const c
| _ (app f v)  := app f v.rew

@[reducible] def sf_itr (m) {n} (t : vecterm L n) : vecterm L n := t.rew (λ x, #(x+m))

@[reducible] def sf {n} (t : vecterm L n) : vecterm L n := t.rew (λ x, #(x+1))

@[simp] lemma cons_sf (a : term L) {n} (v : vecterm L n) : (cons a v).sf = cons a.sf v.sf := rfl
@[simp] lemma var_sf (n) : (#n : term L).sf = #(n + 1) := rfl
@[simp] lemma const_sf (c : L.fn 0) : (const c).sf = const c := rfl
@[simp] lemma app_sf {n} (f : L.fn (n+1)) (v : vecterm L n) : (app f v).sf = app f v.sf := rfl

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

@[simp] lemma sf_rew_eq {n} (t : vecterm L n) (t₀ : term L) (s : ℕ → term L) :
  t.sf.rew (t₀ ^ˢ s) = t.rew s :=
by cases t; by simp[rew, sf]

@[simp] lemma rew_idvar {n} (t : vecterm L n) : t.rew idvar = t :=
by induction t; simp[rew]; simp*

lemma rew_rew {s₀ s₁ : ℕ → term L} : ∀ {n} (t : vecterm L n),
  (∀ m, m < t.arity → s₀ m = s₁ m) → t.rew s₀ = t.rew s₁
| _ (cons a v) h := by simp[rew, arity] at h ⊢;
    refine ⟨rew_rew _ (λ _ e, h _ (or.inl e)), rew_rew _ (λ _ e, h _ (or.inr e))⟩
| _ (#x)       h := by simp[rew, arity] at h ⊢; simp*
| _ (const c)  _ := rfl
| _ (app f v)  h := by simp[rew, arity] at h ⊢; refine rew_rew _ h

@[simp] lemma sf_rew {n} (t : vecterm L n) (u) (s) : t.sf.rew (u ^ˢ s) = t.rew s :=
by simp[vecterm.sf, vecterm.rew]

@[simp] lemma arity0_rew {n} {v : vecterm L n} (h : v.arity = 0) (s : ℕ → term L) : v.rew s = v :=
by { suffices : rew s v = rew idvar v, { simp* },
     refine rew_rew _ _, simp[h] }

@[simp] lemma arity0_sf {n} {v : vecterm L n} (h : v.arity = 0) : v.sf = v := by simp[vecterm.sf, arity0_rew h]

end vecterm

def rewriting_sf (s : ℕ → term L) : ℕ → term L := #0 ^ˢ λ n, (s n).sf
notation s`⁺¹`:1200 := fopl.rewriting_sf s

@[simp] lemma rewriting_sf_0 (s : ℕ → term L) : s⁺¹ 0 = #0 := rfl
@[simp] lemma rewriting_sf_succ (s : ℕ → term L) (n : ℕ) : s⁺¹ (n.succ) = (s n).sf := rfl

@[simp] def rewriting_sf_itr (s : ℕ → term L) : ℕ → ℕ → term L
| 0     := s
| (n+1) := (rewriting_sf_itr n)⁺¹

instance : has_pow (ℕ → term L) ℕ := ⟨rewriting_sf_itr⟩

@[simp] lemma rewriting_sf_itr_0 (s : ℕ → term L) : s^0 = s := rfl
@[simp] lemma rewriting_sf_itr_succ (s : ℕ → term L) (n) : s^(n+1) = (s^n)⁺¹ := rfl

def formula.arity : formula L → ℕ
| (formula.const c) := 0
| (formula.app p v) := v.arity
| (t =̇ u)           := max t.arity u.arity
| (p →̇ q)          := max p.arity q.arity
| (¬̇p)              := p.arity
| (∀̇p)              := p.arity - 1

@[reducible] def sentence : formula L → Prop := λ p, p.arity = 0

lemma AAAA {α : Type} [encodable α] : ∀ {n : α}, n = n := λ _, rfl

@[reducible] def subst (t : term L) : ℕ → term L := t ^ˢ idvar
notation `ₛ[`t`]` := fopl.subst t

--def subst_sf (t : term L) : ℕ → ℕ → term L
----| 0     := t ^ˢ idvar
----| (n+1) := (subst_sf n)↑
--notation `sₛ[`:95 t ` // `:95  n `]`:0 := subst_sf t n

lemma rewriting_sf_itr_subst_sf (t : term L) : ∀ n, rewriting_sf_itr ₛ[t] n = ₛ[t]^n
| 0     := rfl
| (n+1) := by simp[rewriting_sf_itr_subst_sf n]

@[simp] lemma subst_sf_0 (t : term L) : ₛ[t] 0 = t := rfl
@[simp] lemma subst_sf_succ (t : term L) (n) : ₛ[t] (n+1) = #n := rfl

@[simp] lemma subst_sf_eq_eq (t : term L) (n : ℕ) : (ₛ[t]^n) n = t.rew (λ x, #(x+n)) :=
by { induction n with n IH; simp[has_pow.pow, subst] at*, simp[has_pow.pow, IH, vecterm.sf], refl }

@[simp] lemma subst_sf_lt_eq' (t : term L) : ∀ {n m}, n ≤ m → (ₛ[t]^n) (m+1) = #m :=
by { intros n, induction n with n IH,
     { intros, simp },
     intros m h, simp[rewriting_sf],
     cases m, { exfalso, simp* at* },
     have := @IH m (by { exact nat.succ_le_succ_iff.mp h}), simp[this] }

@[simp] lemma subst_sf_lt_eq (t : term L) : ∀ {n m}, n < m → (ₛ[t]^n) m = #(m-1) :=
by { intros n m h,
     have lmm := subst_sf_lt_eq' t (nat.le_pred_of_lt h), 
     have : m - 1 + 1 = m, omega,
     simp[this] at lmm, exact lmm }

@[simp] lemma subst_sf_gt_eq (t : term L) : ∀ {n m}, m < n → (ₛ[t]^n) m = #m :=
by { intros n, induction n with n IH; simp[rewriting_sf],
     intros m h, cases m; simp,
     simp [@IH m (by { exact nat.succ_lt_succ_iff.mp h})] }

@[reducible] def subst_embed (t : term L) : ℕ → term L := t ^ᵉ idvar
notation `ₑ[`t`]` := subst_embed t

--def embed_sf (t : term L) : ℕ → ℕ → term L
--| 0     := t ^ᵉ idvar
--| (n+1) := (embed_sf n)↑
--notation `em[`:95 t ` // `:95  n `]`:0 := embed_sf t n

@[simp] lemma embed_sf_eq_eq (t : term L) (n) : (ₑ[t]^n) n = t.rew (λ x, #(x+n)) :=
by { induction n with n IH; simp[subst_embed], simp[IH, vecterm.sf], refl }

@[simp] lemma embed_sf_lt_eq' (t : term L) : ∀ {n m}, n < m → (ₑ[t]^n) m = #m :=
by { intros n, induction n with n IH,
     { intros, simp[subst_embed], cases m; simp* at* },
     intros m h, simp[subst_embed, rewriting_sf],
     cases m, { exfalso, simp* at* },
     have := @IH m (by { exact nat.succ_le_succ_iff.mp h}), simp[this] }

@[simp] lemma embed_sf_gt_eq (t : term L) : ∀ {n m}, m < n → (ₑ[t]^n) m = #m :=
by { intros n, induction n with n IH; simp[subst_embed, rewriting_sf],
     intros m h, cases m; simp,
     simp [@IH m (by { exact nat.succ_lt_succ_iff.mp h})] }

namespace formula

@[simp] def rew : (ℕ → term L) → formula L → formula L
| _ (const c) := const c 
| s (app p v) := app p (v.rew s)
| s (t =̇ u)   := (t.rew s) =̇ (u.rew s)
| s (p →̇ q)  := p.rew s →̇ q.rew s
| s (¬̇p)      := ¬̇(p.rew s)
| s (∀̇p)      := ∀̇(p.rew s⁺¹)

@[simp] lemma and_rew (p q : formula L) (s) : (p ⩑ q).rew s = p.rew s ⩑ q.rew s :=by simp[and, formula.rew]
@[simp] lemma or_rew (p q : formula L) (s) : (p ⩒ q).rew s = p.rew s ⩒ q.rew s :=by simp[or, formula.rew]
@[simp] lemma iff_rew (p q : formula L) (s) : (p ↔̇ q).rew s = p.rew s ↔̇ q.rew s :=by simp[iff, formula.rew]
@[simp] lemma ex_rew (p : formula L) (s) : (Ėp).rew s = Ėp.rew s⁺¹ :=by simp[ex, rewriting_sf]
@[simp] lemma top_rew (s) : (⊤̇ : formula L).rew s = ⊤̇ := by simp[formula.top, formula.rew, vecterm.rew]
@[simp] lemma bot_rew (s) : (⊥̇ : formula L).rew s = ⊥̇ := by simp[formula.bot, formula.rew, vecterm.rew]

def sf (p : formula L) : formula L := p.rew (λ x, #(x+1))

@[reducible] def sf_itr (m) (t : formula L) : formula L := t.rew (λ x, #(x+m))


@[simp] lemma const_sf (c : L.pr 0) : (const c).sf = const c := rfl
@[simp] lemma app_sf {n} (p : L.pr (n+1)) (v : vecterm L n) : (app p v).sf = app p v.sf := rfl
@[simp] lemma eq_sf (t u : term L) : (t =̇ u).sf = t.sf =̇ u.sf := rfl
@[simp] lemma imply_sf (p q : formula L) : (p →̇ q).sf = p.sf →̇ q.sf := rfl
@[simp] lemma neg_sf (p : formula L) : (¬̇p).sf = ¬̇p.sf := rfl
@[simp] lemma and_sf (p q : formula L) : (p ⩑ q).sf = p.sf ⩑ q.sf := rfl
@[simp] lemma or_sf (p q : formula L) : (p ⩒ q).sf = p.sf ⩒ q.sf := rfl
@[simp] lemma top_sf : (⊤̇ : formula L).sf = ⊤̇ := by simp[top]; refl
@[simp] lemma bot_sf : (⊥̇ : formula L).sf = ⊥̇ := by simp[bot]; refl

lemma nested_rew : ∀ (p : formula L) (s₀ s₁),
  (p.rew s₀).rew s₁ = p.rew (λ x, (s₀ x).rew s₁)
| (const c) _ _ := rfl
| (app p v) _ _ := by simp[rew]
| (t =̇ u)   _ _ := by simp[rew]
| (p →̇ q)  _ _ := by simp[rew]; refine ⟨nested_rew p _ _, nested_rew q _ _⟩
| (¬̇p)      _ _ := by simp[rew]; refine nested_rew p _ _
| (∀̇p)      _ _ := by { simp[rew, nested_rew p], congr,
    funext n, cases n; simp[vecterm.rew, vecterm.sf] }

@[simp] lemma rew_idvar (p : formula L) : p.rew idvar = p :=
by { induction p; simp[rew]; try {simp*},
     have : idvar⁺¹ = idvar,
     { funext n, cases n; simp }, rw[this], simp* }

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

@[simp] lemma sentence_rew {p : formula L} (h : sentence p) (s : ℕ → term L) : p.rew s = p :=
by { suffices : rew s p = rew idvar p, { simp* },
     refine rew_rew _ _, simp[show p.arity = 0, from h] }

@[simp] lemma sentence_sf {p : formula L} (h : sentence p) : p.sf = p := by simp[formula.sf, sentence_rew h]

@[simp] lemma sf_subst_eq (p : formula L) (t) : p.sf.rew ₛ[t] = p :=
by simp[formula.sf, vecterm.rew, nested_rew]

@[simp] lemma sf_rew_eq (p : formula L) (t s) : p.sf.rew (t ^ˢ s) = p.rew s :=
by simp[formula.sf, vecterm.rew, nested_rew]

lemma subst_sf_rew (p : formula L) (t : term L) (s : ℕ → term L) :
  (p.rew ₛ[t]).rew s = (p.rew s⁺¹).rew ₛ[t.rew s] :=
by { simp[formula.rew, vecterm.rew, nested_rew], congr, ext n, cases n; simp }

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

lemma nfal_rew : ∀ (n) (p : formula L) (s),
  (nfal p n).rew s = nfal (p.rew (λ m, ite (m < n) (#m) ((s $ m - n).rew (λ x, #(x+n))))) n
| 0 p s := by simp 
| (n+1) p s := by { simp[rewriting_sf, nfal_rew n], congr,
    ext m, by_cases C₁ : m < n,
    { simp[C₁, nat.lt.step C₁] },
    by_cases C₂ : m < n + 1; simp[C₁, C₂],
    { have : m - n = 0, omega, simp[this], omega },
    { have : m - n = (m - (n + 1)) + 1, omega,
      simp[this], congr, ext x, simp[nat.succ_add_eq_succ_add x n]} }

lemma nfal_sentence (p : formula L) : sentence (nfal p p.arity) :=
by { have := nfal_arity p.arity p, simp at*, refine this }

end formula


end fopl

@[simp] def dvector.to_vecterm {L : fopl.language} : ∀ {n} (v : dvector (fopl.term L) (n+1)), fopl.vecterm L n
| 0     (t :: dvector.nil) := t
| (n+1) (t :: ts)          := fopl.vecterm.cons t ts.to_vecterm 
