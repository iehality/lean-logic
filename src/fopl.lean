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
prefix `Ȧ`:90 := formula.fal

variables {L}

@[reducible] def formula.neq (t : term L) (u : term L) : formula L := ¬̇(t =̇ u)
infix ` ≠̇ `:90 := formula.neq

def formula.and (p : formula L) (q : formula L) : formula L := ¬̇(p →̇ ¬̇q)
infix ` ⩑ `:86 := formula.and

def formula.or (p : formula L) (q : formula L) : formula L := ¬̇p →̇ q
infix ` ⩒ `:82 := formula.or

def formula.iff (p : formula L) (q : formula L) : formula L := (p →̇ q) ⩑ (q →̇ p)
infix ` ↔̇ `:74 := formula.iff

def formula.ex (p : formula L) : formula L := ¬̇Ȧ¬̇p
prefix `Ė`:90 := formula.ex

@[irreducible] def formula.top : formula L := Ȧ(#0 =̇ #0)
notation `⊤̇` := formula.top

@[irreducible] def formula.bot : formula L := ¬̇⊤̇
notation `⊥̇` := formula.bot

instance : inhabited (formula L) := ⟨⊥̇⟩

@[simp] def nfal (p : formula L) : ℕ → formula L
| 0     := p
| (n+1) := Ȧ(nfal n)

@[simp] def slide {α : Type*} (a : α) (s : ℕ → α) : ℕ → α
| 0     := a
| (m+1) := s m

@[simp] def embed {α : Type*} (a : α) (s : ℕ → α) : ℕ → α
| 0     := a
| (m+1) := s (m+1)

infixr ` ^ˢ `:max := slide

infixr ` ^ᵉ `:max := embed

@[reducible] def idvar : ℕ → term L := λ x, #x

@[reducible] def slide_head (a : term L) : ℕ → term L := a ^ˢ idvar
prefix `sl₁ `:80 := slide_head

@[reducible] def embed_head (a : term L) : ℕ → term L := a ^ᵉ idvar
prefix `em₁ `:80 := slide_head

namespace vecterm

@[simp] def rew (s : ℕ → term L) : ∀ {n}, vecterm L n → vecterm L n
| _ (cons a v) := cons a.rew v.rew
| _ (#x)       := s x
| _ (const c)  := const c
| _ (app f v)  := app f v.rew

def sf {n} (t : vecterm L n) : vecterm L n := t.rew (λ x, #(x+1))

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
notation s`⁺`:1200 := rewriting_sf s

@[simp] lemma rewriting_sf_0 (s : ℕ → term L) : s⁺ 0 = #0 := rfl
@[simp] lemma rewriting_sf_succ (s : ℕ → term L) (n : ℕ) : s⁺ (n.succ) = (s n).sf := rfl

def formula.arity : formula L → ℕ
| (formula.const c) := 0
| (formula.app p v) := v.arity
| (t =̇ u)        := max t.arity u.arity
| (p →̇ q)       := max p.arity q.arity
| (¬̇p)           := p.arity
| (Ȧp)           := p.arity - 1

@[reducible] def sentence : formula L → Prop := λ p, p.arity = 0

namespace formula

@[simp] def rew : (ℕ → term L) → formula L → formula L
| _ (const c) := const c 
| s (app p v) := app p (v.rew s)
| s (t =̇ u)   := (t.rew s) =̇ (u.rew s)
| s (p →̇ q)  := p.rew s →̇ q.rew s
| s (¬̇p)      := ¬̇(p.rew s)
| s (Ȧp)      := Ȧ(p.rew s⁺)

def sf (p : formula L) : formula L := p.rew (λ x, #(x+1))

@[simp] lemma const_sf (c : L.pr 0) : (const c).sf = const c := rfl
@[simp] lemma app_sf {n} (p : L.pr (n+1)) (v : vecterm L n) : (app p v).sf = app p v.sf := rfl
@[simp] lemma eq_sf (t u : term L) : (t =̇ u).sf = t.sf =̇ u.sf := rfl
@[simp] lemma imply_sf (p q : formula L) : (p →̇ q).sf = p.sf →̇ q.sf := rfl
@[simp] lemma neg_sf (p : formula L) : (¬̇p).sf = ¬̇p.sf := rfl
@[simp] lemma and_sf (p q : formula L) : (p ⩑ q).sf = p.sf ⩑ q.sf := rfl
@[simp] lemma or_sf (p q : formula L) : (p ⩒ q).sf = p.sf ⩒ q.sf := rfl
@[simp] lemma top_sf : (⊤̇ : formula L).sf = ⊤̇ := by simp[top]; refl
@[simp] lemma bot_sf : (⊥̇ : formula L).sf = ⊥̇ := by simp[bot]; refl

def subst₁ (p : formula L) (x : term L) := p.rew (x ^ˢ idvar) 

notation p`.(`x`)` := p.subst₁ x

def subst₂ (p : formula L) (x y : term L) := p.rew (x ^ˢ y ^ˢ idvar) 

notation p`.(`x`, `y`)` := p.subst₂ x y

def subst₁_e (p : formula L) (x : term L) := p.rew (x ^ᵉ idvar) 

notation p`.ᵉ(`x`)` := p.subst₁_e x



@[simp] lemma nested_rew : ∀ (p : formula L) (s₀ s₁),
  (p.rew s₀).rew s₁ = p.rew (λ x, (s₀ x).rew s₁)
| (const c) _ _ := rfl
| (app p v) _ _ := by simp[rew]
| (t =̇ u)   _ _ := by simp[rew]
| (p →̇ q)  _ _ := by simp[rew]; refine ⟨nested_rew p _ _, nested_rew q _ _⟩
| (¬̇p)      _ _ := by simp[rew]; refine nested_rew p _ _
| (Ȧp)      _ _ := by { simp[rew, nested_rew p], congr,
    funext n, cases n; simp[vecterm.rew, vecterm.sf] }

@[simp] lemma rew_idvar (p : formula L) : p.rew idvar = p :=
by { induction p; simp[rew]; try {simp*},
     have : idvar⁺ = idvar,
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
| (Ȧp)      _ _ h := by { simp[rew, arity] at h ⊢,
    refine rew_rew _ (λ m e, _), cases m; simp,
    cases p.arity, { exfalso, simp* at* },
    { simp at h, simp[h _ (nat.succ_lt_succ_iff.mp e)] } }

@[simp] lemma sentence_rew {p : formula L} (h : sentence p) (s : ℕ → term L) : p.rew s = p :=
by { suffices : rew s p = rew idvar p, { simp* },
     refine rew_rew _ _, simp[show p.arity = 0, from h] }

@[simp] lemma sentence_sf {p : formula L} (h : sentence p) : p.sf = p := by simp[formula.sf, sentence_rew h]

@[simp] lemma sf_subst (p : formula L) (t) : p.sf.(t) = p :=
by simp[formula.sf, formula.subst₁, vecterm.rew]

@[simp] lemma sf_rew (p : formula L) (t s) : p.sf.rew (t ^ˢ s) = p.rew s :=
by simp[formula.sf, vecterm.rew]


@[simp] lemma and_rew (p q : formula L) (s) : (p ⩑ q).rew s = p.rew s ⩑ q.rew s :=by simp[and, formula.rew]
@[simp] lemma or_rew (p q : formula L) (s) : (p ⩒ q).rew s = p.rew s ⩒ q.rew s :=by simp[or, formula.rew]
@[simp] lemma iff_rew (p q : formula L) (s) : (p ↔̇ q).rew s = p.rew s ↔̇ q.rew s :=by simp[iff, formula.rew]
@[simp] lemma ex_rew (p : formula L) (s) : (Ėp).rew s = Ėp.rew (#0 ^ˢ λ x, (s x).sf) :=by simp[ex, formula.rew]
@[simp] lemma top_rew (s) : (⊤̇ : formula L).rew s = ⊤̇ := by simp[formula.top, formula.rew, vecterm.rew]
@[simp] lemma bot_rew (s) : (⊥̇ : formula L).rew s = ⊥̇ := by simp[formula.bot, formula.rew, vecterm.rew]

@[simp] lemma imply_subst₁ (p q : formula L) (t) : (p →̇ q).(t) = p.(t) →̇ q.(t) :=by simp[subst₁, formula.rew]
@[simp] lemma neg_subst₁ (p : formula L) (t) : (¬̇p).(t) = ¬̇p.(t) :=by simp[subst₁, formula.rew]
@[simp] lemma and_subst₁ (p q : formula L) (t) : (p ⩑ q).(t) = p.(t) ⩑ q.(t) :=by simp[subst₁, formula.rew]
@[simp] lemma or_subst₁ (p q : formula L) (t) : (p ⩒ q).(t) = p.(t) ⩒ q.(t) :=by simp[subst₁, formula.rew]
@[simp] lemma iff_subst₁ (p q : formula L) (t) : (p ↔̇ q).(t) = p.(t) ↔̇ q.(t) :=by simp[subst₁, formula.rew]


lemma subst₁_rew (p : formula L) (t) (s) : (p.(t)).rew s = (p.rew (#0 ^ˢ λ x, (s x).sf)).(t.rew s) :=
by { simp[subst₁, formula.rew, vecterm.rew], congr, ext n, cases n; simp[vecterm.rew] }


@[simp] def Open : formula L → bool
| (const c) := tt
| (app p v) := tt
| (t =̇ u)   := tt
| (p →̇ q)  := p.Open && q.Open
| (¬̇p)      := p.Open
| (Ȧp)      := ff

@[simp] lemma op.and (p q : formula L) : (p ⩑ q).Open = p.Open && q.Open := rfl

@[simp] lemma op.or (p q : formula L) : (p ⩒ q).Open = p.Open && q.Open := rfl

lemma nfal_arity : ∀ (n) (p : formula L), (nfal p n).arity = p.arity - n
| 0     p := by simp[formula.arity]
| (n+1) p := by {simp[formula.arity, nfal_arity n], exact (arity p).sub_sub _ _ }

lemma nfal_sentence (p : formula L) : sentence (nfal p p.arity) :=
by { have := nfal_arity p.arity p, simp at*, refine this }

end formula

def openform (p : formula L) : Prop := p.Open = tt

def subst' : ℕ → term L → ℕ → term L
| 0     a := a ^ˢ idvar
| (n+1) a := #0 ^ˢ (λ m, ((subst' n a) m).sf)

@[simp] lemma fal_subst' (p : formula L) (t n) :
  (Ȧp).rew (subst' n t) = Ȧp.rew (subst' (n+1) t) := rfl
@[simp] lemma ex_subst' (p : formula L) (t n) :
  (Ėp).rew (subst' n t) = Ėp.rew (subst' (n+1) t) := rfl

@[simp] lemma var_subst_at (t : term L) (n) :
  (#n).rew (subst' n t) = t 

end fopl



@[simp] def dvector.to_vecterm {L : fopl.language} : ∀ {n} (v : dvector (fopl.term L) (n+1)), fopl.vecterm L n
| 0     (t :: dvector.nil) := t
| (n+1) (t :: ts)          := fopl.vecterm.cons t ts.to_vecterm 
