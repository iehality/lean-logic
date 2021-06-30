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

inductive form : Type u
| const : L.pr 0 → form
| app   : ∀ {n : ℕ}, L.pr (n+1) → vecterm L n → form
| equal : term L → term L → form
| imply : form → form → form
| neg : form → form
| fal : form → form

infix ` =̇ `:90 := form.equal
infixr ` →̇ `:78 := form.imply
prefix `¬̇`:94 := form.neg
prefix `Ȧ`:90 := form.fal

variables {L}

@[reducible] def form.neq (t : term L) (u : term L) : form L := ¬̇(t =̇ u)
infix ` ≠̇ `:90 := form.neq

def form.and (p : form L) (q : form L) : form L := ¬̇(p →̇ ¬̇q)
infix ` ⩑ `:86 := form.and

def form.or (p : form L) (q : form L) : form L := ¬̇p →̇ q
infix ` ⩒ `:82 := form.or

def form.iff (p : form L) (q : form L) : form L := (p →̇ q) ⩑ (q →̇ p)
infix ` ↔̇ `:74 := form.iff

def form.ex (p : form L) : form L := ¬̇Ȧ¬̇p
prefix `Ė`:90 := form.ex

def form.top : form L := Ȧ(#0 =̇ #0)
notation `⊤̇` := form.top

def form.bot : form L := ¬̇⊤̇
notation `⊥̇` := form.bot

instance : inhabited (form L) := ⟨⊥̇⟩

@[simp] def slide {α : Type*} (a : α) (s : ℕ → α) : ℕ → α
| 0     := a
| (m+1) := s m

@[simp] def embed {α : Type*} (a : α) (s : ℕ → α) : ℕ → α
| 0     := a
| (m+1) := s (m+1)

infixr ` ^ˢ `:max := slide

infixr ` ^ᵉ `:max := embed

@[simp, reducible] def idvar : ℕ → term L := λ x, #x

namespace vecterm

def rew (s : ℕ → term L) : ∀ {n}, vecterm L n → vecterm L n
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

end vecterm

def form.arity : form L → ℕ
| (form.const c) := 0
| (form.app p v) := v.arity
| (t =̇ u)        := max t.arity u.arity
| (p →̇ q)       := max p.arity q.arity
| (¬̇p)           := p.arity
| (Ȧp)           := p.arity - 1

def sentence : set (form L) := {p | p.arity = 0}

namespace form

def rew : (ℕ → term L) → form L → form L
| _ (const c) := const c 
| s (app p v) := app p (v.rew s)
| s (t =̇ u)   := (t.rew s) =̇ (u.rew s)
| s (p →̇ q)  := p.rew s →̇ q.rew s
| s (¬̇p)      := ¬̇(p.rew s)
| s (Ȧp)      := Ȧ(p.rew $ #0 ^ˢ (λ x, (s x).sf))

def sf (p : form L) : form L := p.rew (λ x, #(x+1))


@[simp] lemma const_sf (c : L.pr 0) : (const c).sf = const c := rfl
@[simp] lemma app_sf {n} (p : L.pr (n+1)) (v : vecterm L n) : (app p v).sf = app p v.sf := rfl
@[simp] lemma eq_sf (t u : term L) : (t =̇ u).sf = t.sf =̇ u.sf := rfl
@[simp] lemma imply_sf (p q : form L) : (p →̇ q).sf = p.sf →̇ q.sf := rfl
@[simp] lemma neg_sf (p : form L) : (¬̇p).sf = ¬̇p.sf := rfl
@[simp] lemma and_sf (p q : form L) : (p ⩑ q).sf = p.sf ⩑ q.sf := rfl
@[simp] lemma or_sf (p q : form L) : (p ⩒ q).sf = p.sf ⩒ q.sf := rfl

def subst₁ (p : form L) (x : term L) := p.rew (x ^ˢ idvar) 

notation p`.(`x`)` := p.subst₁ x

/-
@[simp] lemma app_subst₁ {n} (p : L.pr n) (v : vecterm L n) (t) : (app p v).(t) = app p v.(t) := rfl
@[simp] lemma eq_subst₁ (t u : vecterm L 1) (v) : (t =̇ u).(v) = t.rew (v ^ˢ idvar) =̇ u.rew (v ^ˢ idvar) := rfl
@[simp] lemma imply_subst₁ (p q : form L) (t) : (p →̇ q).(t) = p.(t) →̇ q.(t) := rfl
@[simp] lemma neg_subst₁ (p : form L) (t) : (¬̇p).(t) = ¬̇p.(t) := rfl
@[simp] lemma and_subst₁ (p q : form L) (t) : (p ⩑ q).(t) = p.(t) ⩑ q.(t) := rfl
@[simp] lemma or_subst₁ (p q : form L) (t) : (p ⩒ q).(t) = p.(t) ⩒ q.(t) := rfl
-/

def subst₂ (p : form L) (x y : term L) := p.rew (x ^ˢ y^ˢ idvar) 

notation p`.(`x`, `y`)` := p.subst₂ x y

def subst₁_e (p : form L) (x : term L) := p.rew (x ^ᵉ idvar) 

notation p`.ᵉ(`x`)` := p.subst₁_e x

@[simp] lemma nested_rew : ∀ (p : form L) (s₀ s₁),
  (p.rew s₀).rew s₁ = p.rew (λ x, (s₀ x).rew s₁)
| (const c) _ _ := rfl
| (app p v) _ _ := by simp[rew]
| (t =̇ u)   _ _ := by simp[rew]
| (p →̇ q)  _ _ := by simp[rew]; refine ⟨nested_rew p _ _, nested_rew q _ _⟩
| (¬̇p)      _ _ := by simp[rew]; refine nested_rew p _ _
| (Ȧp)      _ _ := by { simp[rew, nested_rew p], congr,
    funext n, cases n; simp[vecterm.rew, vecterm.sf] }

@[simp] lemma rew_idvar (p : form L) : p.rew idvar = p :=
by { induction p; simp[rew]; try {simp*},
     have : (#0 ^ˢ λ x, #(x+1) : ℕ → term L) = idvar,
     { funext n, cases n; simp }, simp* }

lemma rew_rew : ∀ (p : form L) {s₀ s₁ : ℕ → term L},
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

lemma sentence_rew {p : form L} (h : sentence p) (s : ℕ → term L) : p.rew s = p :=
by { suffices : rew s p = rew idvar p, { simp* },
     refine rew_rew _ _, simp[show p.arity = 0, from h] }

@[simp] lemma sf_subst (p : form L) (t) : p.sf.(t) = p :=
by simp[form.sf, form.subst₁, vecterm.rew]

@[simp] lemma sf_rew (p : form L) (t s) : p.sf.rew (t ^ˢ s) = p.rew s :=
by simp[form.sf, vecterm.rew]

@[simp] def op : form L → bool
| (const c) := tt
| (app p v) := tt
| (t =̇ u)   := tt
| (p →̇ q)  := p.op && q.op
| (¬̇p)      := p.op
| (Ȧp)      := ff

@[simp] lemma op.and (p q : form L) : (p ⩑ q).op = p.op && q.op := rfl

@[simp] lemma op.or (p q : form L) : (p ⩒ q).op = p.op && q.op := rfl

end form

def openform (p : form L) : Prop := p.op = tt

end fopl
