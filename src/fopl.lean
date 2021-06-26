import tactic

/- 焼き直し -/

universe u

structure language : Type (u+1) :=
(fn : ℕ → Type u)
(pr : ℕ → Type u)

namespace language
variables (L : language.{u})

inductive vecterm (L : language.{u}) : ℕ → Type u
| nil {} : vecterm 0
| cons   : ∀ {n : ℕ}, vecterm 1 → vecterm n → vecterm (n+1)
| var {} : ℕ → vecterm 1
| app    : ∀ {n : ℕ}, L.fn n → vecterm n → vecterm 1

prefix `#`:max := vecterm.var

@[reducible] def term : Type u := L.vecterm 1

inductive form : Type u
| app   : ∀ {n : ℕ}, L.pr n → L.vecterm n → form
| equal : L.term → L.term → form
| imply : form → form → form
| neg : form → form
| fal : form → form

instance : has_emptyc (L.vecterm 0) := ⟨vecterm.nil⟩
infix ` =̇ `:90 := form.equal
infixr ` →̇ `:78 := form.imply
prefix `¬̇`:94 := form.neg
prefix `Ȧ`:70 := form.fal

variables {L}

def vecterm.neq (t : L.term) (u : L.term) : L.form := ¬̇(t =̇ u)
infix ` ≠̇ `:90 := vecterm.neq

def form.and (p : L.form) (q : L.form) : L.form := ¬̇(p →̇ ¬̇q)
infix ` ⩑ `:86 := form.and

def form.or (p : L.form) (q : L.form) : L.form := ¬̇p →̇ q
infix ` ⩒ `:82 := form.or

def form.iff (p : L.form) (q : L.form) : L.form := (p →̇ q) ⩑ (q →̇ p)
infix ` ↔̇ `:74 := form.iff

def form.ex (p : L.form) : L.form := ¬̇Ȧ¬̇p

prefix `Ė`:70 := form.ex

def slide {α : Type*} (n : α) (s : ℕ → α) : ℕ → α := λ x0,
  match x0 with
  | 0   := n
  | m+1 := s m
  end

infixr ` ^ˢ `:max := slide

@[simp, reducible] def idvar : ℕ → L.term := λ x, #x

def symbolf₀ (L : language) (b : L.fn 0) : L.term := vecterm.app b vecterm.nil

def symbolf₁ (L : language) (b : L.fn 1) : L.term → L.term := (λ x, vecterm.app b x)

def symbolf₂ (L : language) (b : L.fn 2) : L.term → L.term → L.term :=
(λ x y, vecterm.app b (vecterm.cons x y))

def symbolp₀ (L : language) (b : L.pr 0) : L.form := form.app b vecterm.nil

def symbolp₁ (L : language) (b : L.pr 1) : L.term → L.form := (λ x, form.app b x)

def symbolp₂ (L : language) (b : L.pr 2) : L.term → L.term → L.form :=
(λ x y, form.app b (vecterm.cons x y))

namespace vecterm




def rew (s : ℕ → L.term) : ∀ {n}, L.vecterm n → L.vecterm n
| _ nil        := nil
| _ (cons a v) := cons a.rew v.rew
| _ (#x)       := s x
| _ (app f v)  := app f v.rew

def sf {n} (t : L.vecterm n) : L.vecterm n := t.rew (λ x, #(x+1))

@[simp] lemma nil_sf {n : ℕ} : (nil : L.vecterm 0).sf = nil := rfl
@[simp] lemma var_sf {n : ℕ} : (#n : L.term).sf = #(n + 1) := rfl

def arity : ∀ {n}, L.vecterm n → ℕ
| _ nil        := 0
| _ (cons a v) := max a.arity v.arity
| _ (#n)       := n + 1
| _ (app f v)  := v.arity

@[simp] lemma nested_rew (s₀ s₁) : ∀ {n} (t : L.vecterm n),
  (t.rew s₀).rew s₁ = t.rew (λ x, (s₀ x).rew s₁)
| _ nil := rfl
| _ (cons a v) := by simp[rew, nested_rew]
| _ (#x)       := by simp[rew]
| _ (app f v)  := by simp[rew, nested_rew]

@[simp] lemma sf_rew_eq {n} (t : L.vecterm n) (t₀ : L.term) (s : ℕ → L.term) :
  t.sf.rew (t₀ ^ˢ s) = t.rew s :=
by cases t; by simp[rew, sf, slide]

@[simp] lemma rew_idvar {n} (t : L.vecterm n) : t.rew idvar = t :=
by induction t; simp[rew]; simp*

lemma rew_rew {s₀ s₁ : ℕ → L.term} : ∀ {n} (t : L.vecterm n),
  (∀ m, m < t.arity → s₀ m = s₁ m) → t.rew s₀ = t.rew s₁
| _ nil        _ := rfl
| _ (cons a v) h := by simp[rew, arity] at h ⊢;
    refine ⟨rew_rew _ (λ _ e, h _ (or.inl e)), rew_rew _ (λ _ e, h _ (or.inr e))⟩
| _ (#x)       h := by simp[rew, arity] at h ⊢; simp*
| _ (app f v)  h := by simp[rew, arity] at h ⊢; refine rew_rew _ h

end vecterm

def form.arity : L.form → ℕ
| (form.app p v) := v.arity
| (t =̇ u)        := max t.arity u.arity
| (p →̇ q)       := max p.arity q.arity
| (¬̇p)           := p.arity
| (Ȧp)           := p.arity - 1

def sentence : set L.form := {p | p.arity = 0}

namespace form

def rew : (ℕ → L.term) → L.form → L.form
| s (app p v) := app p (v.rew s)
| s (t =̇ u)   := (t.rew s) =̇ (u.rew s)
| s (p →̇ q)  := p.rew s →̇ q.rew s
| s (¬̇p)      := ¬̇(p.rew s)
| s (Ȧp)      := Ȧ(p.rew $ #0 ^ˢ (λ x, (s x).sf))

def sf (p : L.form) : L.form := p.rew (λ x, #(x+1))

@[simp] lemma nested_rew : ∀ (p : L.form) (s₀ s₁),
  (p.rew s₀).rew s₁ = p.rew (λ x, (s₀ x).rew s₁)
| (app p v) _ _ := by simp[rew]
| (t =̇ u)   _ _ := by simp[rew]
| (p →̇ q)  _ _ := by simp[rew]; refine ⟨nested_rew p _ _, nested_rew q _ _⟩
| (¬̇p)      _ _ := by simp[rew]; refine nested_rew p _ _
| (Ȧp)      _ _ := by { simp[rew, nested_rew p], congr,
    funext n, cases n; simp[slide, vecterm.rew, vecterm.sf] }

@[simp] lemma rew_idvar (p : L.form) : p.rew idvar = p :=
by { induction p; simp[rew]; try {simp*},
     have : (#0 ^ˢ λ x, #(x+1) : ℕ → L.term) = idvar,
     { funext n, cases n; simp[slide] }, simp* }

lemma rew_rew : ∀ (p : L.form) {s₀ s₁ : ℕ → L.term},
  (∀ m, m < p.arity → s₀ m = s₁ m) → p.rew s₀ = p.rew s₁
| (app p v) _ _ h := by simp[rew, arity] at h ⊢; refine vecterm.rew_rew _ h
| (t =̇ u)   _ _ h := by simp[rew, arity] at h ⊢;
    refine ⟨vecterm.rew_rew _ (λ _ e, h _ (or.inl e)), vecterm.rew_rew _ (λ _ e, h _ (or.inr e))⟩
| (p →̇ q)  _ _ h := by simp[rew, arity] at h ⊢;
    refine ⟨rew_rew _ (λ _ e, h _ (or.inl e)), rew_rew _ (λ _ e, h _ (or.inr e))⟩
| (¬̇p)      _ _ h := by simp[rew, arity] at h ⊢; refine rew_rew _ h
| (Ȧp)      _ _ h := by { simp[rew, arity] at h ⊢,
    refine rew_rew _ (λ m e, _), cases m; simp[slide],
    cases p.arity, { exfalso, simp* at* },
    { simp at h, simp[h _ (nat.succ_lt_succ_iff.mp e)] } }

lemma sentence_rew {p : L.form} (h : sentence p) (s : ℕ → L.term) : p.rew s = p :=
by { suffices : rew s p = rew idvar p, { simp* },
     refine rew_rew _ _, simp[show p.arity = 0, from h] }

end form

notation p `.(` x `)` := p.rew (x ^ˢ idvar) 
notation p `.(` x `, ` y `)` := p.rew (x ^ˢ y ^ˢ idvar) 

end language
