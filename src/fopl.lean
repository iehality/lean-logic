import tactic

universe u

structure language : Type (u+1) :=
(fn : ℕ → Type u)
(pr : ℕ → Type u)

namespace language
variables (L : language.{u})

inductive vecterm : ℕ → ℕ → Type u
| nil {} : vecterm 0 0
| var {} : ∀ (i : ℕ), vecterm (i+1) 1
| tuple  : ∀ {i j n : ℕ}, vecterm i n → vecterm j 1 → vecterm (max i j) (n+1)
| app    : ∀ {i n : ℕ}, L.fn n → vecterm i n → vecterm i 1

prefix `#`:max := language.vecterm.var

@[reducible] def term (i : ℕ) : Type u := L.vecterm i 1

inductive form : ℕ → Type u
| app   : ∀ {i n : ℕ}, L.pr n → L.vecterm i n → form i
| equal : ∀ {i j : ℕ}, L.term i → L.term j → form (max i j)
| imply : ∀ {i j : ℕ}, form i → form j → form (max i j)
| neg : ∀ {i : ℕ}, form i → form i
| fal : ∀ {i : ℕ}, form (i+1) → form i

@[reducible] def sentence : Type u := L.form 0

infix ` =̇ `:88 := language.form.equal
infixr ` →̇ `:62 := language.form.imply
prefix `¬̇`:max := language.form.neg
notation `∀̇` n`, ` p := @language.form.fal _ n p
#check @language.form.fal _
variables {L}

def form.and {i j : ℕ} (p : L.form i) (q : L.form j) := ¬̇(p →̇ ¬̇q)
infix ` ⩑ `:70 := form.and

def form.or {i j : ℕ} (p : L.form i) (q : L.form j) := ¬̇p →̇ q
infix ` ⩒ `:65 := form.or

def form.iff {i j : ℕ} (p : L.form i) (q : L.form j) := (p →̇ q) ⩑ (q →̇ p)
infix ` ↔̇ `:60 := form.iff

def form.ex {i : ℕ} (p : L.form (i+1)) : L.form i := ¬̇(∀̇ i, ¬̇p)

notation `∃̇` n`, `p := @form.ex _ n p

def vecterm.mem (k : ℕ) : ∀ {i n}, L.vecterm i n → Prop
| _ _ vecterm.nil         := false
| _ _ #n                  := k = n
| _ _ (vecterm.tuple v a) := a.mem ∨ v.mem
| _ _ (vecterm.app f v)   := v.mem

instance {i n} : has_mem ℕ (L.vecterm i n) := ⟨λ x, @vecterm.mem L x i n⟩
instance {i} : has_mem ℕ (L.term i) := ⟨λ x, @vecterm.mem L x i 1⟩

def form.mem (k : ℕ) : ∀ {i}, L.form i → Prop
| _ (form.app p v)   := k ∈ v
| _ (form.equal t u) := k ∈ t ∨ k ∈ u
| _ (p →̇ q)         := p.mem ∨ q.mem
| _ (¬̇p)             := p.mem
| i (∀̇ _, p)         := k < i ∧ p.mem

instance {i} : has_mem ℕ (L.form i) := ⟨λ x, @form.mem L x i⟩

def vecterm.vers {i n} (v : L.vecterm i n) := {x | x ∈ v}
def form.vers {i} (p : L.form i) := {x | x ∈ p}

def vecterm.rew (k : ℕ) {i} (t : L.term i) :
  ∀ {j n} (v : L.vecterm j n), k ∈ v → k < j →  L.vecterm (max i j) n
| _ _ vecterm.nil h := by cases h
| _ _ #x h          := by { cases h, }

end language
