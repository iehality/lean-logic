import deduction model data.equiv.encodable.basic
open encodable

universes u

namespace fopl
variables {L : language.{u}} 

inductive language_fn (L : language.{u}) : ℕ → Type u
| sk : ∀ (p : formula L), language_fn p.arity
| old : ∀ {n}, L.fn n → language_fn n

def language.skolemize (L : language) : language := ⟨language_fn L, L.pr⟩

@[simp] lemma skolemize_fn : L.skolemize.fn = language_fn L := rfl

def vecterm.corresp : ∀ {n}, vecterm L n → vecterm L.skolemize n
| _ (vecterm.cons a v) := vecterm.cons a.corresp v.corresp
| _ (#n)               := #n
| _ (vecterm.const c)  := vecterm.const (language_fn.old c)
| _ (vecterm.app f v)  := vecterm.app (language_fn.old f) v.corresp

instance (n) : has_coe (vecterm L n) (vecterm L.skolemize n) := ⟨vecterm.corresp⟩

def formula.corresp : formula L → formula L.skolemize
| (formula.const c) := formula.const c
| (formula.app p v) := formula.app p v.corresp
| (t =̇ u)        := t.corresp =̇ u.corresp
| (p →̇ q)       := p.corresp →̇ q.corresp
| (¬̇p)           := ¬̇p.corresp
| (Ȧp)           := Ȧp.corresp

instance : has_coe (formula L) (formula L.skolemize) := ⟨formula.corresp⟩

def normvecvar : ∀ {n}, vecterm L n
| 0     := #0
| (n+1) := vecterm.cons #(n+1) normvecvar

namespace skolemization
variables {L}

def skterm (p : formula L) : term L.skolemize :=
begin
  cases C : p.arity,
  have := language_fn.sk p, simp[C] at this, exact vecterm.const this,
  have F : L.skolemize.fn (n+1), { have := language_fn.sk p, simp[C] at this, exact this },
  refine vecterm.app F normvecvar
end


inductive theory.skolemize (T : theory L) : theory (L.skolemize)
| sk  : ∀ (p : formula L), theory.skolemize (p.corresp →̇ p.corresp.ᵉ(skterm p))
| old : ∀ {p}, T p → theory.skolemize p

end skolemization

end fopl

namespace fopl
variables {L : language.{u}} [encodable (formula L)] (T : theory L)


def theory.maximum_aux (T : theory L) : ℕ → theory L
| 0     := T
| (s+1) := let p := idecode (formula L) s in
    if (theory.maximum_aux s +{p}).consistent then theory.maximum_aux s +{p} else theory.maximum_aux s

def theory.maximum  : theory L := {p | ∃ s, T.maximum_aux s p}

variables {T}

lemma maximum_aux_inclusion (s) : T.maximum_aux s ⊆ T.maximum := λ p h, ⟨s, h⟩

lemma maximum_consistent_aux (h : T.consistent) : ∀ s, (T.maximum_aux s).consistent
| 0 := h
| (s+1) := by { simp[theory.maximum_aux],
    by_cases (T.maximum_aux s +{idecode (formula L) s}).consistent; simp[h, maximum_consistent_aux s] }

lemma maximum_aux_ss (s) : T.maximum_aux s ⊆ T.maximum_aux (s+1) := λ p hyp_p,
by { simp[theory.maximum_aux], by_cases C₁ : (T.maximum_aux s)+{idecode (formula L) s}.consistent; simp[C₁],
     refine theory.add.old hyp_p, refine hyp_p }

theorem maximum_maximum {p} : T.maximum ⊢ p ∨ T.maximum ⊢ ¬̇p :=
begin
  by_cases C : (T.maximum_aux (encode p) +{p}).consistent,
  { left, have : T.maximum_aux (encode p + 1) = (T.maximum_aux (encode p) +{p}),
    { simp[theory.maximum_aux, C] },
    have : T.maximum_aux (encode p + 1) ⊢ p,
    { rw this, simp },
    refine provable.inclusion this (maximum_aux_inclusion _) },
  { right, simp[theory.consistent] at C, rcases C with ⟨r, hyp1, hyp2⟩,
    have hyp1 : T.maximum +{p} ⊢ r,
    { refine provable.inclusion hyp1 (λ h h1, _), cases h1 with _ h,
      refine theory.add.new, refine theory.add.old (maximum_aux_inclusion _ _ h) },
    have hyp2 : T.maximum +{p} ⊢ ¬̇r,
    { refine provable.inclusion hyp2 (λ h h1, _), cases h1 with _ h,
      refine theory.add.new, refine theory.add.old (maximum_aux_inclusion _ _ h) },
    show T.maximum ⊢ ¬̇p, from provable.raa _ hyp1 hyp2 }
end 

lemma maximum_consistent (con : T.consistent) : T.maximum.consistent :=
begin
  simp[theory.consistent], intros p hyp A,
  have : ∃ s, T.maximum_aux s ⊢ p, from provable.proof_compact maximum_aux_ss hyp, rcases this with ⟨s₁, lmm₁⟩,
  have : ∃ s, T.maximum_aux s ⊢ ¬̇p, from provable.proof_compact maximum_aux_ss A, rcases this with ⟨s₂, lmm₂⟩,
  have lmm₁ : T.maximum_aux (max s₁ s₂) ⊢ p, from provable.inclusion lmm₁ (ss_le maximum_aux_ss (by simp)),
  have lmm₂ : T.maximum_aux (max s₁ s₂) ⊢ ¬̇p, from provable.inclusion lmm₂ (ss_le maximum_aux_ss (by simp)),
  have : ¬(T.maximum_aux (max s₁ s₂)).consistent, simp[theory.consistent], refine ⟨p, lmm₁, lmm₂⟩,
  exact this (maximum_consistent_aux con _)
end

def LMmodel := 𝔗[T.maximum]


end fopl