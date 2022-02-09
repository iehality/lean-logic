import deduction pnf data.equiv.encodable.basic arithmetic
open encodable

universes u

namespace fopl
variables {L : language.{u}} 

local notation `𝚷` := bool.tt

local notation `𝚺` := bool.ff

namespace language

inductive skolemize.char (L : language.{u}) : ℕ → Type u
| sk : ∀ (p : pnf L) (n : ℕ), skolemize.char n

def skolemize (L : language) : language := L + ⟨skolemize.char L, L.pr⟩

namespace skolemize

instance : translation L L.skolemize := language.has_add.add.fopl.translation

@[simp] lemma iff_open (p : formula L) : (tr[p] : formula L.skolemize).is_open ↔ p.is_open :=
language.add_open p

@[simp] lemma translation_eq : ∀ (Q : list bool) (p : formula L) (h),
  tr[(⟨Q, p, h⟩ : pnf L).to_formula] = (⟨Q, tr[p], by simp[h]⟩ : pnf L.skolemize).to_formula
| []       p h := by simp
| (𝚷 :: Q) p h := by simp[translation_eq Q p h]
| (𝚺 :: Q) p h := by simp[translation_eq Q p h]

def Sk (p : pnf L) (n : ℕ) : finitary (term L.skolemize) n → term L.skolemize :=
term.app (sum.inr $ skolemize.char.sk p n)

@[simp] lemma skolemize.skolem_fn_rew (p : pnf L) (n) (v : finitary (term L.skolemize) n) (s : ℕ → term L.skolemize) :
  term.rew s (Sk p n v) = Sk p n (λ i, term.rew s (v i)) :=
by simp[Sk]

@[simp] def skseq (p : pnf L) : fin (p.rank + 1) → ℕ → term L.skolemize
| ⟨0,     _⟩ := ı
| ⟨n + 1, h⟩ :=
    match p.quantifier.nth_le n (by simp at h; exact h) with
    | 𝚷 := (skseq ⟨n, by { simp at h ⊢; exact nat.lt.step h }⟩)^1
    | 𝚺 := Sk p n (λ i, skseq ⟨n, by { simp at h ⊢; exact nat.lt.step h }⟩ i) ⌢ 
    skseq ⟨n, by { simp at h ⊢; exact nat.lt.step h }⟩
    end

/-
@[simp] def skseq (p : pnf L) : list bool → ℕ → ℕ → term L.skolemize
| Q        0       := ı
| []       (n + 1) := ı
| (𝚷 :: Q) (n + 1) := (skseq Q n)^1
| (𝚺 :: Q) (n + 1) := Sk p (p.rank - Q.length - 1) (λ i, skseq Q n i) ⌢ skseq Q n
-/

@[simp] def skolemize_core : Π (p : pnf L) (n : fin (p.rank + 1)), pnf L.skolemize
| ⟨Q, p, h⟩ n := ⟨Q.drop n, tr[p], by simp[h]⟩

def skolemize (p : pnf L) (n : fin (p.rank + 1)) : pnf L.skolemize :=
(skolemize_core p n).rew (skseq p n)

@[simp] lemma skseq_zero (p : pnf L) : skseq p 0 = ı :=
by simp [show (0 : fin (p.rank + 1)) = ⟨0, by simp⟩, from rfl, -fin.mk_zero]

@[simp] lemma skolemize_zero : ∀ (p : pnf L), (skolemize p 0).to_formula = tr[p.to_formula]
| ⟨Q, p, h⟩ := by simp[skolemize, pnf.to_formula, skseq]

lemma skseq_succ_of_pi : ∀ (p : pnf L) (s : fin p.rank)
  (eq_pi : p.quantifier.nth_le s s.property = 𝚷),
  skseq p s.succ = (skseq p (fin.cast_succ s))^1
| ⟨𝚷 :: Q, p, h⟩ ⟨0,     lt⟩ eq_pi := by simp
| ⟨𝚺 :: Q, p, h⟩ ⟨0,     lt⟩ eq_pi := by { simp at eq_pi, contradiction }
| ⟨𝚷 :: Q, p, h⟩ ⟨s + 1, lt⟩ eq_pi := by { simp at eq_pi ⊢, simp[eq_pi] }
| ⟨𝚺 :: Q, p, h⟩ ⟨s + 1, lt⟩ eq_pi := by { simp at eq_pi ⊢, simp[eq_pi] }

lemma skseq_succ_of_sigma : ∀ (p : pnf L) (s : fin p.rank)
  (eq_sigma : p.quantifier.nth_le s s.property = 𝚺),
  skseq p s.succ = (Sk p s (λ i, skseq p (fin.cast_succ s) i)) ⌢ skseq p (fin.cast_succ s)
| ⟨𝚷 :: Q, p, h⟩ ⟨0,     lt⟩ eq_sigma := by { simp at eq_sigma, contradiction }
| ⟨𝚺 :: Q, p, h⟩ ⟨0,     lt⟩ eq_sigma := by { simp, refl }
| ⟨𝚷 :: Q, p, h⟩ ⟨s + 1, lt⟩ eq_sigma := by { simp at eq_sigma ⊢, simp[eq_sigma], refl }
| ⟨𝚺 :: Q, p, h⟩ ⟨s + 1, lt⟩ eq_sigma := by { simp at eq_sigma ⊢, simp[eq_sigma], refl }

lemma skolemize_succ_of_pi : ∀ (p : pnf L)
  (s : fin p.rank) (eq_pi : p.quantifier.nth_le s s.property = 𝚷),
  ∏ skolemize p s.succ = skolemize p s
| ⟨Q, p, h⟩ s eq_pi :=
begin
  have : list.drop s Q = 𝚷 :: list.drop (s + 1) Q,
  { rw [←eq_pi], from list.drop_eq_nth_le_cons s.property },
  simp [skolemize, this, pnf.rew_fal, skseq_succ_of_pi ⟨Q, p, h⟩ s eq_pi]
end

lemma skolemize_succ_of_sigma : ∀ (p : pnf L)
  (s : fin p.rank) (eq_sigma : p.quantifier.nth_le s s.property = 𝚺),
  ∃ p' : pnf L.skolemize, skolemize p s = ∐ p' ∧
    skolemize p s.succ = p'.rew ı[0 ⇝ Sk p s (λ i, skseq p (fin.cast_succ s) i)]
| ⟨Q, p, h⟩ s eq_sigma :=
begin
  have : list.drop s Q = 𝚺 :: list.drop (s + 1) Q,
  { rw [←eq_sigma], from list.drop_eq_nth_le_cons s.property },
  simp [skolemize, this, pnf.rew_ex, pnf.nested_rew, skseq_succ_of_sigma ⟨Q, p, h⟩ s eq_sigma]
end


instance [∀ n, has_to_string (L.fn n)] : ∀ n, has_to_string (L.skolemize.fn n) := λ n,
⟨λ c, by { cases c, { exact has_to_string.to_string c }, { exact "Sk[" ++ has_to_string.to_string n ++ "]" } }⟩

instance [∀ n, has_to_string (L.pr n)] : ∀ n, has_to_string (L.skolemize.pr n) := λ n,
⟨λ c, by { cases c, { exact has_to_string.to_string c }, { exact "" } }⟩

def skolem_axiom (p : pnf L) (s : fin (p.rank + 1)) : formula L.skolemize :=
(skolemize_core p s : formula L.skolemize) ⟶ skolemize_core p s.succ

end skolemize

end language

open language.skolemize

def formula.skolemize (p : formula L) : formula L.skolemize := skolemize p.to_pnf 0

def Skolemize (T : theory L) : theory L.skolemize:= formula.skolemize '' T

open arithmetic

#eval to_string (skolemize (∀₁ x, ∃₁ y, ∀₁ z, ∃₁ v, (x ≃ 0) ⟶ (y ≃ 0) ⟶ (z ≃ 0) ⟶ (v ≃ 0)
  : formula LA).to_pnf (fin.last _)).to_formula

def term.skolem_corresp : term L → term L.skolemize
| (#n) := #n
| (term.app f v) := (term.app (sum.inl f) (λ i, (v i).skolem_corresp))



def formula.corresp : formula L → formula L.skolemize
| (formula.const c) := formula.const c
| (formula.app p v) := formula.app p v.corresp
| (t ≃ u)        := t.corresp ≃ u.corresp
| (p ⟶ q)       := p.corresp ⟶ q.corresp
| (⁻p)           := ⁻p.corresp
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
| sk  : ∀ (p : formula L), theory.skolemize (p.corresp ⟶ p.corresp.ᵉ(skterm p))
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

theorem maximum_maximum {p} : T.maximum ⊢ p ∨ T.maximum ⊢ ⁻p :=
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
    have hyp2 : T.maximum +{p} ⊢ ⁻r,
    { refine provable.inclusion hyp2 (λ h h1, _), cases h1 with _ h,
      refine theory.add.new, refine theory.add.old (maximum_aux_inclusion _ _ h) },
    show T.maximum ⊢ ⁻p, from provable.raa _ hyp1 hyp2 }
end 

lemma maximum_consistent (con : T.consistent) : T.maximum.consistent :=
begin
  simp[theory.consistent], intros p hyp A,
  have : ∃ s, T.maximum_aux s ⊢ p, from provable.proof_compact maximum_aux_ss hyp, rcases this with ⟨s₁, lmm₁⟩,
  have : ∃ s, T.maximum_aux s ⊢ ⁻p, from provable.proof_compact maximum_aux_ss A, rcases this with ⟨s₂, lmm₂⟩,
  have lmm₁ : T.maximum_aux (max s₁ s₂) ⊢ p, from provable.inclusion lmm₁ (ss_le maximum_aux_ss (by simp)),
  have lmm₂ : T.maximum_aux (max s₁ s₂) ⊢ ⁻p, from provable.inclusion lmm₂ (ss_le maximum_aux_ss (by simp)),
  have : ¬(T.maximum_aux (max s₁ s₂)).consistent, simp[theory.consistent], refine ⟨p, lmm₁, lmm₂⟩,
  exact this (maximum_consistent_aux con _)
end

def LMmodel := 𝔗[T.maximum]


end fopl