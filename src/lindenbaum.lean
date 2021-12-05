import deduction semantics

universes u t

namespace fopl
variables {L : language.{u}} (T : theory L) (i : ℕ)

local infix ` ≃₁ `:80 := ((≃) : term L → term L → formula L)

local prefix `∏₁ `:64 := (has_univ_quantifier.univ : formula L → formula L)

local prefix `∐₁ `:64 := (has_exists_quantifier.ex : formula L → formula L)

notation t` ≃[`:50 T :50`] `:0 u:50 := term.equiv T t u

@[symm] lemma term.equiv_refl (T : theory L) (t : term L) : t ≃[T] t := by simp[term.equiv]

@[symm] lemma term.equiv_symm (T : theory L) (t u : term L) : (t ≃[T] u) → (u ≃[T] t) := provable.eq_symm

@[trans] lemma term.equiv_trans (T : theory L) (t u s : term L) : (t ≃[T] u) → (u ≃[T] s) → (t ≃[T] s) := provable.eq_trans

theorem term_equiv_equivalence (T : theory L) : equivalence (term.equiv T) :=
⟨@term.equiv_refl _ _, @term.equiv_symm _ _, @term.equiv_trans _ _⟩

@[reducible, simp, instance]
def herbrand (n : ℕ) : setoid (term L) := ⟨λ t₁ t₂, T^n ⊢ t₁ ≃ t₂, term_equiv_equivalence (T^n)⟩

def Herbrand (n : ℕ) : Type u := quotient (herbrand T n)

def term.quo (T : theory L) (n : ℕ) (t : term L) : Herbrand T n := quotient.mk' t

notation `⟦`t`⟧ᴴ` :max := term.quo _ _ t

instance (T : theory L) (n) : inhabited (Herbrand T n) := ⟨⟦#0⟧ᴴ⟩

local infix ` ≃₁ `:80 := ((≃) : term L → term L → formula L)

namespace Herbrand
variables {T} {i}

@[elab_as_eliminator]
protected lemma ind_on {C : Herbrand T i → Prop} (d : Herbrand T i)
  (h : ∀ t : term L, C ⟦t⟧ᴴ) : C d :=
quotient.induction_on' d h

@[elab_as_eliminator, reducible]
protected def lift_on {φ} (d : Herbrand T i) (f : term L → φ)
  (h : ∀ t u : term L, T^i ⊢ t ≃ u → f t = f u) : φ :=
quotient.lift_on' d f h

@[simp]
protected lemma lift_on_eq {φ} (t : term L) (f : term L → φ)
  (h : ∀ t u, T^i ⊢ t ≃ u → f t = f u) : fopl.Herbrand.lift_on (⟦t⟧ᴴ : Herbrand T i) f h = f t := rfl

@[elab_as_eliminator, reducible, simp]
protected def lift_on₂ {φ} (d₁ d₂ : Herbrand T i) (f : term L → term L → φ)
  (h : ∀ t₁ t₂ u₁ u₂, (T^i ⊢ t₁ ≃ u₁) → (T^i ⊢ t₂ ≃ u₂) → f t₁ t₂ = f u₁ u₂) : φ :=
quotient.lift_on₂' d₁ d₂ f h

@[simp]
protected lemma lift_on₂_eq {φ} (t u : term L) (f : term L → term L → φ)
  (h : ∀ t₁ t₂ u₁ u₂, (T^i ⊢ t₁ ≃ u₁) → (T^i ⊢ t₂ ≃ u₂) → f t₁ t₂ = f u₁ u₂) :
  fopl.Herbrand.lift_on₂ ⟦t⟧ᴴ ⟦u⟧ᴴ f h = f t u := rfl

protected def lift_on_finitary {φ} {n : ℕ} (v : finitary (Herbrand T i) n) (f : finitary (term L) n → φ)
  (h : ∀ v₁ v₂ : finitary (term L) n, (∀ n, T^i ⊢ (v₁ n) ≃ (v₂ n)) → f v₁ = f v₂) : φ :=
quotient.lift_on_finitary v f h 

@[simp]
protected lemma lift_on_finitary_eq {φ} {n} (v : finitary (term L) n) (f : finitary (term L) n → φ)
  (h : ∀ v₁ v₂ : finitary (term L) n, (∀ n, T^i ⊢ (v₁ n) ≃ (v₂ n)) → f v₁ = f v₂) :
  fopl.Herbrand.lift_on_finitary (λ x, (⟦v x⟧ᴴ : Herbrand T i)) f h = f v :=
quotient.lift_on_finitary_eq v f h

@[simp]
protected lemma lift_on_finitary_0_eq {φ} (f : finitary (term L) 0 → φ)
  (h : ∀ v₁ v₂ : finitary (term L) 0, (∀ n, T^i ⊢ (v₁ n) ≃ (v₂ n)) → f v₁ = f v₂)
  (n : finitary (Herbrand T i) 0) :
  fopl.Herbrand.lift_on_finitary n f h = f finitary.nil :=
quotient.lift_on_finitary_0_eq f h n

@[simp]
protected lemma lift_on_finitary_1_eq {φ} (t : term L) (f : finitary (term L) 1 → φ)
  (h : ∀ v₁ v₂ : finitary (term L) 1, (∀ n, T^i ⊢ (v₁ n) ≃ (v₂ n)) → f v₁ = f v₂) :
  fopl.Herbrand.lift_on_finitary ‹⟦t⟧ᴴ› f h = f ‹t› :=
quotient.lift_on_finitary_1_eq t f h

@[simp]
protected lemma lift_on_finitary_2_eq {φ} (t u : term L) (f : finitary (term L) 2 → φ)
  (h : ∀ v₁ v₂ : finitary (term L) 2, (∀ n, T^i ⊢ (v₁ n) ≃ (v₂ n)) → f v₁ = f v₂) :
  fopl.Herbrand.lift_on_finitary ‹⟦t⟧ᴴ, ⟦u⟧ᴴ› f h = f ‹t, u› :=
quotient.lift_on_finitary_2_eq t u f h

@[simp]
lemma of_eq_of {t u : term L} : (⟦t⟧ᴴ : Herbrand T i) = ⟦u⟧ᴴ ↔ (T^i ⊢ t ≃ u) :=
by simp[term.quo, term.equiv, quotient.eq']

def function {n} (f : L.fn n) : finitary (Herbrand T i) n → Herbrand T i :=
λ v, fopl.Herbrand.lift_on_finitary v (λ u : finitary (term L) n, ⟦term.app f u⟧ᴴ) 
  $ λ v₁ v₂ eqs, by simp[of_eq_of]; exact provable.equiv_function_of_equiv f eqs

notation `H❨` c `❩` v :84 := function c v

instance [has_zero_symbol L] : has_zero (Herbrand T i) := ⟨function has_zero_symbol.zero finitary.nil⟩

instance [has_succ_symbol L] : has_succ (Herbrand T i) := ⟨λ h, function has_succ_symbol.succ ‹h›⟩

@[simp] def Numeral [has_zero_symbol L] [has_succ_symbol L] : ℕ → Herbrand T i
| 0       := 0
| (n + 1) := Succ (Numeral n)

instance [has_add_symbol L] : has_add (Herbrand T i) := ⟨λ h₁ h₂, function has_add_symbol.add ‹h₁, h₂›⟩

instance [has_mul_symbol L] : has_mul (Herbrand T i) := ⟨λ h₁ h₂, function has_mul_symbol.mul ‹h₁, h₂›⟩


def symbol.pr {n} (p : L.pr n) : finitary (Herbrand T i) n → Prop :=
λ v, fopl.Herbrand.lift_on_finitary v (λ u : finitary (term L) n, T^i ⊢ formula.app p u) 
  $ λ v₁ v₂ eqs, by simp[of_eq_of]; 
  exact ⟨λ h, provable.predicate_of_equiv p h eqs, λ h, provable.predicate_of_equiv p h (λ i, provable.eq_symm (eqs i))⟩

def model (T : theory L) : model L := ⟨Herbrand T 0, ⟨⟦#0⟧ᴴ⟩, @function _ T 0, @symbol.pr _ T 0⟩

notation `𝔗[`T`]` := model T

protected theorem provable_iff {t₁ t₂} : T^i ⊢ t₁ ≃ t₂ ↔ (⟦t₁⟧ᴴ : Herbrand T i) = ⟦t₂⟧ᴴ := by simp[of_eq_of]

protected theorem provable_iff0 {t₁ t₂} : T ⊢ t₁ ≃ t₂ ↔ (⟦t₁⟧ᴴ : Herbrand T 0) = ⟦t₂⟧ᴴ := by simp[of_eq_of]

theorem constant_term (c : L.fn 0) (v : finitary (term L) 0):
  (⟦❨c❩ v⟧ᴴ : Herbrand T i) = function c finitary.nil := by simp[function, show v = finitary.nil, by ext; simp]

@[simp] theorem zero_eq_zero [has_zero_symbol L] :
  (⟦(0 : term L)⟧ᴴ : Herbrand T i) = 0 := by unfold has_zero.zero; simp[function]

@[simp] theorem succ_eq_succ [has_succ_symbol L] (t : term L) :
  (⟦Succ t⟧ᴴ : Herbrand T i) = Succ ⟦t⟧ᴴ := by unfold has_succ.succ; simp[function]

@[simp] theorem numeral_eq_Numeral [has_zero_symbol L] [has_succ_symbol L] (n : ℕ) :
  (⟦(n˙ : term L)⟧ᴴ : Herbrand T i) = Numeral n :=
by induction n; simp[*,numeral]

@[simp] theorem add_eq_add [has_add_symbol L] (t u : term L) :
  (⟦t + u⟧ᴴ : Herbrand T i) = ⟦t⟧ᴴ + ⟦u⟧ᴴ := by unfold has_add.add; simp[function]

@[simp] theorem mul_eq_mul [has_mul_symbol L] (t u : term L) :
  (⟦t * u⟧ᴴ : Herbrand T i) = ⟦t⟧ᴴ * ⟦u⟧ᴴ := by unfold has_mul.mul; simp[function]

def pow : Herbrand T i → Herbrand T (i+1) :=
λ h, Herbrand.lift_on h (λ u, ⟦u^1⟧ᴴ : term L → Herbrand T (i+1)) $
λ t₁ t₂ hyp, by { simp[Herbrand.of_eq_of, ←theory.pow_add] at*,
  rw [show (t₁^1) ≃₁ (t₂^1) = (t₁ ≃ t₂)^1, by simp, provable.sf_itr_sf_itr], exact hyp }

lemma sentence_pow {t : term L} (a : t.arity = 0) :
  (⟦t⟧ᴴ : Herbrand T i).pow = ⟦t⟧ᴴ := by simp[pow, Herbrand.of_eq_of, a]

@[simp] lemma constant_pow (c : L.fn 0) (f : finitary (Herbrand T i) 0) :
  (H❨c❩ f : Herbrand T i).pow = (H❨c❩ finitary.nil : Herbrand T (i + 1)) := sentence_pow (by simp)

@[simp] theorem zero_pow [has_zero_symbol L] :
  (0 : Herbrand T i).pow = 0 := by unfold has_zero.zero; simp

theorem succ_pow [has_succ_symbol L] (h : Herbrand T i) :
  (Succ h).pow = Succ h.pow :=
by { induction h using fopl.Herbrand.ind_on,
     simp[pow, ←succ_eq_succ _, -succ_eq_succ] }

@[simp] theorem numeral_pow [has_zero_symbol L] [has_succ_symbol L] (n : ℕ) :
  (Numeral n : Herbrand T i).pow = Numeral n :=
by induction n; simp[*,numeral, succ_pow]

theorem add_pow [has_add_symbol L] (h₁ h₂ : Herbrand T i) :
  (h₁ + h₂).pow = h₁.pow + h₂.pow :=
by { induction h₁ using fopl.Herbrand.ind_on with t,
     induction h₂ using fopl.Herbrand.ind_on with u,
    simp[pow, ←add_eq_add _ _, -add_eq_add] }

theorem mul_pow [has_mul_symbol L] (h₁ h₂ : Herbrand T i) :
  (h₁ * h₂).pow = h₁.pow * h₂.pow :=
by { induction h₁ using fopl.Herbrand.ind_on with t,
     induction h₂ using fopl.Herbrand.ind_on with u,
    simp[pow, ←mul_eq_mul _ _, -mul_eq_mul] }

@[simp] def sf_simp (t : term L) (j : ℕ) : (⟦t⟧ᴴ : Herbrand T i).pow = ⟦t^1⟧ᴴ := rfl

def var (n : ℕ) : Herbrand T i := ⟦#n⟧ᴴ
prefix `♯`:max := var

@[simp] lemma var_pow (n : ℕ) : (♯n : Herbrand T i).pow= ♯(n + 1) := rfl

namespace proper

@[simp] def subst_sf_H_aux [proper : proper 0 T] (t : term L) :
  Herbrand T (i + 1) → Herbrand T i :=
λ h, Herbrand.lift_on h (λ u, ⟦u.rew ι[i ⇝ t]⟧ᴴ : term L → Herbrand T i) $
λ t₁ t₂ hyp, by { simp[Herbrand.of_eq_of] at*, exact provable.pow_subst' i hyp t }

variables [proper 0 T]

def subst_sf_H : Herbrand T i → Herbrand T (i+1) → Herbrand T i :=
λ t h, Herbrand.lift_on t (λ t, subst_sf_H_aux t h : term L → Herbrand T i) $
λ t₁ t₂ hyp,
by { induction h using fopl.Herbrand.ind_on,
     simp[Herbrand.of_eq_of] at*, 
     refine provable.equal_rew_equal (ι[i ⇝ t₁]) (ι[i ⇝ t₂]) (λ m, _) h,
     have C : m < i ∨ m = i ∨ i < m, from trichotomous m i,
     cases C,
     { simp[C] }, cases C; simp[C], exact hyp }

infix ` ⊳ᴴ ` :90  := subst_sf_H

@[simp] lemma subst_sf_H_sentence (h : Herbrand T i) {t : term L} (a : t.arity = 0) :
  h ⊳ᴴ (⟦t⟧ᴴ : Herbrand T (i+1)) = ⟦t⟧ᴴ :=
by { induction h using fopl.Herbrand.ind_on, simp[subst_sf_H, Herbrand.of_eq_of, a] }

@[simp] lemma subst_sf_H_var_eq (h : Herbrand T i) :
  h ⊳ᴴ ♯i = h :=
by { induction h using fopl.Herbrand.ind_on, simp[subst_sf_H, Herbrand.of_eq_of, var] }

@[simp] lemma subst_sf_H_var_lt (h : Herbrand T i) (j : ℕ) (eqn : j < i) :
  h ⊳ᴴ ♯j = ♯j :=
by { induction h using fopl.Herbrand.ind_on, simp[subst_sf_H, Herbrand.of_eq_of, var, eqn] }

@[simp] lemma subst_sf_H_var_gt (h : Herbrand T i) (j : ℕ) (eqn : i < j) :
  h ⊳ᴴ ♯j = ♯(j - 1) :=
by { induction h using fopl.Herbrand.ind_on, simp[subst_sf_H, Herbrand.of_eq_of, var, eqn] }

end proper

lemma var_eq (n : ℕ) : (⟦#n⟧ᴴ : Herbrand T i) = ♯n := rfl

lemma subst_eq [proper 0 T] (t : term L) :
  (⟦t.rew ι[i ⇝ t]⟧ᴴ : Herbrand T i) = ⟦t⟧ᴴ ⊳ᴴ ⟦t⟧ᴴ := rfl

lemma pow_eq (t : term L) :
  (⟦t^1⟧ᴴ : Herbrand T (i + 1)) = pow ⟦t⟧ᴴ := rfl

end Herbrand

lemma empty_has_model : ∃ 𝔄 : model L, 𝔄 ⊧ₜₕ (∅ : theory L) :=
⟨𝔗[∅], λ p h, by { exfalso, refine set.not_mem_empty p h }⟩

theorem empty_consistent : theory.consistent (∅ : theory L) := @model_consistent L 𝔗[∅] ∅
(λ p h, by { exfalso, refine set.not_mem_empty p h })

@[reducible] def Lindenbaum : Type u := axiomatic_classical_logic.lindenbaum (T^i)

notation `⟦`p`⟧ᴸ` :max := @classical_logic.to_quo _ _ _ _ _ _ _ ((⊢) _) _ p

namespace Lindenbaum
open provable Herbrand classical_logic axiomatic_classical_logic
variables {T} {i}

instance : boolean_algebra (Lindenbaum T i) := axiomatic_classical_logic.lindenbaum.boolean_algebra _

lemma top_def : (⊤ : Lindenbaum T i) = ⟦⊤⟧ᴸ := rfl

lemma bot_def : (⊥ : Lindenbaum T i) = ⟦⊥⟧ᴸ := rfl

@[simp]
protected lemma of_eq_of {p q : formula L} : (⟦p⟧ᴸ : Lindenbaum T i) = ⟦q⟧ᴸ ↔ T^i ⊢ p ⟷ q :=
by simp[formula.equiv, quotient.eq']

def predicate {n} (p : L.pr n) : finitary (Herbrand T i) n → Lindenbaum T i :=
λ v, fopl.Herbrand.lift_on_finitary v (λ u : finitary (term L) n, ⟦formula.app p u⟧ᴸ) 
  $ λ v₁ v₂ eqs, by simp; exact equiv_predicate_of_equiv p eqs

notation `L❴` f `❵` := predicate f

instance [has_le_symbol L] : has_preceq (Herbrand T i) (Lindenbaum T i) := ⟨λ h₁ h₂, predicate has_le_symbol.le ‹h₁, h₂›⟩

instance [has_mem_symbol L] : has_elem (Herbrand T i) (Lindenbaum T i) := ⟨λ h₁ h₂, predicate has_mem_symbol.mem ‹h₁, h₂›⟩

@[simp] theorem predicate_app_1_iff {p : L.pr 1} {v : finitary (term L) 1} :
  (⟦❴p❵ v⟧ᴸ : Lindenbaum T i) = L❴p❵ ‹⟦v 0⟧ᴴ› := by simp[predicate, show ‹v 0› = v, by ext; simp]

@[simp] theorem predicate_app_2_iff {p : L.pr 2} {v : finitary (term L) 2} :
  (⟦❴p❵ v⟧ᴸ : Lindenbaum T i) = L❴p❵ ‹⟦v 0⟧ᴴ, ⟦v 1⟧ᴴ› := by simp[predicate, show ‹v 0, v 1› = v, by ext; simp]

@[simp] theorem le_iff_le [has_le_symbol L] (t u : term L) :
  (⟦t ⩽ u⟧ᴸ : Lindenbaum T i) = ((⟦t⟧ᴴ : Herbrand T i) ⩽ ⟦u⟧ᴴ) := by unfold has_preceq.preceq; simp

@[simp] theorem mem_iff_mem [has_mem_symbol L] (t u : term L) :
  (⟦t ∊ u⟧ᴸ : Lindenbaum T i) = ((⟦t⟧ᴴ : Herbrand T i) ∊ ⟦u⟧ᴴ) := by unfold has_elem.elem; simp

def equal : Herbrand T i → Herbrand T i → Lindenbaum T i :=
λ h₁ h₂, fopl.Herbrand.lift_on₂ h₁ h₂ (λ t₁ t₂, (⟦t₁ ≃ t₂⟧ᴸ : Lindenbaum T i)) $
λ t₁ t₂ u₁ u₂ eqn₁ eqn₂, by simp; exact equiv_eq_of_equiv eqn₁ eqn₂

instance : has_eq (Herbrand T i) (Lindenbaum T i) := ⟨equal⟩

local infix ` ≃ᴸ `:80 := ((≃) : Herbrand T i → Herbrand T i → Lindenbaum T i)

lemma equal_def (t u : term L) : ⟦t⟧ᴴ ≃ᴸ ⟦u⟧ᴴ = ⟦t ≃ u⟧ᴸ := rfl

def univ : Lindenbaum T (i+1) → Lindenbaum T i :=
λ p, classical_logic.lindenbaum.lift_on p (λ p, (⟦∏ p⟧ᴸ : Lindenbaum T i)) $
λ p₁ p₂ hyp, by simp at hyp ⊢; exact equiv_univ_of_equiv hyp

instance : has_univ_quantifier (Lindenbaum T (i + 1)) (Lindenbaum T i) := ⟨univ⟩

lemma univ_def (p : formula L) : (∏ (⟦p⟧ᴸ : Lindenbaum T (i + 1)) : Lindenbaum T i) = ⟦∏ p⟧ᴸ := rfl

def exist : Lindenbaum T (i+1) → Lindenbaum T i :=
λ p, classical_logic.lindenbaum.lift_on p (λ p, (⟦∐ p⟧ᴸ : Lindenbaum T i)) $
λ p₁ p₂ hyp, by simp at hyp ⊢; exact equiv_ex_of_equiv hyp

instance : has_exists_quantifier (Lindenbaum T (i + 1)) (Lindenbaum T i) := ⟨exist⟩

lemma exist_def (p : formula L) : (∐ (⟦p⟧ᴸ : Lindenbaum T (i + 1)) : Lindenbaum T i) = ⟦∐ p⟧ᴸ := rfl

@[simp] lemma equal_refl {h : Herbrand T i}  : h ≃ᴸ h = ⊤ :=
by { induction h using fopl.Herbrand.ind_on;
     simp only [has_eq.eq, equal, top_def], simp[axiomatic_classical_logic'.iff_equiv], }

lemma equal_iff {h₁ h₂ : Herbrand T i} {p : L.pr 1} : h₁ ≃ᴸ h₂ = ⊤ ↔ h₁ = h₂ :=
by { induction h₁ using fopl.Herbrand.ind_on, induction h₂ using fopl.Herbrand.ind_on,
     simp only [has_eq.eq, equal, top_def], simp[axiomatic_classical_logic'.iff_equiv] }

def pow : Lindenbaum T i → Lindenbaum T (i+1) :=
λ p, lindenbaum.lift_on p (λ p, (⟦p^1⟧ᴸ : Lindenbaum T (i+1))) $
λ p₁ p₂ hyp, by { simp[contrapose, ←theory.pow_add, -axiomatic_classical_logic'.iff_equiv] at*,
  exact sf_itr_sf_itr.mpr hyp }

lemma sentence_pow {p : formula L} (a : sentence p) :
  pow (⟦p⟧ᴸ : Lindenbaum T i) = ⟦p⟧ᴸ := by simp[pow, a]

@[simp] lemma pow_compl (l : Lindenbaum T i) : pow (lᶜ) = (pow l)ᶜ :=
by { induction l using classical_logic.lindenbaum.ind_on, simp[pow, classical_logic.lindenbaum.neg_def] }

@[simp] lemma pow_sup (l m : Lindenbaum T i) : pow (l ⊔ m) = (pow l) ⊔ (pow m) :=
by { induction l using classical_logic.lindenbaum.ind_on, induction m using classical_logic.lindenbaum.ind_on,
     simp[pow, classical_logic.lindenbaum.sup_def] }

@[simp] lemma pow_inf (l m : Lindenbaum T i) : pow (l ⊓ m) = (pow l) ⊓ (pow m) :=
by { induction l using classical_logic.lindenbaum.ind_on, induction m using classical_logic.lindenbaum.ind_on,
     simp[pow, classical_logic.lindenbaum.inf_def] }

@[simp] lemma prod_top : (∏ (⊤ : Lindenbaum T (i+1)) : Lindenbaum T i) = ⊤ :=
by { simp only [top_def, has_univ_quantifier.univ, univ], simp[axiomatic_classical_logic'.iff_equiv], apply provable.generalize, simp }

lemma prenex_ex_neg (l : Lindenbaum T (i+1)) : (∐ l : Lindenbaum T i)ᶜ = ∏ lᶜ :=
by { induction l using classical_logic.lindenbaum.ind_on,
     simp[-axiomatic_classical_logic'.iff_equiv, formula.ex_eq, univ_def, exist_def, classical_logic.lindenbaum.neg_def] }

lemma prenex_fal_neg {l : Lindenbaum T (i+1)} : (∏ l : Lindenbaum T i)ᶜ = ∐ lᶜ :=
by { have := prenex_ex_neg lᶜ, simp[-prenex_ex_neg] at this, simp[←this] }

lemma prenex_fal_or_left {l : Lindenbaum T (i+1)} {k : Lindenbaum T i} :
  (∏ l) ⊔ k = ∏ l ⊔ k.pow :=
begin
  induction l using classical_logic.lindenbaum.ind_on with p, induction k using classical_logic.lindenbaum.ind_on with q,
  simp[pow, axiomatic_classical_logic'.iff_equiv, univ_def, classical_logic.lindenbaum.sup_def], split,
  { refine (deduction.mp $ generalize $ contrapose.mp _), simp [←sf_dsb],
    have lmm₁ : ⤊(T^i) +{ ⁻(∏ p)^1 ⟶ q^1 } ⊢ ⁻q^1 ⟶ (∏ p)^1, { refine contrapose.mp _, simp },
    have lmm₂ : ⤊(T^i) +{ ⁻(∏ p)^1 ⟶ q^1 } ⊢ (∏ p)^1 ⟶ p,
    { suffices : ⤊(T^i) +{ ⁻(∏ p)^1 ⟶ q^1 } ⊢ (∏ p)^1 ⟶ (p.rew $ (λ x, #(x + 1))^1).rew ι[0 ⇝ #0],
      { simp[formula.nested_rew] at this, exact this },
      exact provable.q1 }, 
    exact impl_trans lmm₁ lmm₂ },
  { refine (deduction.mp $ contrapose.mp _), simp[←sf_dsb],
    refine deduction.mp (generalize _), simp[←sf_dsb],
    suffices : ⤊(T^i)+{(∏  (⁻p ⟶ q^1))^1} ⊢ ⁻q^1 ⟶ p, { from deduction.mpr this },
    have :     ⤊(T^i)+{(∏  (⁻p ⟶ q^1))^1} ⊢ ⁻p ⟶ q^1,
    { have : ⤊(T^i)+{(∏  (⁻p ⟶ q^1))^1} ⊢ (∏  (⁻p ⟶ q^1))^1, { simp },
      have lmm₁ := fal_subst this #0, simp at lmm₁,
      simp[formula.nested_rew] at lmm₁,
      exact lmm₁ },
    refine contrapose.mp _, simp[this] }
end

lemma prenex_fal_or_right {l : Lindenbaum T i} {k : Lindenbaum T (i+1)} :
  l ⊔ ∏ k = ∏ (l.pow ⊔ k) :=
by simp[show l ⊔ (∏ k) = (∏ k) ⊔ l, from sup_comm, prenex_fal_or_left,
        show k ⊔ l.pow = l.pow ⊔ k, from sup_comm]

lemma prenex_fal_and_left {l : Lindenbaum T (i+1)} {k : Lindenbaum T i} :
  (∏ l) ⊓ k = ∏ l ⊓ k.pow :=
begin
  induction l using classical_logic.lindenbaum.ind_on, induction k using classical_logic.lindenbaum.ind_on,
  simp[pow, axiomatic_classical_logic'.iff_equiv, univ_def, classical_logic.lindenbaum.inf_def], split,
  { refine (deduction.mp $ generalize _), rw [←sf_dsb], simp[axiom_and],
    have : ⤊(T^i) +{ (∏  l)^1 } +{ k^1 } ⊢ (∏ l)^1, simp,
    have := fal_subst this #0, simp[formula.nested_rew] at this,
    exact this },
  { refine deduction.mp _, simp, split,
    { refine generalize _, simp[←sf_dsb],
      have : ⤊(T^i) +{ (∏ l ⊓ (k^1))^1 } ⊢ (∏ l ⊓ (k^1))^1, simp,
      have := fal_subst this #0, simp[formula.nested_rew] at this, simp* at* },
    { have : (T^i) +{ ∏ l ⊓ (k^1) } ⊢ ∏ l ⊓ (k^1), simp,
      have := fal_subst this #0, simp* at * } }
end

lemma prenex_ex_or_left {l : Lindenbaum T (i+1)} {k : Lindenbaum T i} :
  (∐ l) ⊔ k = ∐ (l ⊔ k.pow) :=
by rw ← compl_inj_iff; simp[-compl_inj_iff, prenex_ex_neg, prenex_fal_and_left]


namespace proper

variables [proper 0 T]

@[simp] def subst_sf_L_aux (t : term L) :
  Lindenbaum T (i+1) → Lindenbaum T i :=
λ p, classical_logic.lindenbaum.lift_on p (λ p, (⟦p.rew (ι[i ⇝ t])⟧ᴸ : Lindenbaum T i)) $
λ p₁ p₂ hyp, by { simp at*,
    exact provable.pow_subst' i hyp t }

def subst_sf_L : Herbrand T i → Lindenbaum T (i+1) → Lindenbaum T i :=
λ t l, Herbrand.lift_on t (λ t, subst_sf_L_aux t l) $
λ t₁ t₂ hyp, by { induction l using classical_logic.lindenbaum.ind_on,
  simp at*,
  refine equal_rew_iff (λ m, _) l,
  have C : m < i ∨ m = i ∨ i < m, from trichotomous _ _,
  cases C,
  { simp[C] }, cases C; simp[C],
  { refine hyp } }
infixr ` ⊳ `:90  := subst_sf_L

lemma fal_le_subst (l : Lindenbaum T (i + 1)) (h : Herbrand T i) : ∏ (♯0 ⊳ l.pow) ≤ h ⊳ l :=
begin
  induction l using classical_logic.lindenbaum.ind_on with p, 
  induction h using fopl.Herbrand.ind_on with t,
  simp[pow],
  have : T^i ⊢ ∏ (p^1).rew ι[(i + 1) ⇝ #0] ⟶ ((p^1).rew ι[(i + 1) ⇝ #0]).rew ι[0 ⇝ t],
    from @specialize _ (T^i) ((p^1).rew ι[(i + 1) ⇝ #0]) t,
  have eqn : (((p^1).rew ι[(i + 1) ⇝ #0]).rew ι[0 ⇝ t]) = p.rew ι[i ⇝ t],
  { simp[formula.nested_rew, formula.pow_eq], congr,
    funext x, have C : i < x ∨ i = x ∨ x < i, exact trichotomous i x,
    cases C, { simp[C, pos_of_gt C] }, cases C;
    simp[C] },
  rw eqn at this,
  exact this
end

lemma fal_le_subst0 (l : Lindenbaum T 1) (h) : ∏ l ≤ (h ⊳ l) :=
begin
  induction l using classical_logic.lindenbaum.ind_on with p, 
  induction h using fopl.Herbrand.ind_on with t, 
  simp[subst_sf_L, univ_def, classical_logic.lindenbaum.le_def]
end


lemma subst_sf_L_le_ex (l : Lindenbaum T 1) (h) : h ⊳ l ≤ ∐ l :=
begin
  induction l using classical_logic.lindenbaum.ind_on, 
  induction h using fopl.Herbrand.ind_on, 
  simp[exist_def, subst_sf_L, formula.ex_eq, classical_logic.lindenbaum.le_def],
  refine contrapose.mp _, simp[formula.ex],
  rw (show ⁻(l.rew ι[0 ⇝ h]) = (⁻l).rew ι[0 ⇝ h], by simp), 
  exact specialize _ _
end

lemma le_fal_le_fal {l m : Lindenbaum T (i + 1)} :
  l ≤ m → (∏ l : Lindenbaum T i) ≤ ∏ m :=
begin
  induction l using classical_logic.lindenbaum.ind_on, 
  induction m using classical_logic.lindenbaum.ind_on, 
  simp[subst_sf_L, pow, classical_logic.lindenbaum.le_def],
  { intros h, refine provable.q2.MP (GE h) },
end

@[simp] lemma dummy_fal (l : Lindenbaum T i) : ∏ pow l = l :=
by { symmetry,
     induction l using classical_logic.lindenbaum.ind_on, 
     simp[pow, univ_def],
     exact @provable.dummy_fal_quantifir _ (T^i) l }

lemma pow_le_le_fal {l : Lindenbaum T i} {m : Lindenbaum T (i + 1)} :
  l.pow ≤ m → l ≤ ∏ m :=
by { have := @le_fal_le_fal _ _ _ _ l.pow m, simp at this, exact this }

@[simp] lemma subst_sf_L_compl (h : Herbrand T i) (l : Lindenbaum T (i+1)) :
  h ⊳ (lᶜ)= (h ⊳ l)ᶜ :=
by { induction l using classical_logic.lindenbaum.ind_on, 
     induction h using fopl.Herbrand.ind_on,
     simp[subst_sf_L, Lindenbaum.of_eq_of, classical_logic.lindenbaum.neg_def] }

@[simp] lemma subst_sf_L_and (h : Herbrand T i) (l m : Lindenbaum T (i+1)) :
  h ⊳ (l ⊓ m) = h ⊳ l ⊓ h ⊳ m :=
by { induction l using classical_logic.lindenbaum.ind_on, induction m using classical_logic.lindenbaum.ind_on, 
     induction h using fopl.Herbrand.ind_on,
     simp[subst_sf_L, classical_logic.lindenbaum.inf_def] }

@[simp] lemma subst_sf_L_or (h : Herbrand T i) (l m : Lindenbaum T (i+1)) :
  h ⊳ (l ⊔ m) = h ⊳ l ⊔ h ⊳ m :=
by { induction l using classical_logic.lindenbaum.ind_on, induction m using classical_logic.lindenbaum.ind_on, 
     induction h using fopl.Herbrand.ind_on,
     simp[subst_sf_L, lindenbaum.sup_def] }

@[simp] lemma subst_sf_L_equal (h₁ : Herbrand T i) (h₂ h₃ : Herbrand T (i+1)) :
  h₁ ⊳ (h₂ ≃ h₃) = ((h₁ ⊳ᴴ h₂) ≃ (h₁ ⊳ᴴ h₃)) :=
by { induction h₁ using fopl.Herbrand.ind_on, induction h₂ using fopl.Herbrand.ind_on,
     induction h₃ using fopl.Herbrand.ind_on,
     simp[subst_sf_L, Herbrand.proper.subst_sf_H, Herbrand.proper.subst_sf_H_aux, equal_def] }

@[simp] lemma subst_sf_L_fal (h : Herbrand T i) (l : Lindenbaum T (i+2)) :
  h ⊳ ∏ l = ∏ (h.pow ⊳ l) :=
by { induction l using classical_logic.lindenbaum.ind_on,
     induction h using fopl.Herbrand.ind_on,
     simp[subst_sf_L, Herbrand.pow, pow, subst_pow, univ_def] }

@[simp] lemma subst_sf_L_ex (h : Herbrand T i) (l : Lindenbaum T (i+2)) :
  h ⊳ ∐ l = ∐ (h.pow ⊳ l) :=
by { induction l using classical_logic.lindenbaum.ind_on,
     induction h using fopl.Herbrand.ind_on,
     simp[subst_sf_L, Herbrand.pow, pow, subst_pow, exist_def] }

lemma subst_sf_L_sentence (h : Herbrand T i) {p : formula L} (a : sentence p) :
  h ⊳ (⟦p⟧ᴸ : Lindenbaum T (i+1)) = ⟦p⟧ᴸ :=
by { induction h using fopl.Herbrand.ind_on, simp[subst_sf_L, Lindenbaum.of_eq_of, a] }

lemma ex_subst_le (l : Lindenbaum T (i + 1)) (h : Herbrand T i) : h ⊳ l ≤ ∐ (♯0 ⊳ l.pow) :=
begin
  suffices : (∐ (♯0 ⊳ pow l))ᶜ ≤ (h ⊳ l)ᶜ,
  { exact compl_le_compl_iff_le.mp this },
  simp[prenex_ex_neg, -compl_le_compl_iff_le], 
  have := fal_le_subst lᶜ h, simp at this, exact this
end

@[simp] lemma pow_fal1 (l : Lindenbaum T 1) : pow (∏ l : Lindenbaum T 0) = ∏ (♯0 ⊳ pow (pow l)) :=
by { induction l using classical_logic.lindenbaum.ind_on, 
     simp[pow, subst_sf_L, var, formula.pow_eq, formula.nested_rew, rewriting_sf_itr.pow_eq', univ_def],
     have : (λ x, ite (x = 0) #x #(x - 1 + 1 + 1) : ℕ → term L) = (λ x, ι[(1 + 1) ⇝ #0] (x + 1 + 1)),
     { funext x, simp[slide', ι], cases x; simp[← nat.add_one] },
     simp [this] }

end proper

@[elab_as_eliminator]
protected lemma ind_on {C : Lindenbaum T i → Prop} (d : Lindenbaum T i)
  (h : ∀ p : formula L, C ⟦p⟧ᴸ) : C d :=
quotient.induction_on' d h

@[simp] lemma compl_sup_iff_le (l m : Lindenbaum T i) : lᶜ ⊔ m = ⊤ ↔ l ≤ m :=
by { induction l using classical_logic.lindenbaum.ind_on,
     induction m using classical_logic.lindenbaum.ind_on,
     simp[top_def, show ⁻l ⊔ m = ⁻⁻l ⟶ m, by refl, axiomatic_classical_logic'.iff_equiv,
          lindenbaum.neg_def, lindenbaum.sup_def, lindenbaum.le_def], }

@[simp] lemma fal_top_top : (∏ (⊤ : Lindenbaum T (i + 1)) : Lindenbaum T i) = ⊤ :=
by { simp[top_def, axiomatic_classical_logic'.iff_equiv, univ_def], refine generalize (by simp) }

@[simp] lemma ex_top_top : (∐ (⊤ : Lindenbaum T (i + 1)) : Lindenbaum T i) = ⊤ :=
by { simp[top_def, axiomatic_classical_logic'.iff_equiv, exist_def], refine provable.use #0 (by simp) }

theorem provable_top_iff {p} : T^i ⊢ p ↔ (⟦p⟧ᴸ : Lindenbaum T i) = ⊤ := by simp[top_def, axiomatic_classical_logic'.iff_equiv]

theorem provable_top_iff0 {p} : T ⊢ p ↔ (⟦p⟧ᴸ : Lindenbaum T 0) = ⊤ := by simp[top_def, axiomatic_classical_logic'.iff_equiv]

protected theorem provable_iff {p q} : T^i ⊢ p ⟷ q ↔ (⟦p⟧ᴸ : Lindenbaum T i) = ⟦q⟧ᴸ := by simp

protected theorem provable_iff0 {p q} : T ⊢ p ⟷ q ↔ (⟦p⟧ᴸ : Lindenbaum T 0) = ⟦q⟧ᴸ := by simp

theorem provable_imp_iff {p q} : T^i ⊢ p ⟶ q ↔ (⟦p⟧ᴸ : Lindenbaum T i) ≤ ⟦q⟧ᴸ := by refl

theorem provable_imp_iff0 {p q} : T ⊢ p ⟶ q ↔ (⟦p⟧ᴸ : Lindenbaum T 0) ≤ ⟦q⟧ᴸ := by refl

@[simp] lemma provable_top_eq : (⟦⊤⟧ᴸ : Lindenbaum T i) = ⊤ := rfl

@[simp] lemma provable_bot_eq : (⟦⊥⟧ᴸ : Lindenbaum T i) = ⊥ := rfl

@[simp] theorem provable_and_eq {p q} : (⟦p ⊓ q⟧ᴸ : Lindenbaum T i) = ⟦p⟧ᴸ ⊓ ⟦q⟧ᴸ := rfl

@[simp] theorem provable_or_eq {p q} : (⟦p ⊔ q⟧ᴸ : Lindenbaum T i) = ⟦p⟧ᴸ ⊔ ⟦q⟧ᴸ := rfl

theorem provable_neg_eq {p} : (⟦⁻p⟧ᴸ : Lindenbaum T i) = ⟦p⟧ᴸᶜ := rfl

@[simp] theorem provable_imp_eq {p q} : (⟦p ⟶ q⟧ᴸ : Lindenbaum T i) = ⟦p⟧ᴸᶜ ⊔ ⟦q⟧ᴸ := by {
  have : (⟦p ⟶ q⟧ᴸ : Lindenbaum T i) = ⟦⁻p ⊔ q⟧ᴸ, 
  { simp[-provable_or_eq, formula.or, axiomatic_classical_logic'.iff_equiv], simp only [has_sup.sup, formula.or],
    refine ⟨deduction.mp (by { simp }), deduction.mp _⟩,
    refine imply_of_equiv (show (T^i)+{⁻⁻p ⟶ q} ⊢ ⁻⁻p ⟶ q, by simp[-dn1_iff]) _ _; simp },
  exact this }

lemma subst_eq [proper 0 T] (p : formula L) (t : term L) :
  (⟦p.rew ι[i ⇝ t]⟧ᴸ : Lindenbaum T i) = ⟦t⟧ᴴ ⊳ ⟦p⟧ᴸ := rfl

lemma pow_eq (p : formula L) :
  (⟦p^1⟧ᴸ : Lindenbaum T (i + 1)) = pow ⟦p⟧ᴸ := rfl
lemma provable_equal_eq {t₁ t₂} : (⟦t₁ ≃ t₂⟧ᴸ : Lindenbaum T i) = ⟦t₁⟧ᴴ ≃ᴸ ⟦t₂⟧ᴴ := rfl

lemma equiv_eq_top_iff {p q} : (⟦p ⟷ q⟧ᴸ : Lindenbaum T i) = ⊤ ↔ (⟦p⟧ᴸ : Lindenbaum T i) = ⟦q⟧ᴸ :=
by simp[provable_top_iff]

@[simp] theorem provable_fal_eq {p : formula L} : (⟦∏ p⟧ᴸ : Lindenbaum T i) = ∏ (⟦p⟧ᴸ : Lindenbaum T (i + 1)) := rfl

@[simp] theorem provable_ex_eq {p : formula L} : (⟦∐ p⟧ᴸ : Lindenbaum T i) = ∐ (⟦p⟧ᴸ : Lindenbaum T (i + 1)) := rfl

lemma to_Herbrand {h₁ h₂ : Herbrand T i} : h₁ ≃ᴸ h₂ = ⊤ ↔ h₁ = h₂ :=
by { induction h₁ using fopl.Herbrand.ind_on, induction h₂ using fopl.Herbrand.ind_on,
     simp only [equal_def, top_def],
     simp[-provable_equal_eq, -provable_top_eq, axiomatic_classical_logic'.iff_equiv] }

theorem provable_neg_iff {p} : T^i ⊢ ⁻p ↔ (⟦p⟧ᴸ : Lindenbaum T i) = ⊥ :=
by simp [provable_top_iff, ←lindenbaum.neg_def]

end Lindenbaum

lemma Lindenbaum.theory (C : theory L) (i : ℕ) : set (Lindenbaum T i) := {l | ∃ p, p ∈ C ∧ l = ⟦p⟧ᴸ}

end fopl