import deduction semantics

universes u v

namespace fopl
variables {L : language.{u}} (T : theory L)

@[simp] def vecterm.equiv (T : theory L) : ∀ n, vecterm L n → vecterm L n → Prop := λ _ v₁ v₂, T ⊢̇ v₁ ≡̇ v₂

notation v` ≃[`T :80`] `u:60 := vecterm.equiv T _ v u

@[simp] lemma veq_eq (t u : vecterm L 0) : t ≡̇ u = t =̇ u := rfl

@[simp] lemma vecterm.equiv_refl (T : theory L) : ∀ {n} (v : vecterm L n), T ⊢̇ v ≡̇ v
| 0     _                  := by simp[vecterm.equiv]
| (n+1) (vecterm.cons t v) := by { simp[vecterm.equiv], exact vecterm.equiv_refl v}

private lemma vecterm.equiv_symm (T : theory L) : ∀ {n} {v₁ v₂ : vecterm L n},
  T ⊢̇ v₁ ≡̇ v₂ → T ⊢̇ v₂ ≡̇ v₁
| 0     _                    _                    := by simp[vecterm.equiv, provable.eq_symm]
| (n+1) (vecterm.cons t₁ v₁) (vecterm.cons t₂ v₂) :=
    by { simp[vecterm.equiv, provable.eq_symm], refine λ h₁ h₂, ⟨h₁, vecterm.equiv_symm h₂⟩ }

private lemma vecterm.equiv_trans (T : theory L) : ∀ {n} {v₁ v₂ v₃ : vecterm L n},
  T ⊢̇ v₁ ≡̇ v₂ → T ⊢̇ v₂ ≡̇ v₃ → T ⊢̇ v₁ ≡̇ v₃
| 0     _                 _ _ := by simp[vecterm.equiv]; exact provable.eq_trans
| (n+1) (vecterm.cons t₁ v₁) (vecterm.cons t₂ v₂) (vecterm.cons t₃ v₃) := 
    by {simp[vecterm.equiv], refine λ e₁ h₁ e₂ h₂, ⟨provable.eq_trans e₁ e₂, vecterm.equiv_trans h₁ h₂⟩ }

theorem vecterm_equiv_equivalence (T : theory L) : equivalence (λ t₁ t₂, T ⊢̇ t₁ =̇ t₂) :=
⟨λ _, by simp, λ _ _ , provable.eq_symm.mp, λ _ _ _, provable.eq_trans⟩

@[reducible, simp, instance]
def herbrand : setoid (term L) := ⟨λ t₁ t₂, T ⊢̇ t₁ =̇ t₂, vecterm_equiv_equivalence T⟩

def Herbrand : Type u := quotient (herbrand T)

def vecterm.quo (T : theory L) (t : term L) : Herbrand T := quotient.mk' t

notation `⟦`v`⟧ᴴ.`T :max := vecterm.quo T v
notation `⟦`v`⟧ᴴ` :max := vecterm.quo _ v

local infix ` ≋ `:80 := (@setoid.vec_r _ (herbrand T) _)

instance (T : theory L) : inhabited (Herbrand T) := ⟨⟦#0⟧ᴴ.T⟩

namespace Herbrand
variables {T}

@[elab_as_eliminator]
protected lemma ind_on {C : Herbrand T → Prop} (d : Herbrand T)
  (h : ∀ t : term L, C ⟦t⟧ᴴ.T) : C d :=
quotient.induction_on' d h

@[elab_as_eliminator, reducible]
protected def lift_on {φ} (d : Herbrand T) (f : term L → φ)
  (h : ∀ v u : term L, T ⊢̇ v =̇ u → f v = f u) : φ :=
quotient.lift_on' d f h

@[simp]
protected lemma lift_on_eq {φ} (t : term L) (f : term L → φ)
  (h : ∀ v u, T ⊢̇ v =̇ u → f v = f u) : fopl.Herbrand.lift_on ⟦t⟧ᴴ.T f h = f t := rfl

@[elab_as_eliminator, reducible, simp]
protected def lift_on₂ {φ} (d₁ d₂ : Herbrand T) (f : term L → term L → φ)
  (h : ∀ t₁ t₂ u₁ u₂, (T ⊢̇ t₁ =̇ u₁) → (T ⊢̇ t₂ =̇ u₂) → f t₁ t₂ = f u₁ u₂) : φ :=
quotient.lift_on₂' d₁ d₂ f h

@[simp]
protected lemma lift_on₂_eq {φ} (t u : term L) (f : term L → term L → φ)
  (h : ∀ t₁ t₂ u₁ u₂, (T ⊢̇ t₁ =̇ u₁) → (T ⊢̇ t₂ =̇ u₂) → f t₁ t₂ = f u₁ u₂) :
  fopl.Herbrand.lift_on₂ ⟦t⟧ᴴ.T ⟦u⟧ᴴ.T f h = f t u := rfl

lemma of_eq_of {t u : term L} : ⟦t⟧ᴴ.T = ⟦u⟧ᴴ.T ↔ (T ⊢̇ t =̇ u) :=
by simp[vecterm.quo, vecterm.equiv, quotient.eq']

@[elab_as_eliminator, reducible]
protected def lift_on_vec {φ} {n} (v : dvector (Herbrand T) n) (f : dvector (term L) n → φ)
  (h : ∀ (a b : dvector (term L) n), a ≋ b → f a = f b) : φ :=
quotient.lift_on_vec v f h

@[simp]
protected lemma lift_on_vec_eq {φ} {n} (u : dvector (term L) n) (f : dvector (term L) n → φ)
  (h : ∀ (v u : dvector (term L) n), v ≋ u → f v = f u) :
fopl.Herbrand.lift_on_vec ᵥ⟦u⟧ f h = f u := quotient.lift_on_vec_eq u f h

@[simp] lemma equivs_equals : ∀ {n} (v₁ v₂ : dvector (term L) (n+1)),
  v₁ ≋ v₂ ↔ (T ⊢̇ v₁.to_vecterm ≡̇ v₂.to_vecterm)
| 0 (t₁ :: dvector.nil) (t₂ :: dvector.nil) := by { simp, refl }
| (n+1) (t₁ :: v₁) (t₂ :: v₂) := by { simp[equivs_equals v₁ v₂], intros, refl }

def symbol.fn : ∀ {n} (f : L.fn n), dvector (Herbrand T) n → Herbrand T
| 0     c _ := ⟦vecterm.const c⟧ᴴ.T
| (n+1) f v := fopl.Herbrand.lift_on_vec v (λ u : dvector (term L) (n+1), ⟦vecterm.app f (u.to_vecterm)⟧ᴴ.T) 
  $ λ v₁ v₂ eqn, by { simp[of_eq_of] at*, refine provable.e4.MP eqn }

def function₀ (T : theory L) (c : L.fn 0) : Herbrand T := symbol.fn c dvector.nil

def function₁ (T : theory L) (f : L.fn 1) (h : Herbrand T) : Herbrand T := symbol.fn f (h :: dvector.nil)

def function₂ (T : theory L) (f : L.fn 2) (h₁ h₂ : Herbrand T) : Herbrand T := symbol.fn f (h₁ :: h₂ :: dvector.nil)

def symbol.pr : ∀ {n} (f : L.pr n), dvector (Herbrand T) n → Prop
| 0     c _ := T ⊢̇ formula.const c
| (n+1) p v := fopl.Herbrand.lift_on_vec v (λ u : dvector (term L) (n+1), T ⊢̇ formula.app p (u.to_vecterm))
  $ λ v₁ v₂ eqn, by { simp at*, refine ⟨(provable.e5.MP eqn).MP, (provable.e5.MP (vecterm.equiv_symm _ eqn)).MP⟩  }

def model (T : theory L) : model L := ⟨Herbrand T, ⟦#0⟧ᴴ.T, @symbol.fn _ T, @symbol.pr _ T⟩
notation `𝔗[`T`]` := model T

protected theorem provable_iff {t₁ t₂} : T ⊢̇ t₁ =̇ t₂ ↔ ⟦t₁⟧ᴴ.T = ⟦t₂⟧ᴴ.T := by simp[of_eq_of]

@[simp] theorem const_function₀_eq {c : L.fn 0} : ⟦vecterm.const c⟧ᴴ.T = function₀ T c := rfl
@[simp] theorem vecterm_app_function₁_eq {f : L.fn 1} {t} : ⟦vecterm.app f t⟧ᴴ.T = function₁ T f ⟦t⟧ᴴ.T := rfl 
@[simp] theorem vecterm_app_function₂_eq {f : L.fn 2} {t₁ t₂} :
  ⟦vecterm.app f (vecterm.cons t₁ t₂)⟧ᴴ.T = function₂ T f ⟦t₁⟧ᴴ.T ⟦t₂⟧ᴴ.T := rfl 

namespace proper
variables [proper 0 T]

@[simp] def subst_sf_H_aux (t : term L) (n : ℕ) :
  Herbrand (theory.sf_itr T (n+1)) → Herbrand (theory.sf_itr T n) :=
λ h, Herbrand.lift_on h (λ u, ⟦u.rew ss[t // n]⟧ᴴ.(theory.sf_itr T n)) $
λ t₁ t₂ hyp, by { 
  simp[Herbrand.of_eq_of, -provable.iff] at*,
  have := (provable.GE hyp).fal_subst t,
  have := provable.ppc_prove_rew n this, simp[formula.nested_rew] at this,
  exact this }

def subst_sf_H (n : ℕ) : Herbrand T → Herbrand (theory.sf_itr T n) → Herbrand (theory.sf_itr T n) :=
λ t h, Herbrand.lift_on t (λ t, subst_sf_H_aux t n h) $
λ t₁ t₂ hyp, by { induction h using fopl.Herbrand.ind_on,
  simp[Herbrand.of_eq_of, -provable.iff] at*, 
  refine provable.equal_rew_equals_term h ss[t₁ // n] ss[t₂ // n] (λ m, _),
  have C : m < n ∨ m = n ∨ n < m, from trichotomous m n,
  cases C,
  { simp[C] }, cases C; simp[C],
  have := provable.sf_itr_sf_itr.mpr hyp, simp at this, refine this }
notation h₁ ` ⊳ᴴ[`:90 n `] `h₂ :90  := subst_sf_H n h₁ h₂

@[simp] lemma subst_sf_H_function₁ {n} {h₁ : Herbrand T} {h₂ : Herbrand (theory.sf_itr T n)} {f} :
  h₁ ⊳ᴴ[n] (function₁ _ f h₂) = function₁ _ f (h₁ ⊳ᴴ[n] h₂) :=
by { induction h₁ using fopl.Herbrand.ind_on, induction h₂ using fopl.Herbrand.ind_on,
     rw ← vecterm_app_function₁_eq,
     simp[-vecterm_app_function₁_eq, subst_sf_H, Herbrand.of_eq_of], refl }

@[simp] lemma subst_sf_H_function₂ {n} {h₁ : Herbrand T} {h₂ h₃ : Herbrand (theory.sf_itr T n)} {f} :
  h₁ ⊳ᴴ[n] (function₂ _ f h₂ h₃) = function₂ _ f (h₁ ⊳ᴴ[n] h₂) (h₁ ⊳ᴴ[n] h₃) :=
by { induction h₁ using fopl.Herbrand.ind_on,
     induction h₂ using fopl.Herbrand.ind_on,
     induction h₃ using fopl.Herbrand.ind_on,
     rw ← vecterm_app_function₂_eq,
     simp[-vecterm_app_function₂_eq, subst_sf_H, Herbrand.of_eq_of], refl }

@[simp] lemma subst_sf_H_sentence (h : Herbrand T) {n} {t : term L} (a : t.arity = 0) :
  h ⊳ᴴ[n] ⟦t⟧ᴴ = ⟦t⟧ᴴ :=
by { induction h using fopl.Herbrand.ind_on, simp[subst_sf_H, Herbrand.of_eq_of, a] }

@[simp] lemma subst_sf_H_var0 (h : Herbrand T) :
  h ⊳ᴴ[0] ⟦#0⟧ᴴ = h :=
by { induction h using fopl.Herbrand.ind_on, simp[subst_sf_H, Herbrand.of_eq_of], refl }

end proper

end Herbrand

lemma empty_has_model : ∃ 𝔄 : model L, 𝔄 ⊧ₜₕ (∅ : theory L) :=
⟨𝔗[∅], λ p h, by { exfalso, refine set.not_mem_empty p h }⟩

theorem empty_consistent : theory.consistent (∅ : theory L) := @model_consistent L 𝔗[∅] ∅
(λ p h, by { exfalso, refine set.not_mem_empty p h })

theorem formula_equiv_equivalence : equivalence (formula.equiv T) :=
⟨λ _, by simp[formula.equiv], λ _ _, by simp[formula.equiv]; exact λ h₁ h₂, ⟨h₂, h₁⟩,
 λ _ _ _, by { simp[formula.equiv], intros h₁ h₂ h₃ h₄, refine ⟨h₁.imp_trans h₃, h₄.imp_trans h₂⟩ }⟩

def Lindenbaum : Type u :=
quotient (⟨formula.equiv T, formula_equiv_equivalence T⟩ : setoid (formula L))

def formula.quo (T : theory L) (p : formula L) : Lindenbaum T := quotient.mk' p

notation `⟦`p`⟧ᴸ.`T :max := formula.quo T p
notation `⟦`p`⟧ᴸ` :max := formula.quo _ p

namespace Lindenbaum
open provable Herbrand
variables {T}

@[elab_as_eliminator]
protected lemma ind_on {C : Lindenbaum T → Prop} (d : Lindenbaum T)
  (h : ∀ p : formula L, C ⟦p⟧ᴸ.T) : C d :=
quotient.induction_on' d h

@[elab_as_eliminator, reducible]
protected def lift_on {φ} (d : Lindenbaum T) (f : formula L → φ)
  (h : ∀ p q : formula L, T ⊢̇ p ↔̇ q → f p = f q) : φ :=
quotient.lift_on' d f h

@[simp]
protected lemma lift_on_eq {φ} (p : formula L) (f : formula L → φ)
  (h : ∀ p q, T ⊢̇ p ↔̇ q → f p = f q) : fopl.Lindenbaum.lift_on ⟦p⟧ᴸ.T f h = f p := rfl

@[elab_as_eliminator, reducible, simp]
protected def lift_on₂ {φ} (d₁ d₂ : Lindenbaum T) (f : formula L → formula L → φ)
  (h : ∀ p₁ p₂ q₁ q₂, T ⊢̇ p₁ ↔̇ q₁ → T ⊢̇ p₂ ↔̇ q₂ → f p₁ p₂ = f q₁ q₂) : φ :=
quotient.lift_on₂' d₁ d₂ f h

@[simp]
protected lemma lift_on₂_eq {φ} (p q : formula L) (f : formula L → formula L → φ)
  (h : ∀ p₁ p₂ q₁ q₂, T ⊢̇ p₁ ↔̇ q₁ → T ⊢̇ p₂ ↔̇ q₂ → f p₁ p₂ = f q₁ q₂) :
  fopl.Lindenbaum.lift_on₂ ⟦p⟧ᴸ.T ⟦q⟧ᴸ.T f h = f p q := rfl

protected lemma of_eq_of {p q : formula L} : ⟦p⟧ᴸ.T = ⟦q⟧ᴸ.T ↔ T ⊢̇ p ↔̇ q :=
by simp[formula.quo, formula.equiv, quotient.eq']

instance : has_le (Lindenbaum T) :=
⟨λ p₁ p₂, Lindenbaum.lift_on₂ p₁ p₂ (λ p₁ p₂, T ⊢̇ p₁ →̇ p₂) $
 λ p₁ p₂ q₁ q₂ hp hq, by { simp at*,
   exact ⟨λ h, (hp.2.imp_trans h).imp_trans hq.1, λ h, (hp.1.imp_trans h).imp_trans hq.2⟩ }⟩

instance : has_lt (Lindenbaum T) := ⟨λ l k, l ≤ k ∧ ¬k ≤ l⟩

def imply : Lindenbaum T → Lindenbaum T → Lindenbaum T :=
λ p₁ p₂, Lindenbaum.lift_on₂ p₁ p₂ (λ p₁ p₂, ⟦p₁ →̇ p₂⟧ᴸ.T) $
 λ p₁ p₂ q₁ q₂ hp hq, by { simp[Lindenbaum.of_eq_of] at*, split,
   { refine provable.deduction.mp (provable.deduction.mp _),
     have : T+{p₁ →̇ p₂}+{q₁} ⊢̇ p₁, from (show _ ⊢̇ q₁ →̇ p₁, by simp[hp]).MP (by simp),
     have : T+{p₁ →̇ p₂}+{q₁} ⊢̇ p₂, from (show _ ⊢̇ p₁ →̇ p₂, by simp).MP this,
     exact (show T+{p₁ →̇ p₂}+{q₁} ⊢̇ p₂ →̇ q₂, by simp[hq]).MP this },
   { refine provable.deduction.mp (provable.deduction.mp _),
     have : T+{q₁ →̇ q₂}+{p₁} ⊢̇ q₁, from (show _ ⊢̇ p₁ →̇ q₁, by simp[hp]).MP (by simp),
     have : T+{q₁ →̇ q₂}+{p₁} ⊢̇ q₂, from (show _ ⊢̇ q₁ →̇ q₂, by simp).MP this,
     exact (show _ ⊢̇ q₂ →̇ p₂, by simp[hq]).MP this  } }
infixr ` ⊑ `:60 := imply

instance : has_inf (Lindenbaum T) :=
⟨λ p₁ p₂, Lindenbaum.lift_on₂ p₁ p₂ (λ p₁ p₂, ⟦p₁ ⩑ p₂⟧ᴸ.T) $
 λ p₁ p₂ q₁ q₂ hp hq, by { simp[Lindenbaum.of_eq_of] at*, split,
   { apply provable.deduction.mp,
     have : T+{p₁ ⩑ p₂} ⊢̇ p₁ ⩑ p₂, from provable.add _ _, simp at *,
     refine ⟨(show T+{p₁ ⩑ p₂} ⊢̇ p₁ →̇ q₁, by simp[hp]).MP this.1,
       (show T+{p₁ ⩑ p₂} ⊢̇ p₂ →̇ q₂, by simp[hq]).MP this.2⟩ },
   { apply provable.deduction.mp,
     have : T+{q₁ ⩑ q₂} ⊢̇ q₁ ⩑ q₂, from provable.add _ _, simp at *,
     refine ⟨(show T+{q₁ ⩑ q₂} ⊢̇ q₁ →̇ p₁, by simp[hp]).MP this.1,
       (show T+{q₁ ⩑ q₂} ⊢̇ q₂ →̇ p₂, by simp[hq]).MP this.2⟩ } }⟩

instance : has_sup (Lindenbaum T) :=
⟨λ p₁ p₂, Lindenbaum.lift_on₂ p₁ p₂ (λ p₁ p₂, ⟦p₁ ⩒ p₂⟧ᴸ.T) $
 λ p₁ p₂ q₁ q₂ hp hq, by { simp[Lindenbaum.of_eq_of] at*, split,
   { refine (provable.deduction.mp ((provable.or_l _ _).MP (provable.deduction.mpr hp.1))).hyp_or
       (provable.deduction.mp ((provable.or_r _ _).MP (provable.deduction.mpr hq.1))) },
   { refine (provable.deduction.mp ((provable.or_l _ _).MP (provable.deduction.mpr hp.2))).hyp_or
       (provable.deduction.mp ((provable.or_r _ _).MP (provable.deduction.mpr hq.2))) }  }⟩

instance : has_compl (Lindenbaum T) :=
⟨λ p, Lindenbaum.lift_on p (λ p, ⟦¬̇p⟧ᴸ.T) $
 λ p₁ p₂ hyp, by { simp[provable.contrapose, Lindenbaum.of_eq_of] at*, refine ⟨hyp.2, hyp.1⟩ }⟩

instance : has_top (Lindenbaum T) := ⟨⟦⊤̇⟧ᴸ.T⟩

instance : has_bot (Lindenbaum T) := ⟨⟦⊥̇⟧ᴸ.T⟩

@[simp] def predicate : ∀ {n} (f : L.pr n), dvector (Herbrand T) n → Lindenbaum T
| 0     c _ := ⟦formula.const c⟧ᴸ.T
| (n+1) p v := fopl.Herbrand.lift_on_vec v (λ u : dvector (term L) (n+1), ⟦formula.app p (u.to_vecterm)⟧ᴸ.T)
  $ λ v₁ v₂ eqn, by { simp[Lindenbaum.of_eq_of] at*, refine ⟨provable.e5.MP eqn, provable.e5.MP (vecterm.equiv_symm _ eqn)⟩ }

def predicate₁ (T : theory L) (f : L.pr 1) (h : Herbrand T) : Lindenbaum T := predicate f (h :: dvector.nil)

def predicate₂ (T : theory L) (f : L.pr 2) (h₁ h₂ : Herbrand T) : Lindenbaum T := predicate f (h₁ :: h₂ :: dvector.nil)

def equal : Herbrand T → Herbrand T → Lindenbaum T :=
λ h₁ h₂, fopl.Herbrand.lift_on₂ h₁ h₂ (λ t₁ t₂, ⟦t₁ =̇ t₂⟧ᴸ.T) $
λ t₁ t₂ u₁ u₂ eqn₁ eqn₂, by { simp[Lindenbaum.of_eq_of], refine ⟨provable.deduction.mp _, provable.deduction.mp  _⟩,
  have lmm₁ : T+{t₁ =̇ t₂} ⊢̇ u₁ =̇ t₁, simp [provable.e2.MP eqn₁],
  have lmm₂ : T+{t₁ =̇ t₂} ⊢̇ t₁ =̇ t₂, simp,
  have lmm₃ : T+{t₁ =̇ t₂} ⊢̇ t₂ =̇ u₂, simp [eqn₂],
  refine (lmm₁.eq_trans lmm₂).eq_trans lmm₃,
  have lmm₁ : T+{u₁ =̇ u₂} ⊢̇ t₁ =̇ u₁, simp [eqn₁],
  have lmm₂ : T+{u₁ =̇ u₂} ⊢̇ u₁ =̇ u₂, simp,
  have lmm₃ : T+{u₁ =̇ u₂} ⊢̇ u₂ =̇ t₂, simp [provable.e2.MP eqn₂],
  refine (lmm₁.eq_trans lmm₂).eq_trans lmm₃ }
infix ` ∥ `:80 := equal

def Box : Lindenbaum T → Prop := λ p, Lindenbaum.lift_on p (λ p, T ⊢̇ p) $
λ p₁ p₂ hyp, by { simp at*, refine ⟨λ h, hyp.1.MP h, λ h, hyp.2.MP h⟩ }
prefix `□`:80 := Box

def refutable : Lindenbaum T → Prop := λ p, ¬□pᶜ
prefix `◇`:80 := refutable

lemma le_antisymm {l k : Lindenbaum T} : l ≤ k → k ≤ l → l = k :=
begin
  induction l using fopl.Lindenbaum.ind_on,
  induction k using fopl.Lindenbaum.ind_on,
  simp[has_le.le, Lindenbaum.of_eq_of], refine λ h₁ h₂, ⟨h₁, h₂⟩
end
lemma Box_iff {l : Lindenbaum T} : ⊤ ≤ l ↔ □l :=
by { induction l using fopl.Lindenbaum.ind_on, simp[has_top.top, Box, has_le.le] }

lemma imply_le {l k : Lindenbaum T} : l ⊑ k = ⊤ ↔ l ≤ k := by sorry

lemma provable_AX {p} (h : p ∈ T) : ⟦p⟧ᴸ.T = ⊤ :=
by simp[has_top.top, provable.AX h, Lindenbaum.of_eq_of]

lemma provable_K {l k : Lindenbaum T} : □(l ⊑ k) → □l → □k :=
begin
  induction l using fopl.Lindenbaum.ind_on,
  induction k using fopl.Lindenbaum.ind_on,
  simp[imply, Box], refine λ h₁ h₂, h₁.MP h₂
end

@[simp] lemma equal_refl {h : Herbrand T}  : h ∥ h = ⊤ :=
by induction h using fopl.Herbrand.ind_on; simp[equal, has_top.top, Lindenbaum.of_eq_of]

lemma equal_iff {h₁ h₂ : Herbrand T} {p : L.pr 1} : ⊤ ≤ h₁ ∥ h₂ ↔ h₁ = h₂ :=
by { simp[Box_iff], induction h₁ using fopl.Herbrand.ind_on, induction h₂ using fopl.Herbrand.ind_on,
      simp[Lindenbaum.of_eq_of, equal, has_le.le, imply, has_top.top, Box, predicate₁,
        (show ⟦h₁⟧ᴴ.T :: dvector.nil = ᵥ⟦h₁ :: dvector.nil⟧, by refl),
        (show ⟦h₂⟧ᴴ.T :: dvector.nil = ᵥ⟦h₂ :: dvector.nil⟧, by refl) ], exact iff.symm Herbrand.of_eq_of }

@[simp] lemma equal_subst_pr₁ {h₁ h₂ : Herbrand T} {p : L.pr 1} :
  h₁ ∥ h₂ ≤ predicate₁ _ p h₁ ⊑ predicate₁ _ p h₂ :=
by { induction h₁ using fopl.Herbrand.ind_on, induction h₂ using fopl.Herbrand.ind_on,
      simp[equal, has_le.le, imply, has_top.top, predicate₁,
        (show ⟦h₁⟧ᴴ.T :: dvector.nil = ᵥ⟦h₁ :: dvector.nil⟧, by refl),
        (show ⟦h₂⟧ᴴ.T :: dvector.nil = ᵥ⟦h₂ :: dvector.nil⟧, by refl) ],
        refine @provable.e5 _ T _ h₁ h₂ p }

@[simp] lemma equal_subst_fn₁ {h₁ h₂ : Herbrand T} {f : L.fn 1} : 
  h₁ ∥ h₂ ≤ function₁ _ f h₁ ∥ function₁ _ f h₂ :=
by { induction h₁ using fopl.Herbrand.ind_on, induction h₂ using fopl.Herbrand.ind_on,
      simp[equal, has_le.le, imply, has_top.top, Herbrand.function₁,
        (show ⟦h₁⟧ᴴ.T :: dvector.nil = ᵥ⟦h₁ :: dvector.nil⟧, by refl),
        (show ⟦h₂⟧ᴴ.T :: dvector.nil = ᵥ⟦h₂ :: dvector.nil⟧, by refl) ],
        refine @provable.e4 _ T _ h₁ h₂ f }

@[simp] lemma double_inv (l : Lindenbaum T) : lᶜᶜ = l :=
by induction l using fopl.Lindenbaum.ind_on; simp[Lindenbaum.of_eq_of, has_compl.compl]

lemma eq_symm (h₁ h₂ : Herbrand T) : h₁ ∥ h₂ = h₂ ∥ h₁ :=
by { induction h₁ using fopl.Herbrand.ind_on, induction h₂ using fopl.Herbrand.ind_on,
     simp[equal, Lindenbaum.of_eq_of] }

@[simp] lemma provable_one : □(⊤ : Lindenbaum T) :=
by simp[has_top.top, Box]

@[simp] lemma one_maximum (l : Lindenbaum T) : l ≤ ⊤ :=
by induction l using fopl.Lindenbaum.ind_on; simp[has_top.top, has_le.le]

@[simp] lemma zero_minimum (l : Lindenbaum T) : ⊥ ≤ l :=
by induction l using fopl.Lindenbaum.ind_on; simp[has_bot.bot, has_le.le]

lemma mul_le_l (l k : Lindenbaum T) : l ⊓ k ≤ l :=
by { induction l using fopl.Lindenbaum.ind_on, induction k using fopl.Lindenbaum.ind_on,
     simp[has_inf.inf, has_le.le], refine provable.deduction.mp _, have := provable.add T (l ⩑ k), simp* at * }

lemma mul_le_r (l k : Lindenbaum T) : l ⊓ k ≤ k :=
by { induction l using fopl.Lindenbaum.ind_on, induction k using fopl.Lindenbaum.ind_on,
     simp[has_inf.inf, has_le.le], refine provable.deduction.mp _, have := provable.add T (l ⩑ k), simp* at * }

lemma add_le_l (l k : Lindenbaum T) : l ≤ l ⊔ k :=
by { induction l using fopl.Lindenbaum.ind_on, induction k using fopl.Lindenbaum.ind_on,
     simp[has_sup.sup, has_le.le, provable.or_l] }

lemma add_le_r (l k : Lindenbaum T) : k ≤ l ⊔ k :=
by { induction l using fopl.Lindenbaum.ind_on, induction k using fopl.Lindenbaum.ind_on,
     simp[has_sup.sup, has_le.le, provable.or_r] }

private lemma le_trans {l m n : Lindenbaum T} : l ≤ m → m ≤ n → l ≤ n :=
by { induction l using fopl.Lindenbaum.ind_on,
     induction m using fopl.Lindenbaum.ind_on,
     induction n using fopl.Lindenbaum.ind_on, simp[has_le.le], refine provable.imp_trans }

private lemma sup_le {l m n : Lindenbaum T} : l ≤ n → m ≤ n → l ⊔ m ≤ n :=
by { induction l using fopl.Lindenbaum.ind_on,
     induction m using fopl.Lindenbaum.ind_on,
     induction n using fopl.Lindenbaum.ind_on, simp[has_le.le, has_sup.sup],
     intros h₁ h₂, exact provable.hyp_or h₁ h₂   }

private lemma le_inf {l m n : Lindenbaum T} : l ≤ m → l ≤ n → l ≤ m ⊓ n :=
by { induction l using fopl.Lindenbaum.ind_on,
     induction m using fopl.Lindenbaum.ind_on,
     induction n using fopl.Lindenbaum.ind_on,
     simp[has_le.le, has_inf.inf],
     refine λ h₁ h₂, provable.deduction.mp _, simp,
     refine ⟨provable.deduction.mpr h₁, provable.deduction.mpr h₂⟩  }

private lemma le_sup_inf {l m n : Lindenbaum T} : (l ⊔ m) ⊓ (l ⊔ n) ≤ l ⊔ m ⊓ n :=
by { induction l using fopl.Lindenbaum.ind_on,
     induction m using fopl.Lindenbaum.ind_on,
     induction n using fopl.Lindenbaum.ind_on,
     simp[has_sup.sup, has_inf.inf, has_le.le, provable.or_r, formula.or],
     refine provable.deduction.mp (provable.deduction.mp _),
     have lmm₁ : T+{(¬̇l →̇ m) ⩑ (¬̇l →̇ n)}+{¬̇l} ⊢̇ (¬̇l →̇ m) ⩑ (¬̇l →̇ n), simp[-provable.and],
     have lmm₂ : T+{(¬̇l →̇ m) ⩑ (¬̇l →̇ n)}+{¬̇l} ⊢̇ ¬̇l, simp,
     simp at lmm₁ ⊢, refine ⟨lmm₁.1.MP lmm₂, lmm₁.2.MP lmm₂⟩ }

private lemma sup_inf_sdiff (l m : Lindenbaum T) : l ⊓ m ⊔ l ⊓ mᶜ = l :=
by { induction l using fopl.Lindenbaum.ind_on, induction m using fopl.Lindenbaum.ind_on,
      simp[Lindenbaum.of_eq_of, has_le.le, has_sup.sup, has_inf.inf, has_compl.compl, has_top.top, formula.or],
      refine ⟨contrapose.mp (deduction.mp _), _⟩, simp,
      have : ∀ n, T+{¬̇l} ⊢̇ ¬̇(l ⩑ n),
      { refine λ n, deduction.mpr (contrapose.mpr (deduction.mp _)),
        have : T+{l ⩑ n} ⊢̇ l ⩑ n, simp[-provable.and], simp* at* },
      refine ⟨this _, this _⟩,
      refine deduction.mp (deduction.mp _), simp, refine neg_hyp (deduction.mp _),
      refine explosion (show T+{l}+{¬̇(l ⩑ m)}+{m} ⊢̇ l ⩑ m, by simp) (by simp) }

private lemma inf_inf_sdiff (l m : Lindenbaum T) : l ⊓ m ⊓ (l ⊓ mᶜ) = ⊥ :=
by { induction l using fopl.Lindenbaum.ind_on, induction m using fopl.Lindenbaum.ind_on,
     simp[Lindenbaum.of_eq_of, has_le.le, has_sup.sup, has_inf.inf, has_compl.compl, has_bot.bot, formula.or],
     refine deduction.mp (explosion (show T+{l ⩑ m ⩑ (l ⩑ ¬̇m)} ⊢̇ m, by simp[axiom_and]) (by simp[axiom_and])) }

private lemma inf_compl_le_bot (l : Lindenbaum T) : l ⊓ lᶜ ≤ ⊥ :=
by { induction l using fopl.Lindenbaum.ind_on, simp[has_le.le, has_inf.inf, has_compl.compl, has_bot.bot],
     have : T+{l ⩑ ¬̇l} ⊢̇ l ⩑ ¬̇l, simp[-provable.and], simp at this,
     refine provable.deduction.mp (provable.explosion this.1 this.2) }

private lemma top_le_sup_compl (l : Lindenbaum T) : ⊤ ≤ l ⊔ lᶜ :=
by induction l using fopl.Lindenbaum.ind_on; simp[has_le.le, has_sup.sup, has_compl.compl, has_top.top, formula.or]

instance : boolean_algebra (Lindenbaum T) :=
{ bot := ⊥,
  top := ⊤,
  le  := (≤),
  lt  := (<),
  sup := (⊔),
  inf := (⊓),
  compl := (λ l, lᶜ),
  sdiff := (λ l m, l ⊓ mᶜ),
  le_refl := λ l, by induction l using fopl.Lindenbaum.ind_on; simp[has_le.le],
  le_trans := λ _ _ _, le_trans,
  lt_iff_le_not_le := λ _ _, by simp[has_lt.lt],
  le_antisymm := λ l m, le_antisymm,
  bot_le := zero_minimum,
  le_sup_left := add_le_l,
  le_sup_right := add_le_r,
  sup_le := λ _ _ _, sup_le,
  inf_le_left := mul_le_l,
  inf_le_right := mul_le_r,
  le_inf := λ _ _ _, le_inf,
  le_sup_inf := λ _ _ _, le_sup_inf,
  sup_inf_sdiff := sup_inf_sdiff,
  inf_inf_sdiff := inf_inf_sdiff,
  le_top := one_maximum,
  inf_compl_le_bot := inf_compl_le_bot,
  top_le_sup_compl := top_le_sup_compl,
  sdiff_eq := λ _ _, rfl }

namespace proper
variables [proper 0 T]

def fal {n} : Lindenbaum (theory.sf_itr T (n+1)) → Lindenbaum (theory.sf_itr T n) :=
λ p, Lindenbaum.lift_on p (λ p, ⟦Ȧp⟧ᴸ.(theory.sf_itr T n)) $
λ p₁ p₂ hyp, by { simp[Lindenbaum.of_eq_of] at*, 
  refine ⟨provable.q2.MP (GE hyp.1), provable.q2.MP (GE hyp.2)⟩ }
prefix `∏`:90 := fal

def ex {n} : Lindenbaum (theory.sf_itr T (n+1)) → Lindenbaum (theory.sf_itr T n) :=
λ p, Lindenbaum.lift_on p (λ p, ⟦Ėp⟧ᴸ.(theory.sf_itr T n)) $
λ p₁ p₂ hyp, by { simp[formula.ex, provable.contrapose, Lindenbaum.of_eq_of] at*, 
  refine ⟨provable.q2.MP $ GE $ contrapose.mpr hyp.1, provable.q2.MP $ GE $ contrapose.mpr hyp.2⟩, }
prefix `∐`:90 := ex

@[simp] def subst_sf_L_aux (n) (t : term L) :
  Lindenbaum (theory.sf_itr T n) → Lindenbaum (theory.sf_itr T n) :=
λ p, Lindenbaum.lift_on p (λ p, ⟦p.rew ss[t // n]⟧ᴸ.(theory.sf_itr T n)) $
λ p₁ p₂ hyp, by { simp[Lindenbaum.of_eq_of, -provable.iff] at*,
  have := provable.ppc_prove_rew n hyp ss[t // 0],
  simp[rewriting_sf_itr_subst_sf,  -provable.iff] at this, exact this }

def subst_sf_L (n) : Herbrand T → Lindenbaum (theory.sf_itr T n) → Lindenbaum (theory.sf_itr T n) :=
λ t l, Herbrand.lift_on t (λ t, subst_sf_L_aux n t l) $
λ t₁ t₂ hyp, by { induction l using fopl.Lindenbaum.ind_on,
  simp[Lindenbaum.of_eq_of, -provable.iff] at*,
  refine equal_rew_iff _ (λ m, _),
  have C : m < n ∨ m = n ∨ n < m, from trichotomous m n,
  cases C,
  { simp[C] }, cases C; simp[C],
  { have := provable.sf_itr_sf_itr.mpr hyp, simp at this, refine this } }
notation h₁ ` ⊳[`:90 n `] `h₂ :90  := subst_sf_L n h₁ h₂

def sf {n} : Lindenbaum (theory.sf_itr T n) → Lindenbaum (theory.sf_itr T (n+1)) :=
λ p, Lindenbaum.lift_on p (λ p, ⟦p.sf⟧ᴸ.(theory.sf_itr T (n+1))) $
λ p₁ p₂ hyp, by { simp[contrapose, -provable.iff, Lindenbaum.of_eq_of] at*,
  exact sf_sf.mpr hyp }

lemma fal_le_subst_sf_L {n} (l : Lindenbaum (theory.sf_itr T (n+1))) (h) : ∏l ≤ h ⊳[n] l :=
begin
  induction l using fopl.Lindenbaum.ind_on, 
  induction h using fopl.Herbrand.ind_on, 
  simp[fal, has_le.le, subst_sf_L]
end

lemma subst_sf_L_le_ex (l : Lindenbaum T) (h) : h ⊳[0] l ≤ ∐l :=
begin
  induction l using fopl.Lindenbaum.ind_on, 
  induction h using fopl.Herbrand.ind_on, 
  simp[ex, has_le.le, subst_sf_L],
  apply contrapose.mp, simp[formula.ex],
  rw (show ¬̇(l.rew ss[h // 0]) = (¬̇l).rew ss[h // 0], by simp), 
  exact provable.q1
end

@[simp] lemma subst_sf_L_and (h : Herbrand T) (n) (l m : Lindenbaum T) :
  h ⊳[n] (l ⊓ m) = h ⊳[n] l ⊓ h ⊳[n] m :=
by { induction l using fopl.Lindenbaum.ind_on, induction m using fopl.Lindenbaum.ind_on, 
     induction h using fopl.Herbrand.ind_on,
     simp[has_inf.inf, has_le.le, subst_sf_L, Lindenbaum.of_eq_of] }

@[simp] lemma subst_sf_L_or (h : Herbrand T) (n) (l m : Lindenbaum T) :
  h ⊳[n] (l ⊔ m) = h ⊳[n] l ⊔ h ⊳[n] m :=
by { induction l using fopl.Lindenbaum.ind_on, induction m using fopl.Lindenbaum.ind_on, 
     induction h using fopl.Herbrand.ind_on,
     simp[has_sup.sup, has_le.le, subst_sf_L, Lindenbaum.of_eq_of] }

@[simp] lemma subst_sf_L_neg (h : Herbrand T) (n) (l : Lindenbaum T) :
  h ⊳[n] lᶜ = (h ⊳[n] l)ᶜ :=
by { induction l using fopl.Lindenbaum.ind_on,
     induction h using fopl.Herbrand.ind_on,
     simp[has_compl.compl, has_le.le, subst_sf_L, Lindenbaum.of_eq_of] }

@[simp] lemma subst_sf_L_equal (h₁ : Herbrand T) (n) (h₂ h₃ : Herbrand T) :
  h₁ ⊳[n] (h₂ ∥ h₃) = (h₁ ⊳ᴴ[n] h₂) ∥ (h₁ ⊳ᴴ[n] h₃) :=
by { induction h₁ using fopl.Herbrand.ind_on, induction h₂ using fopl.Herbrand.ind_on,
     induction h₃ using fopl.Herbrand.ind_on,
     simp[equal, subst_sf_L, Herbrand.closed.subst_sf_H, Herbrand.closed.subst_sf_H_aux,
       Lindenbaum.of_eq_of] }

@[simp] lemma subst_sf_L_fal (h : Herbrand T) (n) (l : Lindenbaum T) :
  h ⊳[n] ∏l = ∏(h ⊳[n+1] l) :=
by { induction l using fopl.Lindenbaum.ind_on,
     induction h using fopl.Herbrand.ind_on,
     simp[fal, has_le.le, subst_sf_L, Lindenbaum.of_eq_of, subst_sf] }

@[simp] lemma subst_sf_L_ex (h : Herbrand T) (n) (l : Lindenbaum T) :
  h ⊳[n] ∐l = ∐(h ⊳[n+1] l) :=
by { induction l using fopl.Lindenbaum.ind_on,
     induction h using fopl.Herbrand.ind_on,
     simp[ex, has_le.le, subst_sf_L, Lindenbaum.of_eq_of, subst_sf] }

lemma subst_sf_L_sentence (h : Herbrand T) (n) {p : formula L} (a : sentence p) :
  h ⊳[n] ⟦p⟧ᴸ = ⟦p⟧ᴸ :=
by { induction h using fopl.Herbrand.ind_on, simp[subst_sf_L, Lindenbaum.of_eq_of, a] }

lemma provable_GE {l : Lindenbaum T} : ⊤ ≤ l → ⊤ ≤ ∏l :=
by { simp[Box_iff], induction l using fopl.Lindenbaum.ind_on, simp[fal, Box], exact provable.GE_cl }

lemma prenex_ex_quantifir_neg  (l : Lindenbaum T) : (∐l)ᶜ = ∏lᶜ :=
by induction l using fopl.Lindenbaum.ind_on;
   simp[has_compl.compl, ex, fal, Lindenbaum.of_eq_of, formula.ex]

lemma prenex_fal_quantifir_neg  {l : Lindenbaum T} : (∏l)ᶜ = ∐lᶜ :=
by { have := prenex_ex_quantifir_neg lᶜ, simp at this, simp[←this] }

@[simp] theorem provable_fal_eq {p} : (⟦Ȧp⟧ᴸ : Lindenbaum T) = ∏⟦p⟧ᴸ := rfl
@[simp] theorem provable_ex_eq {p} : (⟦Ėp⟧ᴸ : Lindenbaum T) = ∐⟦p⟧ᴸ := rfl
lemma prenex_fal_quantifir_imp1  {l : Lindenbaum T} {k : Lindenbaum T} : ∏l ⊑ k = ∐(l ⊑ sf k) := by sorry

end closed

theorem provable_top_iff {p} : T ⊢̇ p ↔ ⟦p⟧ᴸ.T = ⊤ := by simp[has_top.top, Lindenbaum.of_eq_of]

protected theorem provable_iff {p q} : T ⊢̇ p ↔̇ q ↔ ⟦p⟧ᴸ.T = ⟦q⟧ᴸ := by simp[Lindenbaum.of_eq_of]

theorem provable_imp_iff {p q} : T ⊢̇ p →̇ q ↔ ⟦p⟧ᴸ.T ≤ ⟦q⟧ᴸ := by simp[has_le.le]

@[simp] lemma provable_top_eq : (⟦⊤̇⟧ᴸ : Lindenbaum T) = ⊤ := rfl
@[simp] lemma provable_bot_eq : (⟦⊥̇⟧ᴸ : Lindenbaum T) = ⊥ := rfl
@[simp] theorem provable_and_eq {p q} : (⟦p ⩑ q⟧ᴸ : Lindenbaum T) = ⟦p⟧ᴸ ⊓ ⟦q⟧ᴸ := rfl
@[simp] theorem provable_or_eq {p q} : (⟦p ⩒ q⟧ᴸ : Lindenbaum T) = ⟦p⟧ᴸ ⊔ ⟦q⟧ᴸ := rfl
@[simp] theorem provable_neg_eq {p} : (⟦¬̇p⟧ᴸ : Lindenbaum T) = ⟦p⟧ᴸᶜ := rfl
@[simp] theorem imp_eq {p q} : (⟦p →̇ q⟧ᴸ : Lindenbaum T) = ⟦p⟧ᴸᶜ ⊔ ⟦q⟧ᴸ := by {
  have : (⟦p →̇ q⟧ᴸ : Lindenbaum T) = ⟦¬̇p ⩒ q⟧ᴸ, 
  { simp[Lindenbaum.of_eq_of, -provable_or_eq, formula.or], refine ⟨deduction.mp (by simp), deduction.mp _⟩,
    have : T+{¬̇¬̇p →̇ q} ⊢̇ ¬̇¬̇p →̇ q, simp[-dn1_iff], simp* at* },
  simp[this] }

@[simp] lemma provable_equal_eq {t₁ t₂} : (⟦t₁ =̇ t₂⟧ᴸ : Lindenbaum T) = ⟦t₁⟧ᴴ ∥ ⟦t₂⟧ᴴ := rfl
@[simp] theorem provable_predicate₁_iff {p : L.pr 1} {t} : (⟦formula.app p t⟧ᴸ : Lindenbaum T) = predicate₁ T p ⟦t⟧ᴴ := rfl 
@[simp] theorem provable_predicate₂_iff {p : L.pr 2} {t₁ t₂} :
  (⟦formula.app p (vecterm.cons t₁ t₂)⟧ᴸ : Lindenbaum T) = predicate₂ T p ⟦t₁⟧ᴴ ⟦t₂⟧ᴴ := rfl 

lemma to_Herbrand {h₁ h₂ : Herbrand T} : h₁ ∥ h₂ = ⊤ ↔ h₁ = h₂ :=
by { induction h₁ using fopl.Herbrand.ind_on, induction h₂ using fopl.Herbrand.ind_on,
     simp only [equal, Herbrand.of_eq_of, has_top.top],
     simp[-provable_equal_eq, -provable_top_eq, Lindenbaum.of_eq_of] }

theorem provable_neg_iff {p} : T ⊢̇ ¬̇p ↔ (⟦p⟧ᴸ : Lindenbaum T) = ⊥ :=
by simp[provable_top_iff]

end Lindenbaum

end fopl