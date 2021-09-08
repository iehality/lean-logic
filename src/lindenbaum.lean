import deduction semantics

universes u t

namespace fopl
variables {L : language.{u}} (T : theory L) (i : ℕ)

notation t` ≃[`T :80`] `u:60 := term.equiv T _ t u

theorem term_equiv_equivalence (T : theory L) : equivalence (λ t₁ t₂, T ⊢ t₁ =̇ t₂) :=
⟨λ _, by simp, λ _ _ , provable.eq_symm, λ _ _ _, provable.eq_trans⟩

@[reducible, simp, instance]
def herbrand (n : ℕ) : setoid (term L) := ⟨λ t₁ t₂, T^n ⊢ t₁ =̇ t₂, term_equiv_equivalence (T^n)⟩

def Herbrand (n : ℕ) : Type u := quotient (herbrand T n)

def term.quo (T : theory L) (n : ℕ) (t : term L) : Herbrand T n := quotient.mk' t

notation `⟦`t`⟧ᴴ` :max := term.quo _ _ t

local infix ` ≋ `:80 := (@setoid.vec_r _ (herbrand T _) _)

instance (T : theory L) (n) : inhabited (Herbrand T n) := ⟨⟦#0⟧ᴴ⟩


namespace Herbrand
variables {T} {i}

@[elab_as_eliminator]
protected lemma ind_on {C : Herbrand T i → Prop} (d : Herbrand T i)
  (h : ∀ t : term L, C ⟦t⟧ᴴ) : C d :=
quotient.induction_on' d h

@[elab_as_eliminator, reducible]
protected def lift_on {φ} (d : Herbrand T i) (f : term L → φ)
  (h : ∀ t u : term L, T^i ⊢ t =̇ u → f t = f u) : φ :=
quotient.lift_on' d f h

@[simp]
protected lemma lift_on_eq {φ} (t : term L) (f : term L → φ)
  (h : ∀ t u, T^i ⊢ t =̇ u → f t = f u) : fopl.Herbrand.lift_on (⟦t⟧ᴴ : Herbrand T i) f h = f t := rfl

@[elab_as_eliminator, reducible, simp]
protected def lift_on₂ {φ} (d₁ d₂ : Herbrand T i) (f : term L → term L → φ)
  (h : ∀ t₁ t₂ u₁ u₂, (T^i ⊢ t₁ =̇ u₁) → (T^i ⊢ t₂ =̇ u₂) → f t₁ t₂ = f u₁ u₂) : φ :=
quotient.lift_on₂' d₁ d₂ f h

@[simp]
protected lemma lift_on₂_eq {φ} (t u : term L) (f : term L → term L → φ)
  (h : ∀ t₁ t₂ u₁ u₂, (T^i ⊢ t₁ =̇ u₁) → (T^i ⊢ t₂ =̇ u₂) → f t₁ t₂ = f u₁ u₂) :
  fopl.Herbrand.lift_on₂ ⟦t⟧ᴴ ⟦u⟧ᴴ f h = f t u := rfl

protected def lift_on_finitary {φ} {n : ℕ} (v : finitary (Herbrand T i) n) (f : finitary (term L) n → φ)
  (h : ∀ v₁ v₂ : finitary (term L) n, (∀ n, T^i ⊢ (v₁ n) =̇ (v₂ n)) → f v₁ = f v₂) : φ :=
quotient.lift_on_finitary v f h 

@[simp]
protected lemma lift_on_finitary_eq {φ} {n} (v : finitary (term L) n) (f : finitary (term L) n → φ)
  (h : ∀ v₁ v₂ : finitary (term L) n, (∀ n, T^i ⊢ (v₁ n) =̇ (v₂ n)) → f v₁ = f v₂) :
  fopl.Herbrand.lift_on_finitary (λ x, (⟦v x⟧ᴴ : Herbrand T i)) f h = f v :=
quotient.lift_on_finitary_eq v f h

lemma of_eq_of {t u : term L} : (⟦t⟧ᴴ : Herbrand T i) = ⟦u⟧ᴴ ↔ (T^i ⊢ t =̇ u) :=
by simp[term.quo, term.equiv, quotient.eq']

def symbol.fn {n} (f : L.fn n) : finitary (Herbrand T i) n → Herbrand T i :=
λ v, fopl.Herbrand.lift_on_finitary v (λ u : finitary (term L) n, ⟦term.app f u⟧ᴴ) 
  $ λ v₁ v₂ eqs, by { simp[of_eq_of] at*, refine (provable.e4' f v₁ v₂).MP (provable.conjunction' eqs) }

def function₀ (T : theory L) (i) (c : L.fn 0) : Herbrand T i := symbol.fn c finitary.nil
notation `c⟪` s `⟫⁰` := function₀ _ _ s

def function₁ (f : L.fn 1) (h : Herbrand T i) : Herbrand T i := symbol.fn f fin[h]

def function₂ (f : L.fn 2) (h₁ h₂ : Herbrand T i) : Herbrand T i := symbol.fn f fin[h₁, h₂]
notation h₁ ` f⟪` s `⟫² ` h₂ :80 := function₂ s h₁ h₂

def symbol.pr {n} (p : L.pr n) : finitary (Herbrand T i) n → Prop :=
λ v, fopl.Herbrand.lift_on_finitary v (λ u : finitary (term L) n, T^i ⊢ formula.app p u) 
  $ λ v₁ v₂ eqs, by { simp[of_eq_of] at*, have := ((provable.e5' p v₁ v₂).MP (provable.conjunction' eqs)).MP, 
  refine ⟨((provable.e5' p v₁ v₂).MP (provable.conjunction' eqs)).MP,
  ((provable.e5' p v₂ v₁).MP (provable.conjunction' (λ i, provable.eq_symm (eqs _)))).MP⟩ }

def model (T : theory L) : model L := ⟨Herbrand T 0, ⟦#0⟧ᴴ, @symbol.fn _ T 0, @symbol.pr _ T 0⟩
notation `𝔗[`T`]` := model T

protected theorem provable_iff {t₁ t₂} : T^i ⊢ t₁ =̇ t₂ ↔ (⟦t₁⟧ᴴ : Herbrand T i) = ⟦t₂⟧ᴴ := by simp[of_eq_of]
protected theorem provable_iff0 {t₁ t₂} : T ⊢ t₁ =̇ t₂ ↔ (⟦t₁⟧ᴴ : Herbrand T 0) = ⟦t₂⟧ᴴ := by simp[of_eq_of]

@[simp] theorem const_function₀_eq {c : L.fn 0} : ⟦term.app c finitary.nil⟧ᴴ = function₀ T i c := rfl

@[simp] theorem term_app_function₁_eq {f : L.fn 1} {t : term L} :
  ⟦term.app f fin[t]⟧ᴴ = function₁ f (⟦t⟧ᴴ : Herbrand T i) := rfl

@[simp] theorem term_app_function₂_eq {f : L.fn 2} {t₁ t₂} :
  ⟦term.app f fin[t₁, t₂]⟧ᴴ = function₂ f (⟦t₁⟧ᴴ : Herbrand T i) ⟦t₂⟧ᴴ := rfl

def pow : Herbrand T i → Herbrand T (i+1) :=
λ h, Herbrand.lift_on h (λ u, ⟦u^1⟧ᴴ : term L → Herbrand T (i+1)) $
λ t₁ t₂ hyp, by { simp[Herbrand.of_eq_of, -provable.iff, ←theory.pow_add] at*,
  rw [show (t₁^1) =̇ (t₂^1) = (t₁ =̇ t₂)^1, by simp, provable.sf_itr_sf_itr], exact hyp }

@[simp] def sf_simp (t : term L) (j : ℕ) : (⟦t⟧ᴴ : Herbrand T i).pow = ⟦t^1⟧ᴴ := rfl

def var (n : ℕ) : Herbrand T i := ⟦#n⟧ᴴ
prefix `♯`:max := var

@[simp] lemma var_pow (n : ℕ) : (♯n : Herbrand T i).pow= ♯(n + 1) := rfl

namespace proper

@[simp] def subst_sf_H_aux [proper : proper 0 T] (t : term L) :
  Herbrand T (i + 1) → Herbrand T i :=
λ h, Herbrand.lift_on h (λ u, ⟦u.rew ι[i ⇝ t]⟧ᴴ : term L → Herbrand T i) $
λ t₁ t₂ hyp, by { simp[Herbrand.of_eq_of, -provable.iff] at*,
    exact provable.pow_subst' i hyp t }

variables [proper 0 T]

def subst_sf_H : Herbrand T i → Herbrand T (i+1) → Herbrand T i :=
λ t h, Herbrand.lift_on t (λ t, subst_sf_H_aux t h : term L → Herbrand T i) $
λ t₁ t₂ hyp, by { induction h using fopl.Herbrand.ind_on,
  simp[Herbrand.of_eq_of, -provable.iff] at*, 
  refine provable.equal_rew_equal (ι[i ⇝ t₁]) (ι[i ⇝ t₂]) (λ m, _) h,
  have C : m < i ∨ m = i ∨ i < m, from trichotomous m i,
  cases C,
  { simp[C] }, cases C; simp[C], exact hyp }

infix ` ⊳ᴴ ` :90  := subst_sf_H

@[simp] lemma subst_sf_H_function₁ {h₁ : Herbrand T i} {h₂ : Herbrand T (i+1)} {f} :
  h₁ ⊳ᴴ (function₁ f h₂) = function₁ f (h₁ ⊳ᴴ h₂) :=
by { induction h₁ using fopl.Herbrand.ind_on, induction h₂ using fopl.Herbrand.ind_on,
     show ⟦h₁⟧ᴴ ⊳ᴴ function₁ f (⟦h₂⟧ᴴ : Herbrand T (i + 1)) = function₁ f (⟦h₁⟧ᴴ ⊳ᴴ ⟦h₂⟧ᴴ),
     rw ← term_app_function₁_eq,
     simp[-term_app_function₁_eq, subst_sf_H, Herbrand.of_eq_of], refl }

@[simp] lemma subst_sf_H_function₂
  {h₁ : Herbrand T i} {h₂ h₃ : Herbrand T (i+1)} {f} :
  h₁ ⊳ᴴ (function₂ f h₂ h₃) = function₂ f (h₁ ⊳ᴴ h₂) (h₁ ⊳ᴴ h₃) :=
by { induction h₁ using fopl.Herbrand.ind_on,
     induction h₂ using fopl.Herbrand.ind_on,
     induction h₃ using fopl.Herbrand.ind_on,
     rw ← term_app_function₂_eq, 
     simp[-term_app_function₂_eq, subst_sf_H, Herbrand.of_eq_of],
     have : (λ (x : fin 2), (fin[h₂, h₃] x).rew ι[i ⇝ h₁]) = fin[h₂.rew ι[i ⇝ h₁], h₃.rew ι[i ⇝ h₁]],
     { funext x, rcases x with ⟨x, x_p⟩, simp[finitary.cons],
       cases x, { simp }, cases x, { simp }, exfalso, simp[←nat.add_one, add_assoc] at*, exact x_p },
     simp[this] }

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

theorem formula_equiv_equivalence : equivalence (formula.equiv T) :=
⟨λ _, by simp[formula.equiv], λ _ _, by simp[formula.equiv]; exact λ h₁ h₂, ⟨h₂, h₁⟩,
 λ _ _ _, by { simp[formula.equiv], intros h₁ h₂ h₃ h₄, refine ⟨h₁.imp_trans h₃, h₄.imp_trans h₂⟩ }⟩

def Lindenbaum : Type u :=
quotient (⟨formula.equiv (T^i), formula_equiv_equivalence (T^i)⟩ : setoid (formula L))

def formula.quo (T : theory L) (i) (p : formula L) : Lindenbaum T i := quotient.mk' p

notation `⟦`p`⟧ᴸ` :max := formula.quo _ _ p

namespace Lindenbaum
open provable Herbrand
variables {T} {i}

@[elab_as_eliminator]
protected lemma ind_on {C : Lindenbaum T i → Prop} (d : Lindenbaum T i)
  (h : ∀ p : formula L, C ⟦p⟧ᴸ) : C d :=
quotient.induction_on' d h

@[elab_as_eliminator, reducible]
protected def lift_on {φ} (d : Lindenbaum T i) (f : formula L → φ)
  (h : ∀ p q : formula L, T^i ⊢ p ↔̇ q → f p = f q) : φ :=
quotient.lift_on' d f h

@[simp]
protected lemma lift_on_eq {φ} (p : formula L) (f : formula L → φ)
  (h : ∀ p q, T^i ⊢ p ↔̇ q → f p = f q) : fopl.Lindenbaum.lift_on ⟦p⟧ᴸ f h = f p := rfl

@[elab_as_eliminator, reducible]
protected def lift_on₂ {φ} (d₁ d₂ : Lindenbaum T i) (f : formula L → formula L → φ)
  (h : ∀ p₁ p₂ q₁ q₂, T^i ⊢ p₁ ↔̇ q₁ → T^i ⊢ p₂ ↔̇ q₂ → f p₁ p₂ = f q₁ q₂) : φ :=
quotient.lift_on₂' d₁ d₂ f h

@[simp]
protected lemma lift_on₂_eq {φ} (p q : formula L) (f : formula L → formula L → φ)
  (h : ∀ p₁ p₂ q₁ q₂, T^i ⊢ p₁ ↔̇ q₁ → T^i ⊢ p₂ ↔̇ q₂ → f p₁ p₂ = f q₁ q₂) :
  fopl.Lindenbaum.lift_on₂ ⟦p⟧ᴸ ⟦q⟧ᴸ f h = f p q := rfl

protected lemma of_eq_of {p q : formula L} : (⟦p⟧ᴸ : Lindenbaum T i) = ⟦q⟧ᴸ ↔ T^i ⊢ p ↔̇ q :=
by simp[formula.quo, formula.equiv, quotient.eq']

instance : has_le (Lindenbaum T i) :=
⟨λ p₁ p₂, Lindenbaum.lift_on₂ p₁ p₂ (λ p₁ p₂, T^i ⊢ p₁ →̇ p₂) $
 λ p₁ p₂ q₁ q₂ hp hq, by { simp at*,
   exact ⟨λ h, (hp.2.imp_trans h).imp_trans hq.1, λ h, (hp.1.imp_trans h).imp_trans hq.2⟩ }⟩

instance : has_lt (Lindenbaum T i) := ⟨λ l k, l ≤ k ∧ ¬k ≤ l⟩

def imply : Lindenbaum T i → Lindenbaum T i → Lindenbaum T i :=
λ p₁ p₂, Lindenbaum.lift_on₂ p₁ p₂ (λ p₁ p₂, (⟦p₁ →̇ p₂⟧ᴸ : Lindenbaum T i)) $
 λ p₁ p₂ q₁ q₂ hp hq, by { simp[Lindenbaum.of_eq_of] at*, split,
   { refine provable.deduction.mp (provable.deduction.mp _),
     have : (T^i)+{p₁ →̇ p₂}+{q₁} ⊢ p₁, from (show _ ⊢ q₁ →̇ p₁, by simp[hp]).MP (by simp),
     have : (T^i)+{p₁ →̇ p₂}+{q₁} ⊢ p₂, from (show _ ⊢ p₁ →̇ p₂, by simp).MP this,
     exact (show (T^i)+{p₁ →̇ p₂}+{q₁} ⊢ p₂ →̇ q₂, by simp[hq]).MP this },
   { refine provable.deduction.mp (provable.deduction.mp _),
     have : (T^i)+{q₁ →̇ q₂}+{p₁} ⊢ q₁, from (show _ ⊢ p₁ →̇ q₁, by simp[hp]).MP (by simp),
     have : (T^i)+{q₁ →̇ q₂}+{p₁} ⊢ q₂, from (show _ ⊢ q₁ →̇ q₂, by simp).MP this,
     exact (show _ ⊢ q₂ →̇ p₂, by simp[hq]).MP this } }
infixr ` ⊑ `:60 := imply

instance : has_inf (Lindenbaum T i) :=
⟨λ p₁ p₂, Lindenbaum.lift_on₂ p₁ p₂ (λ p₁ p₂, ⟦p₁ ⩑ p₂⟧ᴸ) $
 λ p₁ p₂ q₁ q₂ hp hq, by { simp[Lindenbaum.of_eq_of] at*, split,
   { apply provable.deduction.mp,
     have : (T^i)+{p₁ ⩑ p₂} ⊢ p₁ ⩑ p₂, from provable.add _ _, simp at *,
     refine ⟨(show (T^i)+{p₁ ⩑ p₂} ⊢ p₁ →̇ q₁, by simp[hp]).MP this.1,
       (show (T^i)+{p₁ ⩑ p₂} ⊢ p₂ →̇ q₂, by simp[hq]).MP this.2⟩ },
   { apply provable.deduction.mp,
     have : (T^i)+{q₁ ⩑ q₂} ⊢ q₁ ⩑ q₂, from provable.add _ _, simp at *,
     refine ⟨(show (T^i)+{q₁ ⩑ q₂} ⊢ q₁ →̇ p₁, by simp[hp]).MP this.1,
       (show (T^i)+{q₁ ⩑ q₂} ⊢ q₂ →̇ p₂, by simp[hq]).MP this.2⟩ } }⟩

instance : has_sup (Lindenbaum T i) :=
⟨λ p₁ p₂, Lindenbaum.lift_on₂ p₁ p₂ (λ p₁ p₂, ⟦p₁ ⩒ p₂⟧ᴸ) $
 λ p₁ p₂ q₁ q₂ hp hq, by { simp[Lindenbaum.of_eq_of] at*, split,
   { refine (provable.deduction.mp ((provable.or_l _ _).MP (provable.deduction.mpr hp.1))).hyp_or
       (provable.deduction.mp ((provable.or_r _ _).MP (provable.deduction.mpr hq.1))) },
   { refine (provable.deduction.mp ((provable.or_l _ _).MP (provable.deduction.mpr hp.2))).hyp_or
       (provable.deduction.mp ((provable.or_r _ _).MP (provable.deduction.mpr hq.2))) }  }⟩

instance : has_compl (Lindenbaum T i) :=
⟨λ p, Lindenbaum.lift_on p (λ p, ⟦¬̇p⟧ᴸ) $
 λ p₁ p₂ hyp, by { simp[provable.contrapose, Lindenbaum.of_eq_of] at*, refine ⟨hyp.2, hyp.1⟩ }⟩

instance : has_top (Lindenbaum T i) := ⟨⟦⊤̇⟧ᴸ⟩

instance : has_bot (Lindenbaum T i) := ⟨⟦⊥̇⟧ᴸ⟩

@[simp] def predicate {n} (p : L.pr n) : finitary (Herbrand T i) n → Lindenbaum T i :=
λ v, fopl.Herbrand.lift_on_finitary v (λ u : finitary (term L) n, ⟦formula.app p u⟧ᴸ) 
  $ λ v₁ v₂ eqs, by { simp[fopl.Lindenbaum.of_eq_of] at*,
    refine ⟨(provable.e5' p v₁ v₂).MP (provable.conjunction' eqs),
    (provable.e5' p v₂ v₁).MP (provable.conjunction' (λ x, provable.eq_symm (eqs x)))⟩ }

def function₀ (T : theory L) (i) (c : L.fn 0) : Herbrand T i := symbol.fn c finitary.nil
notation `c⟪` s `⟫⁰` := function₀ _ _ s

def predicate₁ (f : L.pr 1) (h : Herbrand T i) : Lindenbaum T i :=
predicate f fin[h]

def predicate₂ (f : L.pr 2) (h₁ h₂ : Herbrand T i) : Lindenbaum T i :=
predicate f fin[h₁, h₂]

def equal : Herbrand T i → Herbrand T i → Lindenbaum T i :=
λ h₁ h₂, fopl.Herbrand.lift_on₂ h₁ h₂ (λ t₁ t₂, (⟦t₁ =̇ t₂⟧ᴸ : Lindenbaum T i)) $
λ t₁ t₂ u₁ u₂ eqn₁ eqn₂, by {
  simp[Lindenbaum.of_eq_of], refine ⟨provable.deduction.mp _, provable.deduction.mp  _⟩,
  have lmm₁ : (T^i)+{t₁ =̇ t₂} ⊢ u₁ =̇ t₁, simp [provable.eq_symm eqn₁],
  have lmm₂ : (T^i)+{t₁ =̇ t₂} ⊢ t₁ =̇ t₂, simp,
  have lmm₃ : (T^i)+{t₁ =̇ t₂} ⊢ t₂ =̇ u₂, simp [eqn₂],
  refine (lmm₁.eq_trans lmm₂).eq_trans lmm₃,
  have lmm₁ : (T^i)+{u₁ =̇ u₂} ⊢ t₁ =̇ u₁, simp [eqn₁],
  have lmm₂ : (T^i)+{u₁ =̇ u₂} ⊢ u₁ =̇ u₂, simp,
  have lmm₃ : (T^i)+{u₁ =̇ u₂} ⊢ u₂ =̇ t₂, simp [provable.eq_symm eqn₂],
  refine (lmm₁.eq_trans lmm₂).eq_trans lmm₃ }
infix ` ∥ `:60 := equal

def Box : Lindenbaum T i → Prop := λ p, Lindenbaum.lift_on p (λ p, T^i ⊢ p) $
λ p₁ p₂ hyp, by { simp at*, refine ⟨λ h, hyp.1.MP h, λ h, hyp.2.MP h⟩ }
prefix `□`:80 := Box

def refutable : Lindenbaum T i → Prop := λ p, ¬□pᶜ
prefix `◇`:80 := refutable

lemma le_antisymm {l k : Lindenbaum T i} : l ≤ k → k ≤ l → l = k :=
begin
  induction l using fopl.Lindenbaum.ind_on,
  induction k using fopl.Lindenbaum.ind_on,
  simp[has_le.le, Lindenbaum.of_eq_of], refine λ h₁ h₂, ⟨h₁, h₂⟩
end
lemma Box_iff {l : Lindenbaum T i} : ⊤ ≤ l ↔ □l :=
by { induction l using fopl.Lindenbaum.ind_on, simp[has_top.top, Box, has_le.le] }

lemma imply_le {l k : Lindenbaum T i} : l ⊑ k = ⊤ ↔ l ≤ k := by sorry

lemma provable_AX {p} (h : p ∈ T) : (⟦p^i⟧ᴸ : Lindenbaum T i) = ⊤ :=
by { simp[has_top.top, provable.AX h, Lindenbaum.of_eq_of],
     simp[provable.sf_itr_sf_itr], exact provable.AX h }

lemma provable_K {l k : Lindenbaum T i} : □(l ⊑ k) → □l → □k :=
begin
  induction l using fopl.Lindenbaum.ind_on,
  induction k using fopl.Lindenbaum.ind_on,
  simp[imply, Box], refine λ h₁ h₂, h₁.MP h₂
end

@[simp] lemma equal_refl {h : Herbrand T i}  : h ∥ h = ⊤ :=
by induction h using fopl.Herbrand.ind_on; simp[equal, has_top.top, Lindenbaum.of_eq_of]

lemma equal_iff {h₁ h₂ : Herbrand T i} {p : L.pr 1} : h₁ ∥ h₂ = ⊤ ↔ h₁ = h₂ :=
by { induction h₁ using fopl.Herbrand.ind_on, induction h₂ using fopl.Herbrand.ind_on,
     simp[Lindenbaum.of_eq_of, equal, has_le.le, imply, has_top.top, Box, predicate₁ ],
     exact iff.symm Herbrand.of_eq_of }

@[simp] lemma equal_subst_pr₁ {h₁ h₂ : Herbrand T i} {p : L.pr 1} :
  (h₁ ∥ h₂) ⊓ predicate₁ p h₁ ≤ predicate₁ p h₂ :=
by { induction h₁ using fopl.Herbrand.ind_on, induction h₂ using fopl.Herbrand.ind_on,
      simp[has_inf.inf, equal, has_le.le, imply, has_top.top, predicate₁],
        have := @provable.e5' _ T _ p fin[h₁] fin[h₂], simp at this, sorry }

@[simp] lemma double_inv (l : Lindenbaum T i) : lᶜᶜ = l :=
by induction l using fopl.Lindenbaum.ind_on; simp[Lindenbaum.of_eq_of, has_compl.compl]

lemma eq_symm (h₁ h₂ : Herbrand T i) : h₁ ∥ h₂ = h₂ ∥ h₁ :=
by { induction h₁ using fopl.Herbrand.ind_on, induction h₂ using fopl.Herbrand.ind_on,
     simp[equal, Lindenbaum.of_eq_of],
     have := ((@provable.e2 _ (T^i)).fal_subst h₂).fal_subst h₁, simp at*,
     have := ((@provable.e2 _ (T^i)).fal_subst h₁).fal_subst h₂, simp at*, simp* at* }

@[simp] lemma provable_one : □(⊤ : Lindenbaum T i) :=
by simp[has_top.top, Box]

@[simp] lemma one_maximum (l : Lindenbaum T i) : l ≤ ⊤ :=
by induction l using fopl.Lindenbaum.ind_on; simp[has_top.top, has_le.le]

@[simp] lemma zero_minimum (l : Lindenbaum T i) : ⊥ ≤ l :=
by induction l using fopl.Lindenbaum.ind_on; simp[has_bot.bot, has_le.le]

lemma mul_le_l (l k : Lindenbaum T i) : l ⊓ k ≤ l :=
by { induction l using fopl.Lindenbaum.ind_on, induction k using fopl.Lindenbaum.ind_on,
     simp[has_inf.inf, has_le.le], refine provable.deduction.mp _, have := provable.add (T^i) (l ⩑ k), simp* at* }

lemma mul_le_r (l k : Lindenbaum T i) : l ⊓ k ≤ k :=
by { induction l using fopl.Lindenbaum.ind_on, induction k using fopl.Lindenbaum.ind_on,
     simp[has_inf.inf, has_le.le], refine provable.deduction.mp _, have := provable.add (T^i) (l ⩑ k), simp* at* }

lemma add_le_l (l k : Lindenbaum T i) : l ≤ l ⊔ k :=
by { induction l using fopl.Lindenbaum.ind_on, induction k using fopl.Lindenbaum.ind_on,
     simp[has_sup.sup, has_le.le, provable.or_l] }

lemma add_le_r (l k : Lindenbaum T i) : k ≤ l ⊔ k :=
by { induction l using fopl.Lindenbaum.ind_on, induction k using fopl.Lindenbaum.ind_on,
     simp[has_sup.sup, has_le.le, provable.or_r] }

private lemma le_trans {l m n : Lindenbaum T i} : l ≤ m → m ≤ n → l ≤ n :=
by { induction l using fopl.Lindenbaum.ind_on,
     induction m using fopl.Lindenbaum.ind_on,
     induction n using fopl.Lindenbaum.ind_on, simp[has_le.le], refine provable.imp_trans }

private lemma sup_le {l m n : Lindenbaum T i} : l ≤ n → m ≤ n → l ⊔ m ≤ n :=
by { induction l using fopl.Lindenbaum.ind_on,
     induction m using fopl.Lindenbaum.ind_on,
     induction n using fopl.Lindenbaum.ind_on, simp[has_le.le, has_sup.sup],
     intros h₁ h₂, exact provable.hyp_or h₁ h₂   }

private lemma le_inf {l m n : Lindenbaum T i} : l ≤ m → l ≤ n → l ≤ m ⊓ n :=
by { induction l using fopl.Lindenbaum.ind_on,
     induction m using fopl.Lindenbaum.ind_on,
     induction n using fopl.Lindenbaum.ind_on,
     simp[has_le.le, has_inf.inf],
     refine λ h₁ h₂, provable.deduction.mp _, simp,
     refine ⟨provable.deduction.mpr h₁, provable.deduction.mpr h₂⟩  }

private lemma le_sup_inf {l m n : Lindenbaum T i} : (l ⊔ m) ⊓ (l ⊔ n) ≤ l ⊔ m ⊓ n :=
by { induction l using fopl.Lindenbaum.ind_on,
     induction m using fopl.Lindenbaum.ind_on,
     induction n using fopl.Lindenbaum.ind_on,
     simp[has_sup.sup, has_inf.inf, has_le.le, provable.or_r, formula.or],
     refine provable.deduction.mp (provable.deduction.mp _),
     have lmm₁ : (T^i)+{(¬̇l →̇ m) ⩑ (¬̇l →̇ n)}+{¬̇l} ⊢ (¬̇l →̇ m) ⩑ (¬̇l →̇ n), simp[-provable.and],
     have lmm₂ : (T^i)+{(¬̇l →̇ m) ⩑ (¬̇l →̇ n)}+{¬̇l} ⊢ ¬̇l, simp,
     simp at lmm₁ ⊢, refine ⟨lmm₁.1.MP lmm₂, lmm₁.2.MP lmm₂⟩ }

private lemma sup_inf_sdiff (l m : Lindenbaum T i) : l ⊓ m ⊔ l ⊓ mᶜ = l :=
by { induction l using fopl.Lindenbaum.ind_on, induction m using fopl.Lindenbaum.ind_on,
      simp[Lindenbaum.of_eq_of, has_le.le, has_sup.sup, has_inf.inf, has_compl.compl, has_top.top, formula.or],
      refine ⟨contrapose.mp (deduction.mp _), _⟩, simp,
      have : ∀ n, (T^i)+{¬̇l} ⊢ ¬̇(l ⩑ n),
      { refine λ n, deduction.mpr (contrapose.mpr (deduction.mp _)),
        have : (T^i)+{l ⩑ n} ⊢ l ⩑ n, simp[-provable.and], simp* at* },
      refine ⟨this _, this _⟩,
      refine deduction.mp (deduction.mp _), simp, refine neg_hyp (deduction.mp _),
      refine explosion (show (T^i)+{l}+{¬̇(l ⩑ m)}+{m} ⊢ l ⩑ m, by simp) (by simp) }

private lemma inf_inf_sdiff (l m : Lindenbaum T i) : l ⊓ m ⊓ (l ⊓ mᶜ) = ⊥ :=
by { induction l using fopl.Lindenbaum.ind_on, induction m using fopl.Lindenbaum.ind_on,
     simp[Lindenbaum.of_eq_of, has_le.le, has_sup.sup, has_inf.inf, has_compl.compl, has_bot.bot, formula.or],
     refine deduction.mp (explosion (show (T^i)+{l ⩑ m ⩑ (l ⩑ ¬̇m)} ⊢ m, by simp[axiom_and]) (by simp[axiom_and])) }

private lemma inf_compl_le_bot (l : Lindenbaum T i) : l ⊓ lᶜ ≤ ⊥ :=
by { induction l using fopl.Lindenbaum.ind_on, simp[has_le.le, has_inf.inf, has_compl.compl, has_bot.bot],
     have : (T^i)+{l ⩑ ¬̇l} ⊢ l ⩑ ¬̇l, simp[-provable.and], simp at this,
     refine provable.deduction.mp (provable.explosion this.1 this.2) }

private lemma top_le_sup_compl (l : Lindenbaum T i) : ⊤ ≤ l ⊔ lᶜ :=
by induction l using fopl.Lindenbaum.ind_on; simp[has_le.le, has_sup.sup, has_compl.compl, has_top.top, formula.or]

instance : boolean_algebra (Lindenbaum T i) :=
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

def fal : Lindenbaum T (i+1) → Lindenbaum T i :=
λ p, Lindenbaum.lift_on p (λ p, (⟦∀̇ p⟧ᴸ : Lindenbaum T i)) $
λ p₁ p₂ hyp, by { simp[Lindenbaum.of_eq_of] at*, 
  refine ⟨provable.q2.MP (GE hyp.1), provable.q2.MP (GE hyp.2)⟩ }
prefix `∏ `:90 := fal

def ex : Lindenbaum T (i+1) → Lindenbaum T i :=
λ p, Lindenbaum.lift_on p (λ p, (⟦∃̇ p⟧ᴸ : Lindenbaum T i)) $
λ p₁ p₂ hyp, by { simp[formula.ex, provable.contrapose, Lindenbaum.of_eq_of] at*, 
  refine ⟨provable.q2.MP $ GE $ contrapose.mpr hyp.1, provable.q2.MP $ GE $ contrapose.mpr hyp.2⟩ }
prefix `∐ `:90 := ex

def pow : Lindenbaum T i → Lindenbaum T (i+1) :=
λ p, Lindenbaum.lift_on p (λ p, (⟦p^1⟧ᴸ : Lindenbaum T (i+1))) $
λ p₁ p₂ hyp, by { simp[contrapose, -provable.iff, Lindenbaum.of_eq_of, ←theory.pow_add] at*,
  exact (sf_itr_sf_itr _ _).mpr hyp }

@[simp] lemma pow_compl (l : Lindenbaum T i) : pow (lᶜ) = (pow l)ᶜ :=
by { induction l using fopl.Lindenbaum.ind_on, simp[pow, has_compl.compl] }

@[simp] lemma pow_sup (l m : Lindenbaum T i) : pow (l ⊔ m) = (pow l) ⊔ (pow m) :=
by { induction l using fopl.Lindenbaum.ind_on, induction m using fopl.Lindenbaum.ind_on,
     simp[pow, has_sup.sup, Lindenbaum.of_eq_of] }

@[simp] lemma pow_inf (l m : Lindenbaum T i) : pow (l ⊓ m) = (pow l) ⊓ (pow m) :=
by { induction l using fopl.Lindenbaum.ind_on, induction m using fopl.Lindenbaum.ind_on,
     simp[pow, has_inf.inf, Lindenbaum.of_eq_of] }

@[simp] lemma prod_top : ∏ (⊤ : Lindenbaum T (i+1)) = ⊤ :=
by { simp[fal, has_top.top, fopl.Lindenbaum.of_eq_of], 
     apply provable.GE, simp }

lemma prenex_ex_neg (l : Lindenbaum T (i+1)) : (∐ l)ᶜ = ∏ lᶜ :=
by {induction l using fopl.Lindenbaum.ind_on;
   simp[has_compl.compl, ex, fal, Lindenbaum.of_eq_of, formula.ex] }

lemma prenex_fal_neg {l : Lindenbaum T (i+1)} : (∏ l)ᶜ = ∐ lᶜ :=
by { have := prenex_ex_neg lᶜ, simp[-prenex_ex_neg] at this, simp[←this] }

lemma prenex_fal_or_left {l : Lindenbaum T (i+1)} {k : Lindenbaum T i} :
  ∏ l ⊔ k = ∏ (l ⊔ k.pow) :=
begin
  induction l using fopl.Lindenbaum.ind_on, induction k using fopl.Lindenbaum.ind_on,
  simp[fal, has_sup.sup, pow, Lindenbaum.of_eq_of, formula.or], split,
  { refine (deduction.mp $ GE $ contrapose.mp _), rw [←sf_dsb], simp,
    have lmm₁ : ⇑(T^i)+{¬̇(∀̇ l)^1 →̇ k^1} ⊢ ¬̇k^1 →̇ (∀̇ l)^1, { apply contrapose.mp, simp },
    have lmm₂ : ⇑(T^i)+{¬̇(∀̇ l)^1 →̇ k^1} ⊢ (∀̇ l)^1 →̇ l,
    { suffices : ⇑(T^i)+{¬̇(∀̇ l)^1 →̇ k^1} ⊢ (∀̇ l)^1 →̇ (l.rew $ (λ x, #(x + 1))^1).rew ι[0 ⇝ #0],
      { simp[formula.nested_rew] at this, exact this },
      exact provable.q1 },
    exact lmm₁.imp_trans lmm₂ },
  { refine (deduction.mp $ contrapose.mp $ deduction.mp _), simp,
    refine GE _, simp[←sf_dsb], refine deduction.mpr _,
    show ⇑(T^i)+{(∀̇  (¬̇l →̇ k^1))^1} ⊢ ¬̇k^1 →̇ l,
    have : ⇑(T^i)+{(∀̇  (¬̇l →̇ k^1))^1} ⊢ ¬̇l →̇ k^1,
    { have : ⇑(T^i)+{(∀̇  (¬̇l →̇ k^1))^1} ⊢ (∀̇  (¬̇l →̇ k^1))^1, { simp },
      have lmm₁ := this.fal_subst #0, simp at lmm₁,
      simp[formula.nested_rew] at lmm₁,
      exact lmm₁ },
    apply contrapose.mp, simp[this] }
end

lemma prenex_fal_or_right {l : Lindenbaum T i} {k : Lindenbaum T (i+1)} :
  l ⊔ ∏ k = ∏ (l.pow ⊔ k) :=
by simp[show l ⊔ ∏ k = ∏ k ⊔ l, from sup_comm, prenex_fal_or_left,
        show k ⊔ l.pow = l.pow ⊔ k, from sup_comm]

lemma prenex_fal_and_left {l : Lindenbaum T (i+1)} {k : Lindenbaum T i} :
  ∏ l ⊓ k = ∏ (l ⊓ k.pow) :=
begin
  induction l using fopl.Lindenbaum.ind_on, induction k using fopl.Lindenbaum.ind_on,
  simp[fal, has_inf.inf, pow, Lindenbaum.of_eq_of], split,
  { refine (deduction.mp $ GE _), rw [←sf_dsb], simp[axiom_and],
    have : ⇑(T^i)+{(∀̇ l)^1}+{k^1} ⊢ (∀̇ l)^1, simp,
    have := this.fal_subst #0, simp[formula.nested_rew] at this, exact this },
  { refine deduction.mp _, simp,
     split,
    { refine GE _, simp[←sf_dsb],
      have : ⇑(T^i)+{(∀̇ (l ⩑ (k^1)))^1} ⊢ (∀̇ (l ⩑ (k^1)))^1, simp,
      have := this.fal_subst #0, simp[formula.nested_rew] at this, simp* at* },
    { have : (T^i)+{∀̇  (l ⩑ (k^1))} ⊢ ∀̇  (l ⩑ (k^1)), simp,
      have := this.fal_subst #0, simp* at * } }
end

lemma prenex_ex_or_left {l : Lindenbaum T (i+1)} {k : Lindenbaum T i} :
  ∐ l ⊔ k = ∐ (l ⊔ k.pow) :=
begin
  rw ← compl_inj_iff, simp[-compl_inj_iff, prenex_ex_neg, prenex_fal_and_left],
end

namespace proper

variables [proper 0 T]

@[simp] def subst_sf_L_aux (t : term L) :
  Lindenbaum T (i+1) → Lindenbaum T i :=
λ p, Lindenbaum.lift_on p (λ p, (⟦p.rew (ι[i ⇝ t])⟧ᴸ : Lindenbaum T i)) $
λ p₁ p₂ hyp, by { simp[Lindenbaum.of_eq_of, -provable.iff] at*,
    exact provable.pow_subst' i hyp t }

def subst_sf_L : Herbrand T i → Lindenbaum T (i+1) → Lindenbaum T i :=
λ t l, Herbrand.lift_on t (λ t, subst_sf_L_aux t l) $
λ t₁ t₂ hyp, by { induction l using fopl.Lindenbaum.ind_on,
  simp[Lindenbaum.of_eq_of, -provable.iff] at*,
  refine equal_rew_iff (λ m, _) l,
  have C : m < i ∨ m = i ∨ i < m, from trichotomous _ _,
  cases C,
  { simp[C] }, cases C; simp[C],
  { refine hyp } }
infixr ` ⊳ `:90  := subst_sf_L

lemma fal_le_subst (l : Lindenbaum T (i + 1)) (h : Herbrand T i) : ∏ (♯0 ⊳ l.pow) ≤ h ⊳ l :=
begin
  induction l using fopl.Lindenbaum.ind_on with p, 
  induction h using fopl.Herbrand.ind_on with t, 
  simp[fal, has_le.le, subst_sf_L, pow, var],
  have : T^i ⊢ ∀̇ (p^1).rew ι[(i + 1) ⇝ #0] →̇ ((p^1).rew ι[(i + 1) ⇝ #0]).rew ι[0 ⇝ t],
    from @provable.q1 _ (T^i) ((p^1).rew ι[(i + 1) ⇝ #0]) t,
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
  induction l using fopl.Lindenbaum.ind_on with p, 
  induction h using fopl.Herbrand.ind_on with t, 
  simp[fal, has_le.le, subst_sf_L]
end

lemma subst_sf_L_le_ex (l : Lindenbaum T 1) (h) : h ⊳ l ≤ ∐ l :=
begin
  induction l using fopl.Lindenbaum.ind_on, 
  induction h using fopl.Herbrand.ind_on, 
  simp[ex, has_le.le, subst_sf_L],
  apply contrapose.mp, simp[formula.ex],
  rw (show ¬̇(l.rew ι[0 ⇝ h]) = (¬̇l).rew ι[0 ⇝ h], by simp), 
  exact provable.q1
end

lemma le_fal_le_fal {l m : Lindenbaum T (i + 1)} :
  l ≤ m → ∏ l ≤ ∏ m :=
begin
  induction l using fopl.Lindenbaum.ind_on, 
  induction m using fopl.Lindenbaum.ind_on, 
  simp[fal, has_le.le, subst_sf_L, pow],
  { intros h, refine provable.q2.MP (GE h) },
end

@[simp] lemma dummy_fal (l : Lindenbaum T i) : ∏ pow l = l :=
by { induction l using fopl.Lindenbaum.ind_on, 
     simp[pow, fal, Lindenbaum.of_eq_of],
     have := @provable.dummy_fal_quantifir _ (T^i) l, simp at this,
     exact this }

lemma pow_le_le_fal {l : Lindenbaum T i} {m : Lindenbaum T (i + 1)} :
  l.pow ≤ m → l ≤ ∏ m :=
by { have := @le_fal_le_fal _ _ _ _ l.pow m, simp at this, exact this }

@[simp] lemma subst_sf_L_compl (h : Herbrand T i) (l : Lindenbaum T (i+1)) :
  h ⊳ (lᶜ)= (h ⊳ l)ᶜ :=
by { induction l using fopl.Lindenbaum.ind_on, 
     induction h using fopl.Herbrand.ind_on,
     simp[has_compl.compl, has_le.le, subst_sf_L, Lindenbaum.of_eq_of] }

@[simp] lemma subst_sf_L_and (h : Herbrand T i) (l m : Lindenbaum T (i+1)) :
  h ⊳ (l ⊓ m) = h ⊳ l ⊓ h ⊳ m :=
by { induction l using fopl.Lindenbaum.ind_on, induction m using fopl.Lindenbaum.ind_on, 
     induction h using fopl.Herbrand.ind_on,
     simp[has_inf.inf, has_le.le, subst_sf_L, Lindenbaum.of_eq_of] }

@[simp] lemma subst_sf_L_or (h : Herbrand T i) (l m : Lindenbaum T (i+1)) :
  h ⊳ (l ⊔ m) = h ⊳ l ⊔ h ⊳ m :=
by { induction l using fopl.Lindenbaum.ind_on, induction m using fopl.Lindenbaum.ind_on, 
     induction h using fopl.Herbrand.ind_on,
     simp[has_sup.sup, has_le.le, subst_sf_L, Lindenbaum.of_eq_of] }

@[simp] lemma subst_sf_L_equal (h₁ : Herbrand T i) (h₂ h₃ : Herbrand T (i+1)) :
  h₁ ⊳ (h₂ ∥ h₃) = (h₁ ⊳ᴴ h₂) ∥ (h₁ ⊳ᴴ h₃) :=
by { induction h₁ using fopl.Herbrand.ind_on, induction h₂ using fopl.Herbrand.ind_on,
     induction h₃ using fopl.Herbrand.ind_on,
     simp[equal, subst_sf_L, Herbrand.proper.subst_sf_H, Herbrand.proper.subst_sf_H_aux,
       Lindenbaum.of_eq_of] }

@[simp] lemma subst_sf_L_fal (h : Herbrand T i) (l : Lindenbaum T (i+2)) :
  h ⊳ ∏ l = ∏ (h.pow ⊳ l) :=
by { induction l using fopl.Lindenbaum.ind_on,
     induction h using fopl.Herbrand.ind_on,
     simp[fal, has_le.le, subst_sf_L, Lindenbaum.of_eq_of, Herbrand.pow, pow, subst_pow] }

@[simp] lemma subst_sf_L_ex (h : Herbrand T i) (l : Lindenbaum T (i+2)) :
  h ⊳ ∐ l = ∐ (h.pow ⊳ l) :=
by { induction l using fopl.Lindenbaum.ind_on,
     induction h using fopl.Herbrand.ind_on,
     simp[ex, has_le.le, subst_sf_L, Lindenbaum.of_eq_of, Herbrand.pow, pow, subst_pow] }

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

@[simp] lemma pow_fal1 (l : Lindenbaum T 1) : pow (∏ l) = ∏ (♯0 ⊳ pow (pow l)) :=
by { induction l using fopl.Lindenbaum.ind_on, 
     simp[pow, fal, Lindenbaum.of_eq_of, subst_sf_L, var, formula.pow_eq, formula.nested_rew, rewriting_sf_itr.pow_eq'],
     have : (λ x, ite (x < 1) #x #(x - 1 + 1 + 1) : ℕ → term L) = (λ x, ι[(1 + 1) ⇝ #0] (x + 1 + 1)),
     { funext x, simp[slide', ι], cases x; simp[← nat.add_one] },
     simp [this] }

end proper


@[simp] lemma compl_sup_iff_le (l m : Lindenbaum T i) : lᶜ ⊔ m = ⊤ ↔ l ≤ m :=
by { induction l using fopl.Lindenbaum.ind_on,
     induction m using fopl.Lindenbaum.ind_on,
     simp[has_le.le, has_top.top, has_compl.compl, has_sup.sup, Lindenbaum.of_eq_of, formula.or] }

@[simp] lemma fal_top_top : (∏ ⊤ : Lindenbaum T i) = ⊤ :=
by { simp[has_top.top, fal, Lindenbaum.of_eq_of], apply provable.GE, simp }

@[simp] lemma ex_top_top : (∐ ⊤ : Lindenbaum T i) = ⊤ :=
by { simp[has_top.top, ex, Lindenbaum.of_eq_of], apply provable.use #0, simp }

theorem provable_top_iff {p} : T^i ⊢ p ↔ (⟦p⟧ᴸ : Lindenbaum T i) = ⊤ := by simp[has_top.top, Lindenbaum.of_eq_of]
theorem provable_top_iff0 {p} : T ⊢ p ↔ (⟦p⟧ᴸ : Lindenbaum T 0) = ⊤ := by simp[has_top.top, Lindenbaum.of_eq_of]

protected theorem provable_iff {p q} : T^i ⊢ p ↔̇ q ↔ (⟦p⟧ᴸ : Lindenbaum T i) = ⟦q⟧ᴸ :=
by simp[Lindenbaum.of_eq_of]

protected theorem provable_iff0 {p q} : T ⊢ p ↔̇ q ↔ (⟦p⟧ᴸ : Lindenbaum T 0) = ⟦q⟧ᴸ :=
by simp[Lindenbaum.of_eq_of]

theorem provable_imp_iff {p q} : T^i ⊢ p →̇ q ↔ (⟦p⟧ᴸ : Lindenbaum T i) ≤ ⟦q⟧ᴸ := by simp[has_le.le]
theorem provable_imp_iff0 {p q} : T ⊢ p →̇ q ↔ (⟦p⟧ᴸ : Lindenbaum T 0) ≤ ⟦q⟧ᴸ := by simp[has_le.le]

@[simp] lemma provable_top_eq : (⟦⊤̇⟧ᴸ : Lindenbaum T i) = ⊤ := rfl
@[simp] lemma provable_bot_eq : (⟦⊥̇⟧ᴸ : Lindenbaum T i) = ⊥ := rfl
@[simp] theorem provable_and_eq {p q} : (⟦p ⩑ q⟧ᴸ : Lindenbaum T i) = ⟦p⟧ᴸ ⊓ ⟦q⟧ᴸ := rfl
@[simp] theorem provable_or_eq {p q} : (⟦p ⩒ q⟧ᴸ : Lindenbaum T i) = ⟦p⟧ᴸ ⊔ ⟦q⟧ᴸ := rfl
@[simp] theorem provable_neg_eq {p} : (⟦¬̇p⟧ᴸ : Lindenbaum T i) = ⟦p⟧ᴸᶜ := rfl
@[simp] theorem provable_imp_eq {p q} : (⟦p →̇ q⟧ᴸ : Lindenbaum T i) = ⟦p⟧ᴸᶜ ⊔ ⟦q⟧ᴸ := by {
  have : (⟦p →̇ q⟧ᴸ : Lindenbaum T i) = ⟦¬̇p ⩒ q⟧ᴸ, 
  { simp[Lindenbaum.of_eq_of, -provable_or_eq, formula.or], refine ⟨deduction.mp (by simp), deduction.mp _⟩,
    have : (T^i)+{¬̇¬̇p →̇ q} ⊢ ¬̇¬̇p →̇ q, simp[-dn1_iff], simp* at* },
  simp[this] }
lemma subst_eq [proper 0 T] (p : formula L) (t : term L) :
  (⟦p.rew ι[i ⇝ t]⟧ᴸ : Lindenbaum T i) = ⟦t⟧ᴴ ⊳ ⟦p⟧ᴸ := rfl

lemma pow_eq (p : formula L) (j : ℕ) :
  (⟦p^1⟧ᴸ : Lindenbaum T (i + 1)) = ⟦p⟧ᴸ.pow := rfl
@[simp] lemma provable_equal_eq {t₁ t₂} : (⟦t₁ =̇ t₂⟧ᴸ : Lindenbaum T i) = ⟦t₁⟧ᴴ ∥ ⟦t₂⟧ᴴ := rfl
@[simp] theorem provable_predicate₁_iff {p : L.pr 1} {t} : (⟦formula.app p fin[t]⟧ᴸ : Lindenbaum T i) = predicate₁ p ⟦t⟧ᴴ := rfl
@[simp] theorem provable_predicate₂_iff {p : L.pr 2} {t₁ t₂} :
  (⟦formula.app p fin[t₁, t₂]⟧ᴸ : Lindenbaum T i) = predicate₂ p ⟦t₁⟧ᴴ ⟦t₂⟧ᴴ := rfl 

@[simp] theorem provable_fal_eq {p} : (⟦∀̇ p⟧ᴸ : Lindenbaum T i) = ∏  ⟦p⟧ᴸ := rfl
@[simp] theorem provable_ex_eq {p} : (⟦∃̇ p⟧ᴸ : Lindenbaum T i) = ∐  ⟦p⟧ᴸ := rfl

lemma to_Herbrand {h₁ h₂ : Herbrand T i} : h₁ ∥ h₂ = ⊤ ↔ h₁ = h₂ :=
by { induction h₁ using fopl.Herbrand.ind_on, induction h₂ using fopl.Herbrand.ind_on,
     simp only [equal, Herbrand.of_eq_of, has_top.top],
     simp[-provable_equal_eq, -provable_top_eq, Lindenbaum.of_eq_of] }

theorem provable_neg_iff {p} : T^i ⊢ ¬̇p ↔ (⟦p⟧ᴸ : Lindenbaum T i) = ⊥ :=
by simp[provable_top_iff]

end Lindenbaum

lemma Lindenbaum.theory (C : theory L) (i : ℕ) : set (Lindenbaum T i) := {l | ∃ p, p ∈ C ∧ l = ⟦p⟧ᴸ}

end fopl