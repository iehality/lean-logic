import deduction semantics

universes u v

namespace fopl
variables {L : language.{u}} (T : theory L)

@[simp] def vecterm.equiv (T : theory L) : ∀ n, vecterm L n → vecterm L n → Prop := λ _ v₁ v₂, T ⊢̇ v₁ ≡̇ v₂

notation v` ≃[`T :80`] `u:60 := vecterm.equiv T _ v u

@[simp] lemma veq_eq (t u : vecterm L 0) : t ≡̇ u = t =̇ u := rfl

def vecsubst (p : form L) : ∀ {n}, vecterm L n → form L
| 0     t                  := p.(t)
| (n+1) (vecterm.cons t v) := (vecsubst v.sf).(t)

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

notation `⟦`v`⟧ᵗ.`T :max := vecterm.quo T v
local infix ` ≋ `:80 := (@setoid.vec_r _ (herbrand T) _)

instance (T : theory L) : inhabited (Herbrand T) := ⟨⟦#0⟧ᵗ.T⟩

namespace Herbrand
variables {T}

@[elab_as_eliminator]
protected lemma ind_on {C : Herbrand T → Prop} (d : Herbrand T)
  (h : ∀ t : term L, C ⟦t⟧ᵗ.T) : C d :=
quotient.induction_on' d h

@[elab_as_eliminator, reducible]
protected def lift_on {φ} (d : Herbrand T) (f : term L → φ)
  (h : ∀ v u : term L, T ⊢̇ v =̇ u → f v = f u) : φ :=
quotient.lift_on' d f h

@[simp]
protected lemma lift_on_eq {φ} (t : term L) (f : term L → φ)
  (h : ∀ v u, T ⊢̇ v =̇ u → f v = f u) : fopl.Herbrand.lift_on ⟦t⟧ᵗ.T f h = f t := rfl

@[elab_as_eliminator, reducible, simp]
protected def lift_on₂ {φ} (d₁ d₂ : Herbrand T) (f : term L → term L → φ)
  (h : ∀ t₁ t₂ u₁ u₂, (T ⊢̇ t₁ =̇ u₁) → (T ⊢̇ t₂ =̇ u₂) → f t₁ t₂ = f u₁ u₂) : φ :=
quotient.lift_on₂' d₁ d₂ f h

@[simp]
protected lemma lift_on₂_eq {φ} (t u : term L) (f : term L → term L → φ)
  (h : ∀ t₁ t₂ u₁ u₂, (T ⊢̇ t₁ =̇ u₁) → (T ⊢̇ t₂ =̇ u₂) → f t₁ t₂ = f u₁ u₂) :
  fopl.Herbrand.lift_on₂ ⟦t⟧ᵗ.T ⟦u⟧ᵗ.T f h = f t u := rfl

@[simp] lemma of_eq_of {t u : term L} : ⟦t⟧ᵗ.T = ⟦u⟧ᵗ.T ↔ (T ⊢̇ t =̇ u) :=
by simp[vecterm.quo, vecterm.equiv, quotient.eq']

@[elab_as_eliminator, reducible]
protected def lift_on_vec {φ} {n} (v : dvector (Herbrand T) n) (f : dvector (term L) n → φ)
  (h : ∀ (a b : dvector (term L) n), a ≋ b → f a = f b) : φ :=
quotient.lift_on_vec v f h

@[simp]
protected lemma lift_on_vec_eq {φ} {n} (u : dvector (term L) n) (f : dvector (term L) n → φ)
  (h : ∀ (v u : dvector (term L) n), v ≋ u → f v = f u) :
fopl.Herbrand.lift_on_vec ᵥ⟦u⟧ f h = f u := quotient.lift_on_vec_eq u f h

def symbol.pconstant (c : L.pr 0) : Prop := T ⊢̇ form.const c

@[simp] lemma equivs_equals : ∀ {n} (v₁ v₂ : dvector (term L) (n+1)),
  v₁ ≋ v₂ ↔ (T ⊢̇ v₁.to_vecterm ≡̇ v₂.to_vecterm)
| 0 (t₁ :: dvector.nil) (t₂ :: dvector.nil) := by { simp, refl }
| (n+1) (t₁ :: v₁) (t₂ :: v₂) := by { simp[equivs_equals v₁ v₂], intros, refl }

def symbol.fn : ∀ {n} (f : L.fn n), dvector (Herbrand T) n → Herbrand T
| 0     c _ := ⟦vecterm.const c⟧ᵗ.T
| (n+1) f v := fopl.Herbrand.lift_on_vec v (λ u : dvector (term L) (n+1), ⟦vecterm.app f (u.to_vecterm)⟧ᵗ.T) 
  $ λ v₁ v₂ eqn, by { simp at*, refine provable.e4.MP eqn }

def symbol.pr : ∀ {n} (f : L.pr n), dvector (Herbrand T) n → Prop
| 0     c _ := T ⊢̇ form.const c
| (n+1) p v := fopl.Herbrand.lift_on_vec v (λ u : dvector (term L) (n+1), T ⊢̇ form.app p (u.to_vecterm))
  $ λ v₁ v₂ eqn, by { simp at*, refine ⟨(provable.e5.MP eqn).MP, (provable.e5.MP (vecterm.equiv_symm _ eqn)).MP⟩  }

def model (T : theory L) : model L := ⟨Herbrand T, ⟦#0⟧ᵗ.T, @symbol.fn _ T, @symbol.pr _ T⟩
notation `𝔗[`T`]` := model T

end Herbrand

lemma empty_has_model : ∃ 𝔄 : model L, 𝔄 ⊧ₜₕ (∅ : theory L) :=
⟨𝔗[∅], λ p h, by { exfalso, refine set.not_mem_empty p h }⟩

theorem empty_consistent : theory.consistent (∅ : theory L) := @model_consistent L 𝔗[∅] ∅
(λ p h, by { exfalso, refine set.not_mem_empty p h })

theorem form_equiv_equivalence : equivalence (form.equiv T) :=
⟨λ _, by simp[form.equiv], λ _ _, by simp[form.equiv]; exact λ h₁ h₂, ⟨h₂, h₁⟩,
 λ _ _ _, by { simp[form.equiv], intros h₁ h₂ h₃ h₄, refine ⟨h₁.imp_trans h₃, h₄.imp_trans h₂⟩ }⟩

def Lindenbaum : Type u :=
quotient (⟨form.equiv T, form_equiv_equivalence T⟩ : setoid (form L))

def form.quo (T : theory L) (p : form L) : Lindenbaum T := quotient.mk' p

notation `⟦`p`⟧.`T :max := form.quo T p

namespace Lindenbaum
open provable
variables {T}

@[elab_as_eliminator]
protected lemma ind_on {C : Lindenbaum T → Prop} (d : Lindenbaum T)
  (h : ∀ p : form L, C ⟦p⟧.T) : C d :=
quotient.induction_on' d h

@[elab_as_eliminator, reducible]
protected def lift_on {φ} (d : Lindenbaum T) (f : form L → φ)
  (h : ∀ p q : form L, T ⊢̇ p ↔̇ q → f p = f q) : φ :=
quotient.lift_on' d f h

@[simp]
protected lemma lift_on_eq {φ} (p : form L) (f : form L → φ)
  (h : ∀ p q, T ⊢̇ p ↔̇ q → f p = f q) : fopl.Lindenbaum.lift_on ⟦p⟧.T f h = f p := rfl

@[elab_as_eliminator, reducible, simp]
protected def lift_on₂ {φ} (d₁ d₂ : Lindenbaum T) (f : form L → form L → φ)
  (h : ∀ p₁ p₂ q₁ q₂, T ⊢̇ p₁ ↔̇ q₁ → T ⊢̇ p₂ ↔̇ q₂ → f p₁ p₂ = f q₁ q₂) : φ :=
quotient.lift_on₂' d₁ d₂ f h

@[simp]
protected lemma lift_on₂_eq {φ} (p q : form L) (f : form L → form L → φ)
  (h : ∀ p₁ p₂ q₁ q₂, T ⊢̇ p₁ ↔̇ q₁ → T ⊢̇ p₂ ↔̇ q₂ → f p₁ p₂ = f q₁ q₂) :
  fopl.Lindenbaum.lift_on₂ ⟦p⟧.T ⟦q⟧.T f h = f p q := rfl

@[simp] lemma of_eq_of {p q : form L} : ⟦p⟧.T = ⟦q⟧.T ↔ T ⊢̇ p ↔̇ q :=
by simp[form.quo, form.equiv, quotient.eq']

instance : has_le (Lindenbaum T) :=
⟨λ p₁ p₂, Lindenbaum.lift_on₂ p₁ p₂ (λ p₁ p₂, T ⊢̇ p₁ →̇ p₂) $
 λ p₁ p₂ q₁ q₂ hp hq, by { simp at*,
   exact ⟨λ h, (hp.2.imp_trans h).imp_trans hq.1, λ h, (hp.1.imp_trans h).imp_trans hq.2⟩ }⟩

instance : has_lt (Lindenbaum T) := ⟨λ l k, l ≤ k ∧ ¬k ≤ l⟩

def imply : Lindenbaum T → Lindenbaum T → Lindenbaum T :=
λ p₁ p₂, Lindenbaum.lift_on₂ p₁ p₂ (λ p₁ p₂, ⟦p₁ →̇ p₂⟧.T) $
 λ p₁ p₂ q₁ q₂ hp hq, by { simp at*, split,
   { refine provable.deduction.mp (provable.deduction.mp _),
     have : T+{p₁ →̇ p₂}+{q₁} ⊢̇ p₁, from (show _ ⊢̇ q₁ →̇ p₁, by simp[hp]).MP (by simp),
     have : T+{p₁ →̇ p₂}+{q₁} ⊢̇ p₂, from (show _ ⊢̇ p₁ →̇ p₂, by simp).MP this,
     exact (show T+{p₁ →̇ p₂}+{q₁} ⊢̇ p₂ →̇ q₂, by simp[hq]).MP this },
   { refine provable.deduction.mp (provable.deduction.mp _),
     have : T+{q₁ →̇ q₂}+{p₁} ⊢̇ q₁, from (show _ ⊢̇ p₁ →̇ q₁, by simp[hp]).MP (by simp),
     have : T+{q₁ →̇ q₂}+{p₁} ⊢̇ q₂, from (show _ ⊢̇ q₁ →̇ q₂, by simp).MP this,
     exact (show _ ⊢̇ q₂ →̇ p₂, by simp[hq]).MP this  } }
infixr ` ⊳ `:60 := imply

instance : has_mul (Lindenbaum T) :=
⟨λ p₁ p₂, Lindenbaum.lift_on₂ p₁ p₂ (λ p₁ p₂, ⟦p₁ ⩑ p₂⟧.T) $
 λ p₁ p₂ q₁ q₂ hp hq, by { simp at*, split,
   { apply provable.deduction.mp,
     have : T+{p₁ ⩑ p₂} ⊢̇ p₁ ⩑ p₂, from provable.add _ _, simp at *,
     refine ⟨(show T+{p₁ ⩑ p₂} ⊢̇ p₁ →̇ q₁, by simp[hp]).MP this.1,
       (show T+{p₁ ⩑ p₂} ⊢̇ p₂ →̇ q₂, by simp[hq]).MP this.2⟩ },
   { apply provable.deduction.mp,
     have : T+{q₁ ⩑ q₂} ⊢̇ q₁ ⩑ q₂, from provable.add _ _, simp at *,
     refine ⟨(show T+{q₁ ⩑ q₂} ⊢̇ q₁ →̇ p₁, by simp[hp]).MP this.1,
       (show T+{q₁ ⩑ q₂} ⊢̇ q₂ →̇ p₂, by simp[hq]).MP this.2⟩ } }⟩

instance : has_add (Lindenbaum T) :=
⟨λ p₁ p₂, Lindenbaum.lift_on₂ p₁ p₂ (λ p₁ p₂, ⟦p₁ ⩒ p₂⟧.T) $
 λ p₁ p₂ q₁ q₂ hp hq, by { simp at*, split,
   { refine (provable.deduction.mp ((provable.or_l _ _).MP (provable.deduction.mpr hp.1))).hyp_or
       (provable.deduction.mp ((provable.or_r _ _).MP (provable.deduction.mpr hq.1))) },
   { refine (provable.deduction.mp ((provable.or_l _ _).MP (provable.deduction.mpr hp.2))).hyp_or
       (provable.deduction.mp ((provable.or_r _ _).MP (provable.deduction.mpr hq.2))) }  }⟩

instance : has_inv (Lindenbaum T) :=
⟨λ p, Lindenbaum.lift_on p (λ p, ⟦¬̇p⟧.T) $
 λ p₁ p₂ hyp, by { simp[provable.contrapose] at*, refine ⟨hyp.2, hyp.1⟩ }⟩

instance : has_one (Lindenbaum T) := ⟨⟦⊤̇⟧.T⟩

instance : has_zero (Lindenbaum T) := ⟨⟦⊥̇⟧.T⟩

def fal : Lindenbaum ⇑T → Lindenbaum T := λ p, Lindenbaum.lift_on p (λ p, ⟦Ȧp⟧.T) $
λ p₁ p₂ hyp, by { simp at*, 
  suffices : ∀ {q₁ q₂}, ⇑T ⊢̇ q₁ →̇ q₂ → T ⊢̇ Ȧq₁ →̇ Ȧq₂, { refine ⟨this hyp.1, this hyp.2⟩ },
  intros q₁ q₂ hyp,
  refine provable.deduction.mp (provable.GE _),
    have lmm₁ : ⇑(T+{Ȧq₁}) ⊢̇ q₁, from provable.add_sf _,
    have lmm₂ : ⇑(T+{Ȧq₁}) ⊢̇ q₁ →̇ q₂, { rw ←sf_dsb, apply provable.weakening, exact hyp },
    exact lmm₂.MP lmm₁ }
prefix `∏`:90 := fal

def ex : Lindenbaum ⇑T → Lindenbaum T := λ p, Lindenbaum.lift_on p (λ p, ⟦Ėp⟧.T) $
λ p₁ p₂ hyp, by { simp[form.ex, provable.contrapose] at*, 
  suffices : ∀ {q₁ q₂}, ⇑T ⊢̇ q₁ →̇ q₂ → T ⊢̇ Ȧ¬̇q₂ →̇ Ȧ¬̇q₁, { refine ⟨this hyp.1, this hyp.2⟩ },
  intros q₁ q₂ hyp,
  refine provable.deduction.mp (provable.GE _),
    have lmm₁ : ⇑(T+{Ȧ¬̇q₂}) ⊢̇ ¬̇q₂, from provable.add_sf _,
    have lmm₂ : ⇑(T+{Ȧ¬̇q₂}) ⊢̇ ¬̇q₂ →̇ ¬̇q₁,
    { simp[provable.contrapose], rw ←sf_dsb, apply provable.weakening, exact hyp },
    exact lmm₂.MP lmm₁ }
prefix `∐`:90 := ex

@[simp] def predicate : ∀ {n} (f : L.pr n), dvector (Herbrand T) n → Lindenbaum T
| 0     c _ := ⟦form.const c⟧.T
| (n+1) p v := fopl.Herbrand.lift_on_vec v (λ u : dvector (term L) (n+1), ⟦form.app p (u.to_vecterm)⟧.T)
  $ λ v₁ v₂ eqn, by { simp at*, refine ⟨provable.e5.MP eqn, provable.e5.MP (vecterm.equiv_symm _ eqn)⟩ }

def predicate₁ (f : L.pr 1) (h : Herbrand T) : Lindenbaum T := predicate f (h :: dvector.nil)

def predicate₂ (f : L.pr 2) (h₁ h₂ : Herbrand T) : Lindenbaum T := predicate f (h₁ :: h₂ :: dvector.nil)

def equal : Herbrand T → Herbrand T → Lindenbaum T :=
λ h₁ h₂, fopl.Herbrand.lift_on₂ h₁ h₂ (λ t₁ t₂, ⟦t₁ =̇ t₂⟧.T) $
λ t₁ t₂ u₁ u₂ eqn₁ eqn₂, by { simp, refine ⟨provable.deduction.mp _, provable.deduction.mp  _⟩,
  have lmm₁ : T+{t₁ =̇ t₂} ⊢̇ u₁ =̇ t₁, simp [provable.e2.MP eqn₁],
  have lmm₂ : T+{t₁ =̇ t₂} ⊢̇ t₁ =̇ t₂, simp,
  have lmm₃ : T+{t₁ =̇ t₂} ⊢̇ t₂ =̇ u₂, simp [eqn₂],
  refine (lmm₁.eq_trans lmm₂).eq_trans lmm₃,
  have lmm₁ : T+{u₁ =̇ u₂} ⊢̇ t₁ =̇ u₁, simp [eqn₁],
  have lmm₂ : T+{u₁ =̇ u₂} ⊢̇ u₁ =̇ u₂, simp,
  have lmm₃ : T+{u₁ =̇ u₂} ⊢̇ u₂ =̇ t₂, simp [provable.e2.MP eqn₂],
  refine (lmm₁.eq_trans lmm₂).eq_trans lmm₃ }
infix ` ⋈ `:80 := equal

def sf : Lindenbaum T → Lindenbaum ⇑T := λ p, Lindenbaum.lift_on p (λ p, ⟦p.sf⟧.⇑T) $
λ p₁ p₂ hyp, by { simp[form.ex, provable.contrapose] at*, have := provable.dummy_fal_quantifir_iff, }

def provable : Lindenbaum T → Prop := λ p, Lindenbaum.lift_on p (λ p, T ⊢̇ p) $
λ p₁ p₂ hyp, by { simp at*, refine ⟨λ h, hyp.1.MP h, λ h, hyp.2.MP h⟩ }
prefix `□`:80 := provable

def refutable : Lindenbaum T → Prop := λ p, ¬□p⁻¹
prefix `◇`:80 := refutable

lemma le_antisymm {l k : Lindenbaum T} : l ≤ k → k ≤ l → l = k :=
begin
  induction l using fopl.Lindenbaum.ind_on,
  induction k using fopl.Lindenbaum.ind_on,
  simp[has_le.le], refine λ h₁ h₂, ⟨h₁, h₂⟩
end

lemma imply_le {l k : Lindenbaum T} : l ⊳ k = 1 ↔ l ≤ k :=


lemma provable_GE {l : Lindenbaum ⇑T} : □l → □∏l :=
by { induction l using fopl.Lindenbaum.ind_on, simp[fal, provable], exact provable.GE }

lemma provable_AX {p} (h : p ∈ T) : ⟦p⟧.T = 1 :=
by simp[has_one.one, provable.AX h]

lemma provable_K {l k : Lindenbaum T} : □(l ⊳ k) → □l → □k :=
begin
  induction l using fopl.Lindenbaum.ind_on,
  induction k using fopl.Lindenbaum.ind_on,
  simp[imply, provable], refine λ h₁ h₂, h₁.MP h₂
end

@[simp] lemma equal_refl {h : Herbrand T}  : h ⋈ h = 1 :=
by induction h using fopl.Herbrand.ind_on; simp[equal, has_one.one]

@[simp] lemma equal_subst₁ {h₁ h₂ : Herbrand T} {p : L.pr 1} : h₁ ⋈ h₂ ≤ predicate₁ p h₁ ⊳ predicate₁ p h₂ :=
by { induction h₁ using fopl.Herbrand.ind_on, induction h₂ using fopl.Herbrand.ind_on,
      simp[equal, has_le.le, imply, has_one.one, predicate₁,
        (show ⟦h₁⟧ᵗ.T :: dvector.nil = ᵥ⟦h₁ :: dvector.nil⟧, by refl),
        (show ⟦h₂⟧ᵗ.T :: dvector.nil = ᵥ⟦h₂ :: dvector.nil⟧, by refl) ], 
        }

lemma double_inv (l : Lindenbaum T) : l⁻¹⁻¹ = l :=
by induction l using fopl.Lindenbaum.ind_on; simp[has_inv.inv]

#check provable.prenex_fal_quantifir_imp1 _ _

lemma prenex_fal_quantifir_imp1  {l : Lindenbaum ⇑T} {k : Lindenbaum T} : ∏l ⊳ k = ∐(l ⊳ k.sf) := by sorry

lemma prenex_fal_quantifir_neg  {l : Lindenbaum ⇑T} : (∏l)⁻¹ = ∐l⁻¹  := by sorry

@[simp] lemma provable_one : □(1 : Lindenbaum T) :=
by simp[has_one.one, provable]

@[simp] lemma one_maximum (l : Lindenbaum T) : l ≤ 1 :=
by induction l using fopl.Lindenbaum.ind_on; simp[has_one.one, has_le.le]

@[simp] lemma zero_minimum (l : Lindenbaum T) : 0 ≤ l :=
by induction l using fopl.Lindenbaum.ind_on; simp[has_zero.zero, has_le.le]

lemma Box_iff {l : Lindenbaum T} : □l ↔ l = 1 :=
by { split, 
     { induction l using fopl.Lindenbaum.ind_on, simp[has_one.one, provable], intros hyp_l,
       refine provable.deduction.mp (provable.weakening hyp_l _) },
     { intros h, simp[h] } }

lemma mul_le_l {l k : Lindenbaum T} : l * k ≤ l :=
by { induction l using fopl.Lindenbaum.ind_on, induction k using fopl.Lindenbaum.ind_on,
     simp[has_mul.mul, has_le.le], refine provable.deduction.mp _, have := provable.add T (l ⩑ k), simp* at * }

lemma mul_le_r {l k : Lindenbaum T} : l * k ≤ k :=
by { induction l using fopl.Lindenbaum.ind_on, induction k using fopl.Lindenbaum.ind_on,
     simp[has_mul.mul, has_le.le], refine provable.deduction.mp _, have := provable.add T (l ⩑ k), simp* at * }

lemma add_le_l {l k : Lindenbaum T} : l ≤ l + k :=
by { induction l using fopl.Lindenbaum.ind_on, induction k using fopl.Lindenbaum.ind_on,
     simp[has_add.add, has_le.le, provable.or_l] }

lemma add_le_r {l k : Lindenbaum T} : k ≤ l + k :=
by { induction l using fopl.Lindenbaum.ind_on, induction k using fopl.Lindenbaum.ind_on,
     simp[has_add.add, has_le.le, provable.or_r] }

private lemma sup_le {l m n : Lindenbaum T} : l ≤ n → m ≤ n → l + m ≤ n :=
by { induction l using fopl.Lindenbaum.ind_on,
       induction m using fopl.Lindenbaum.ind_on,
       induction n using fopl.Lindenbaum.ind_on, simp[has_le.le, has_add.add],
       intros h₁ h₂, exact provable.hyp_or h₁ h₂   }

private lemma le_inf {l m n : Lindenbaum T} : l ≤ m → l ≤ n → l ≤ m * n :=
by { induction l using fopl.Lindenbaum.ind_on,
     induction m using fopl.Lindenbaum.ind_on,
     induction n using fopl.Lindenbaum.ind_on,
     simp[has_le.le, has_mul.mul],
     refine λ h₁ h₂, provable.deduction.mp _, simp,
     refine ⟨provable.deduction.mpr h₁, provable.deduction.mpr h₂⟩  }

private lemma le_sup_inf {l m n : Lindenbaum T} : (l + m) * (l + n) ≤ l + m * n :=
by { induction l using fopl.Lindenbaum.ind_on,
     induction m using fopl.Lindenbaum.ind_on,
     induction n using fopl.Lindenbaum.ind_on,
     simp[has_add.add, has_mul.mul, has_le.le, provable.or_r, form.or],
     refine provable.deduction.mp (provable.deduction.mp _),
     have lmm₁ : T+{(¬̇l →̇ m) ⩑ (¬̇l →̇ n)}+{¬̇l} ⊢̇ (¬̇l →̇ m) ⩑ (¬̇l →̇ n), simp[-provable.and],
     have lmm₂ : T+{(¬̇l →̇ m) ⩑ (¬̇l →̇ n)}+{¬̇l} ⊢̇ ¬̇l, simp,
     simp at lmm₁ ⊢, refine ⟨lmm₁.1.MP lmm₂, lmm₁.2.MP lmm₂⟩ }


private lemma sup_inf_sdiff (l m : Lindenbaum T) : l * m + l * m⁻¹ = l :=
by { induction l using fopl.Lindenbaum.ind_on, induction m using fopl.Lindenbaum.ind_on,
      simp[has_le.le, has_add.add, has_mul.mul, has_inv.inv, has_one.one, form.or],
      refine ⟨contrapose.mp (deduction.mp _), _⟩, simp,
      have : ∀ n, T+{¬̇l} ⊢̇ ¬̇(l ⩑ n),
      { refine λ n, deduction.mpr (contrapose.mpr (deduction.mp _)),
        have : T+{l ⩑ n} ⊢̇ l ⩑ n, simp[-provable.and], simp* at* },
      refine ⟨this _, this _⟩,
      refine deduction.mp (deduction.mp _), simp, refine neg_hyp (deduction.mp _),
      refine explosion (show T+{l}+{¬̇(l ⩑ m)}+{m} ⊢̇ l ⩑ m, by simp) (by simp) }

private lemma inf_inf_sdiff (l m : Lindenbaum T) : l * m * (l * m⁻¹) = 0 :=
by { induction l using fopl.Lindenbaum.ind_on, induction m using fopl.Lindenbaum.ind_on,
     simp[has_le.le, has_add.add, has_mul.mul, has_inv.inv, has_zero.zero, form.or],
     refine deduction.mp (explosion (show T+{l ⩑ m ⩑ (l ⩑ ¬̇m)} ⊢̇ m, by simp[axiom_and]) (by simp[axiom_and])) }

private lemma inf_compl_le_bot (l : Lindenbaum T) : l * l⁻¹ ≤ 0 :=
by { induction l using fopl.Lindenbaum.ind_on, simp[has_le.le, has_mul.mul, has_inv.inv, has_zero.zero],
     have : T+{l ⩑ ¬̇l} ⊢̇ l ⩑ ¬̇l, simp[-provable.and], simp at this,
     refine provable.deduction.mp (provable.explosion this.1 this.2) }

private lemma top_le_sup_compl (l : Lindenbaum T) : 1 ≤ l + l⁻¹ :=
by induction l using fopl.Lindenbaum.ind_on; simp[has_le.le, has_add.add, has_inv.inv, has_one.one, form.or]

instance : boolean_algebra (Lindenbaum T) :=
{ bot := 0,
  top := 1,
  le  := (≤),
  lt  := (<),
  sup := (+),
  inf := (*),
  compl := (λ l, l⁻¹),
  sdiff := (λ l m, l * m⁻¹),
  le_refl := λ l, by induction l using fopl.Lindenbaum.ind_on; simp[has_le.le],
  le_trans := λ l m n,
  by { induction l using fopl.Lindenbaum.ind_on,
       induction m using fopl.Lindenbaum.ind_on,
       induction n using fopl.Lindenbaum.ind_on, simp[has_le.le], refine provable.imp_trans },
  lt_iff_le_not_le := λ l m,
  by { induction l using fopl.Lindenbaum.ind_on,
       induction m using fopl.Lindenbaum.ind_on, simp[has_le.le, has_lt.lt] },
  le_antisymm := λ l m, le_antisymm,
  bot_le := zero_minimum,
  le_sup_left := λ l m, by { induction l using fopl.Lindenbaum.ind_on, induction m using fopl.Lindenbaum.ind_on,
     simp[has_add.add, has_le.le, preorder.le, provable.or_l] },
  le_sup_right := λ l m, by { induction l using fopl.Lindenbaum.ind_on, induction m using fopl.Lindenbaum.ind_on,
     simp[has_add.add, has_le.le, preorder.le, provable.or_r] },
  sup_le := λ _ _ _, sup_le,
  inf_le_left := λ l m, by { induction l using fopl.Lindenbaum.ind_on,
    induction m using fopl.Lindenbaum.ind_on, simp[has_le.le, has_mul.mul, preorder.le],
    refine provable.hyp_and_left (by simp) },
  inf_le_right := λ l m, by { induction l using fopl.Lindenbaum.ind_on,
    induction m using fopl.Lindenbaum.ind_on, simp[has_le.le, has_mul.mul, preorder.le],
    refine provable.hyp_and_right (by simp) },
  le_inf := λ _ _ _, le_inf,
  le_sup_inf := λ _ _ _, le_sup_inf,
  sup_inf_sdiff := sup_inf_sdiff,
  inf_inf_sdiff := inf_inf_sdiff,
  le_top := one_maximum,
  inf_compl_le_bot := inf_compl_le_bot,
  top_le_sup_compl := top_le_sup_compl,
  sdiff_eq := λ _ _, rfl }

end Lindenbaum

end fopl