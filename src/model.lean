import deduction semantics

universes u

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

theorem vecterm_equiv_equivalence (T : theory L) (n) : equivalence (vecterm.equiv T n) :=
⟨vecterm.equiv_refl T, λ _ _ , vecterm.equiv_symm T, λ _ _ _, vecterm.equiv_trans T⟩

def Herbrand (n) : Type u :=
quotient (⟨vecterm.equiv T n, vecterm_equiv_equivalence T n⟩ : setoid (vecterm L n))

def vecterm.quo (T : theory L) {n} (t : vecterm L n) : Herbrand T n := quotient.mk' t

notation `⟦`v`⟧ᵗ.`T :max := vecterm.quo T v

instance (T : theory L) : inhabited (Herbrand T 0) := ⟨⟦#0⟧ᵗ.T⟩

namespace Herbrand
variables {T}

@[elab_as_eliminator]
protected lemma ind_on {n} {C : Herbrand T n → Prop} (d : Herbrand T n)
  (h : ∀ t : vecterm L n, C ⟦t⟧ᵗ.T) : C d :=
quotient.induction_on' d h

@[elab_as_eliminator, reducible]
protected def lift_on {φ} {n} (d : Herbrand T n) (f : vecterm L n → φ)
  (h : ∀ v u : vecterm L n, v ≃[T] u → f v = f u) : φ :=
quotient.lift_on' d f h

@[simp]
protected lemma lift_on_eq {φ} {n} (t : vecterm L n) (f : vecterm L n → φ)
  (h : ∀ v u, v ≃[T] u → f v = f u) : fopl.Herbrand.lift_on ⟦t⟧ᵗ.T f h = f t := rfl

@[elab_as_eliminator, reducible, simp]
protected def lift_on₂ {φ} {n} (d₁ d₂ : Herbrand T n) (f : vecterm L n → vecterm L n → φ)
  (h : ∀ t₁ t₂ u₁ u₂, (t₁ ≃[T] u₁) → (t₂ ≃[T] u₂) → f t₁ t₂ = f u₁ u₂) : φ :=
quotient.lift_on₂' d₁ d₂ f h

@[simp]
protected lemma lift_on₂_eq {φ} {n} (t u : vecterm L n) (f : vecterm L n → vecterm L n → φ)
  (h : ∀ t₁ t₂ u₁ u₂, (t₁ ≃[T] u₁) → (t₂ ≃[T] u₂) → f t₁ t₂ = f u₁ u₂) :
  fopl.Herbrand.lift_on₂ ⟦t⟧ᵗ.T ⟦u⟧ᵗ.T f h = f t u := rfl

#check quotient.lift

@[simp] lemma of_eq_of {n} {t u : vecterm L n} : ⟦t⟧ᵗ.T = ⟦u⟧ᵗ.T ↔ (t ≃[T] u) :=
by simp[vecterm.quo, vecterm.equiv, quotient.eq']

def dvector.cons'_aux (T : theory L) (t : term L) : ∀ n, Herbrand T n → Herbrand T (n+1) :=
λ n p, Herbrand.lift_on p (λ v, ⟦vecterm.cons t v⟧ᵗ.T) $
  λ p₁ p₂ hyp, by simp* at*

def dvector.cons' : ∀ {n}, Herbrand T 0 → Herbrand T n → Herbrand T (n+1) :=
λ n t, Herbrand.lift_on t (λ t, dvector.cons'_aux T t n) $
  λ t₁ t₂ hyp, by { simp, funext e, induction e using fopl.Herbrand.ind_on,
  simp[dvector.cons'_aux], refine hyp }

def dvector_to_herbrand : ∀ {n}, dvector (Herbrand T 0) (n+1) → Herbrand T n
| 0     c        := c.extract
| (n+1) (a :: v) := dvector.cons' a (dvector_to_herbrand v)

def symbol.pconstant (c : L.pr 0) : Prop := T ⊢̇ form.const c

def symbol.fn' {n} (f : L.fn (n+1)) : Herbrand T n → Herbrand T 0 :=
λ e, Herbrand.lift_on e (λ v, ⟦vecterm.app f v⟧ᵗ.T) $
  λ t₁ t₂ hyp, by { simp* at*,
  refine (show T ⊢̇ t₁ ≡̇ t₂ →̇ vecterm.app f t₁ =̇ vecterm.app f t₂, by simp).MP hyp }

def symbol.fn : ∀ {n} (f : L.fn n), dvector (Herbrand T 0) n → Herbrand T 0
| 0     c _ := ⟦vecterm.const c⟧ᵗ.T
| (n+1) f v := symbol.fn' f (dvector_to_herbrand v)

def symbol.pr' {n} (p : L.pr (n+1)) : Herbrand T n → Prop :=
λ e, Herbrand.lift_on e (λ v, T ⊢̇ form.app p v) $
  λ t₁ t₂ hyp, by { simp[-provable.iff],  }

def symbol.pr : ∀ {n} (f : L.pr n), dvector (Herbrand T 0) n → Prop
| 0     c _ := T ⊢̇ form.const c
| (n+1) p v := symbol.pr' p (dvector_to_herbrand v)

def model (T : theory L) : model L := ⟨Herbrand T 0, ⟦#0⟧ᵗ.T, @symbol.fn _ T, @symbol.pr _ T⟩
notation `𝔗[`T`]` := model T


end Herbrand

theorem form_equiv_equivalence : equivalence (form.equiv T) :=
⟨λ _, by simp[form.equiv], λ _ _, by simp[form.equiv]; exact λ h₁ h₂, ⟨h₂, h₁⟩,
 λ _ _ _, by { simp[form.equiv], intros h₁ h₂ h₃ h₄, refine ⟨h₁.imp_trans h₃, h₄.imp_trans h₂⟩ }⟩

def Lindenbaum : Type u :=
quotient (⟨form.equiv T, form_equiv_equivalence T⟩ : setoid (form L))

def form.quo (T : theory L) (p : form L) : Lindenbaum T := quotient.mk' p

notation `⟦`p`⟧.`T :max := form.quo T p

namespace Lindenbaum
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
infixr ` ⊐ `:60 := imply

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

lemma provable_GE {l : Lindenbaum ⇑T} : □l → □∏l :=
by { induction l using fopl.Lindenbaum.ind_on, simp[fal, provable], exact provable.GE }

lemma provable_K {l k : Lindenbaum T} : □(l ⊐ k) → □l → □k :=
begin
  induction l using fopl.Lindenbaum.ind_on,
  induction k using fopl.Lindenbaum.ind_on,
  simp[imply, provable], refine λ h₁ h₂, h₁.MP h₂
end

lemma double_inv (l : Lindenbaum T) : l⁻¹⁻¹ = l :=
by induction l using fopl.Lindenbaum.ind_on; simp[has_inv.inv]

#check provable.prenex_fal_quantifir_imp1 _ _

lemma prenex_fal_quantifir_imp1  {l : Lindenbaum ⇑T} {k : Lindenbaum T} : ∏l ⊐ k = ∐(l ⊐ k.sf) := by sorry

lemma prenex_fal_quantifir_neg  {l : Lindenbaum ⇑T} : (∏l)⁻¹ = ∐l⁻¹  := by sorry

@[simp] lemma provable_one : □(1 : Lindenbaum T) :=
by simp[has_one.one, provable]

@[simp] lemma one_maximum {l : Lindenbaum T} : l ≤ 1 :=
by induction l using fopl.Lindenbaum.ind_on; simp[has_one.one, has_le.le]

@[simp] lemma zero_minimum {l : Lindenbaum T} : 0 ≤ l :=
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

end Lindenbaum

end fopl