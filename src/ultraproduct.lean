import deduction model data.equiv.encodable.basic order.filter.ultrafilter
open encodable

universes u v


namespace fopl
variables {L : language.{u}} {I : Type.{v}} [inhabited I] (F : ultrafilter I) {𝔄 : I → model L}

def uequiv : (Π i, |𝔄 i|) → (Π i, |𝔄 i|) → Prop :=
λ u₁ u₂, {i | u₁ i = u₂ i} ∈ F

notation u` ~[`:80 F`] `v:80 := uequiv F u v

lemma uequiv_refl (u : Π i, |𝔄 i|) : u ~[F] u :=
by { simp[uequiv], exact F.univ_sets }

lemma uequiv_symm {u₁ u₂ : Π i, |𝔄 i|} : u₁ ~[F] u₂ → u₂ ~[F] u₁ :=
by { simp[uequiv], have : {i | u₁ i = u₂ i} = {i | u₂ i = u₁ i}, { ext, simp, exact eq_comm }, simp[this] }

lemma uequiv_trans {u₁ u₂ u₃ : Π i, |𝔄 i|} : u₁ ~[F] u₂ → u₂ ~[F] u₃ → u₁ ~[F] u₃ :=
by { simp[uequiv], intros h₁ h₂,
     have : {i | u₁ i = u₂ i} ∩ {i | u₂ i = u₃ i} ⊆ {i | u₁ i = u₃ i},
     { intros i hi, simp* at* },
     exact filter.mem_sets_of_superset (filter.inter_mem_sets h₁ h₂) this }

theorem uequiv_equivalence : equivalence (@uequiv L I _ F 𝔄) :=
⟨uequiv_refl F, λ _ _ , uequiv_symm F, λ _ _ _, uequiv_trans F⟩


@[reducible, simp, instance]
def ult (𝔄 : I → model L) (F : ultrafilter I) : setoid (Π i, |𝔄 i|) := ⟨@uequiv L I _ F 𝔄, uequiv_equivalence F⟩

def Ult (𝔄 : I → model L) (F : ultrafilter I) : Type* :=
quotient (ult 𝔄 F: setoid (Π i, |𝔄 i|))

def to_quotient {𝔄 : I → model L} {F : ultrafilter I} (u : Π i, |𝔄 i|) : Ult 𝔄 F := quotient.mk' u

notation `⟦`u`⟧*` :max := to_quotient u

instance : inhabited (Ult 𝔄 F) := ⟨⟦λ i, (𝔄 i).one⟧*⟩

namespace Ult
@[elab_as_eliminator]
protected lemma ind_on {C : Ult 𝔄 F → Prop} (u : Ult 𝔄 F)
  (h : ∀ u : Π i, |𝔄 i|, C ⟦u⟧*) : C u :=
quotient.induction_on' u h

@[elab_as_eliminator, reducible]
protected def lift_on {φ} (d : Ult 𝔄 F) (f : (Π i, |𝔄 i|) → φ)
  (h : ∀ (v u : Π i, |𝔄 i|), v ~[F] u → f v = f u) : φ :=
quotient.lift_on' d f h

@[simp]
protected lemma lift_on_eq {φ} (u₀ : Π i, |𝔄 i|) (f : (Π i, |𝔄 i|) → φ)
  (h : ∀ v u, v ~[F] u → f v = f u) : fopl.Ult.lift_on F ⟦u₀⟧* f h = f u₀ := rfl

@[elab_as_eliminator, reducible, simp]
protected def lift_on₂ {φ} (u₁ u₂ : Ult 𝔄 F) (f : (Π i, |𝔄 i|) → (Π i, |𝔄 i|) → φ)
  (h : ∀ u₁ u₂ v₁ v₂, u₁ ~[F] v₁ → u₂ ~[F] v₂ → f u₁ u₂ = f v₁ v₂) : φ :=
quotient.lift_on₂' u₁ u₂ f h

@[simp]
protected lemma lift_on₂_eq {φ} (u₁ u₂ : Π i, |𝔄 i|) (f : (Π i, |𝔄 i|) → (Π i, |𝔄 i|) → φ)
  (h : ∀ t₁ t₂ u₁ u₂, (t₁ ~[F] u₁) → (t₂ ~[F] u₂) → f t₁ t₂ = f u₁ u₂) :
  fopl.Ult.lift_on₂ F ⟦u₁⟧* ⟦u₂⟧* f h = f u₁ u₂ := rfl

@[simp] lemma of_eq_of {u₁ u₂ : Π i, |𝔄 i|} : (⟦u₁⟧* : Ult 𝔄 F) = ⟦u₂⟧* ↔ u₁ ~[F] u₂ :=
by simp[to_quotient, quotient.eq']

#check λ i, |𝔄 i|
#check @quotient.lift_on_vec

@[elab_as_eliminator, reducible]
protected def lift_on_vec {φ} {n} (d : dvector (Ult 𝔄 F) n) (f : dvector (Π i, |𝔄 i|) n → φ)
  (h : ∀ (v u : dvector (Π i, |𝔄 i|) n), @setoid.vec_r _ (ult 𝔄 F) _ v u → f v = f u) : φ :=
quotient.lift_on_vec d f h

lemma fn_equiv : ∀ {n} {u₁ u₂ : dvector (Π i, |𝔄 i|) n} (h : @setoid.vec_r _ (ult 𝔄 F) _ u₁ u₂) (f : L.fn n),
  (λ i, (𝔄 i).fn f (u₁.app i)) ~[F] (λ i, (𝔄 i).fn f (u₂.app i))
| 0 dvector.nil dvector.nil _ c := by { simp[uequiv], exact F.univ_sets }
| (n+1) (u₁ :: us₁) (u₂ :: us₂) e f := by { simp[uequiv] at*, sorry }

def Ult_fn (n) (f : L.fn n) : dvector (Ult 𝔄 F) n → Ult 𝔄 F :=
λ v, fopl.Ult.lift_on_vec F v (λ u, (⟦λ i, (𝔄 i).fn f (u.app i)⟧* : Ult 𝔄 F)) $ λ u₁ u₂ eqn,
by { simp, have := fn_equiv F eqn f, refine this }

def Ult_pr (n) (p : L.pr n) : dvector (Ult 𝔄 F) n → Prop :=
λ v, fopl.Ult.lift_on_vec F v (λ u, {i | (𝔄 i).pr p (u.app i)} ∈ F) $ λ u₁ u₂ eqn,
by { simp, have := fn_equiv F eqn, refine this }

def model (𝔄 : I → model L) (F : ultrafilter I) : model L := ⟨Ult 𝔄 F, default _, Ult_fn F, Ult_pr F⟩
notation `Π`𝔄`/`F := model 𝔄 F


end Ult


end fopl