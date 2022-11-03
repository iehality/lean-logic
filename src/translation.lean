import lib.lib

universes u v
open_locale logic_symbol
namespace logic
section

class translation (α : Type u) (β : Type v) :=
(tr : α → β)

namespace translation
variables (α : Type*) (β : Type*) (γ : Type*)

instance : translation α α := ⟨id⟩

def comp [translation α β] [translation β γ] : translation α γ := ⟨(tr : β → γ) ∘ (tr : α → β)⟩

end translation

end

section
variables (F : Type u) (G : Type v) [has_logic_symbol F] [has_logic_symbol G]

set_option old_structure_cmd true
structure homomorphism :=
(to_fun : F → G)
(map_neg' : ∀ a, to_fun (∼a) = ∼to_fun a)
(map_imply' : ∀ a b, to_fun (a ⟶ b) = to_fun a ⟶ to_fun b)
(map_and' : ∀ a b, to_fun (a ⊓ b) = to_fun a ⊓ to_fun b)
(map_or' : ∀ a b, to_fun (a ⊔ b) = to_fun a ⊔ to_fun b)
(map_top' : to_fun ⊤ = ⊤)
(map_bot' : to_fun ⊥ = ⊥)

infix ` →ₗ `:25 := homomorphism
#check homomorphism

instance : has_coe_to_fun (F →ₗ G) (λ _, F → G) := ⟨homomorphism.to_fun⟩

namespace homomorphism
variables {F} {G} (f g : F →ₗ G) (a b : F)

lemma eq_to_fun (a : F) : f a = f.to_fun a := rfl

@[ext] lemma ext (h : ∀ x, f x = g x) : f = g :=
by rcases f; rcases g; simp; funext x; by simpa using h x

@[simp] lemma map_neg : f (∼a) = ∼f a := map_neg' f a

@[simp] lemma map_imply : f (a ⟶ b) = f a ⟶ f b := map_imply' f a b

@[simp] lemma map_and : f (a ⊓ b) = f a ⊓ f b := map_and' f a b

@[simp] lemma map_or : f (a ⊔ b) = f a ⊔ f b := map_or' f a b

@[simp] lemma map_top : f ⊤ = ⊤ := map_top' f

@[simp] lemma map_bot : f ⊥ = ⊥ := map_bot' f

@[simp] lemma map_list_disjunction (P : list F) :
  f P.disjunction = (P.map f).disjunction :=
by induction P; simp*

@[simp] lemma map_list_conjunction (P : list F) :
  f P.conjunction = (P.map f).conjunction :=
by induction P; simp*

@[simp] lemma map_finitary_disjunction {n} (P : finitary F n) :
  f (finitary.disjunction n P) = ⋁ i, f (P i) :=
by induction n with n IH; simp*

@[simp] lemma map_finitary_conjunction {n} (P : finitary F n) :
  f (finitary.conjunction n P) = ⋀ i, f (P i) :=
by induction n with n IH; simp*

protected def id : F →ₗ F :=
{ to_fun := id,
  map_neg' := by simp,
  map_imply' := by simp,
  map_and' := by simp,
  map_or' := by simp,
  map_top' := by simp,
  map_bot' := by simp }

@[simp] lemma app_id (a : F) : homomorphism.id a = a := by refl

variables {F₁ : Type*} {F₂ : Type*} {F₃ : Type*}
  [has_logic_symbol F₁] [has_logic_symbol F₂] [has_logic_symbol F₃]
  (f₂ : F₂ →ₗ F₃) (f₁ : F₁ →ₗ F₂)

def comp : F₁ →ₗ F₃ :=
{ to_fun := f₂.to_fun ∘ f₁.to_fun,
  map_neg' := by simp[←eq_to_fun],
  map_imply' := by simp[←eq_to_fun],
  map_and' := by simp[←eq_to_fun],
  map_or' := by simp[←eq_to_fun],
  map_top' := by simp[←eq_to_fun],
  map_bot' := by simp[←eq_to_fun] }

@[simp] lemma app_comp (a) : (f₂.comp f₁) a = f₂ (f₁ a) :=
by simp[eq_to_fun, comp] 

end homomorphism

end

section

variables (F : ℕ → Type u) (G : ℕ → Type v)
  [∀ k, has_logic_symbol (F k)] [∀ k, has_logic_symbol (G k)]
  [has_univ_quantifier' F] [has_exists_quantifier' F]
  [has_univ_quantifier' G] [has_exists_quantifier' G]

structure homomorphism_q₁ :=
(to_fun (k) : F k → G k)
(map_neg' (k) : ∀ a, to_fun k (∼a) = ∼to_fun k a)
(map_imply' (k) : ∀ a b, to_fun k (a ⟶ b) = to_fun k a ⟶ to_fun k b)
(map_and' (k) : ∀ a b, to_fun k (a ⊓ b) = to_fun k a ⊓ to_fun k b)
(map_or' (k) : ∀ a b, to_fun k (a ⊔ b) = to_fun k a ⊔ to_fun k b)
(map_top' (k) : to_fun k ⊤ = ⊤)
(map_bot' (k) : to_fun k ⊥ = ⊥)
(map_fal' (k) : ∀ a, to_fun k (∀'a) = ∀'(to_fun (k + 1) a))

end
end logic