import logic

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

@[simp] lemma map_iff : f (a ⟷ b) = f a ⟷ f b := by simp[lrarrow_def]

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

variables (F G)

class iso :=
(to_fun : F →ₗ G)
(inv_fun : G →ₗ F)
(left_inv : function.left_inverse inv_fun to_fun)
(right_inv : function.right_inverse inv_fun to_fun)

namespace iso
variables {F G} [iso F G] {a a₁ a₂ a₃ : F} {b b₁ b₂ b₃ : G}

instance coe : has_coe F G := ⟨to_fun⟩

instance inv_coe : has_coe G F := ⟨inv_fun⟩

@[simp] lemma to_fun_inv_fun : ((a : G) : F) = a := left_inv a

@[simp] lemma inv_fun_to_fun : ((b : F) : G) = b := right_inv b

lemma coe_to_fun (a : F) : (a : G) = to_fun a := rfl

lemma coe_inv_fun (b : G) : (b : F) = inv_fun b := rfl

@[simp] lemma coe_neg : (↑(∼a) : G) = ∼(a : G) := by simp[coe_to_fun]

@[simp] lemma inv_coe_neg : (↑(∼b) : F) = ∼(b : F) := by simp[coe_inv_fun]

end iso

variables {Ω : Type u} (Φ : Ω → Type v) [∀ L, has_logic_symbol (Φ L)] [∀ L, axiomatic_classical_logic (Φ L)]

structure system :=
(language : Ω)
(theory : Theory (Φ language))

class system_has_le :=
(language_translation {} : Ω → Ω → Type*)
(sentence_translation : Π {L₁ L₂ : Ω}, language_translation L₁ L₂ → (Φ L₁ →ₗ Φ L₂))
(provability_translation : Π {L₁ L₂ : Ω} {l : language_translation L₁ L₂} {T : Theory (Φ L₁)} {p : Φ L₁},  
  T ⊢ p → sentence_translation l '' T ⊢ sentence_translation l p)

namespace system
open system_has_le
variables {Φ} [system_has_le Φ] (S₁ S₂ : system Φ)

structure le :=
(tr : language_translation Φ S₁.language S₂.language)
(h : ∀ p ∈ S₁.theory, S₂.theory ⊢ sentence_translation tr p) 

end system

end logic