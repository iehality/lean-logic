import tactic

universes u

@[notation_class] class has_succ (α : Sort*) := (succ : α → α)

prefix `Succ `:85 := has_succ.succ

def numeral {α : Type*} [has_zero α] [has_succ α] : ℕ → α
| 0       := 0
| (n + 1) := Succ (numeral n)

instance numeral_has_one {α : Type*} [has_zero α] [has_succ α] : has_one α := ⟨Succ 0⟩

lemma numeral_one_def  {α : Type*} [has_zero α] [has_succ α] : (1 : α) = Succ 0 := rfl 

@[notation_class] class has_eq (α : out_param (Sort*)) (β : Sort*) := (eq : α → α → β)

infix ` ≃ `:50 := has_eq.eq

@[notation_class] class has_preceq (α : out_param (Sort*)) (β : Sort*) := (preceq : α → α → β)

infix ` ≼ `:50 := has_preceq.preceq

@[notation_class] class has_elem (α : out_param (Sort*)) (β : Sort*) := (elem : α → α → β)

infix ` ∊ `:50 := has_elem.elem

@[notation_class] class has_negation (α : Sort*) := (neg : α → α)

prefix `⁻`:75 := has_negation.neg

@[reducible] def has_eq.ineq {α : out_param (Sort*)} {β : Sort*} [has_eq α β] [has_negation β] (a b : α) : β := ⁻(a ≃ b)

infix ` ≄ `:50 := has_eq.ineq

@[notation_class] class has_arrow (α : Sort*) := (arrow : α → α → α)

infixr ` ⟶ `:60 := has_arrow.arrow

@[notation_class] class has_lrarrow (α : Sort*) := (lrarrow : α → α → α)

@[notation_class] class has_univ_quantifier (α : Sort*) := (univ : α → α)

prefix `∏ `:64 := has_univ_quantifier.univ

@[notation_class] class has_exists_quantifier (α : Sort*) := (ex : α → α)

prefix `∐ `:64 := has_exists_quantifier.ex

@[notation_class] class has_univ_quantifier' (α : Sort*) (β : Sort*):= (univ : α → β)

prefix `∏' `:64 := has_univ_quantifier'.univ

@[notation_class] class has_exists_quantifier' (α : Sort*) (β : Sort*) := (ex : α → β)

prefix `∐' `:64 := has_exists_quantifier'.ex

@[notation_class] class has_turnstile (α : Sort*) := (turnstile : set α → α → Prop)

infix ` ⊢ `:45 := has_turnstile.turnstile
notation T ` ⊢{`:45 β `} `:45 p := has_turnstile.turnstile T β p

namespace has_turnstile
variables {α : Type*} [has_turnstile α]

def turnstile_set (T : set α) (Γ : set α) : Prop := ∀ p ∈ Γ, T ⊢ p

infix ` ⊢* `:45 := turnstile_set

end has_turnstile

@[notation_class] class has_Longarrow (α : Sort*) := (Longarrow : set α → α → Type u)

infix ` ⟹ `:45 := has_Longarrow.Longarrow

def has_arrow.lrarrow {α : Type*} [has_arrow α] [has_inf α] (a b : α) : α := (a ⟶ b) ⊓ (b ⟶ a)

infix ` ⟷ `:59 := has_arrow.lrarrow

lemma lrarrow_def {α : Type*} [has_arrow α] [has_inf α] (a b : α) : a ⟷ b = (a ⟶ b) ⊓ (b ⟶ a) := rfl

@[notation_class] class has_double_turnstile (α : Sort*) (β : Sort*) := (double_turnstile : α → β → Prop)

infix ` ⊧ ` :55 := has_double_turnstile.double_turnstile

namespace has_double_turnstile
variables {α : Type*} {β : Type*} [has_double_turnstile α β]

def double_turnstile_set (T : α) (S : set β) : Prop := ∀ p ∈ S, T ⊧ p

infix ` ⊧* `:45 := double_turnstile_set

end has_double_turnstile

class has_logic_symbol (F : Sort*)
  extends has_negation F, has_arrow F, has_inf F, has_sup F, has_top F, has_bot F

