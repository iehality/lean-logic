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

@[notation_class] class has_prec (α : out_param (Sort*)) (β : Sort*) := (prec : α → α → β)

@[notation_class] class has_preceq (α : out_param (Sort*)) (β : Sort*) := (preceq : α → α → β)

@[notation_class] class has_elem (α : out_param (Sort*)) (β : Sort*) := (elem : α → α → β)

@[notation_class] class has_negation (α : Sort*) := (neg : α → α)

@[notation_class] class has_arrow (α : Sort*) := (arrow : α → α → α)

@[notation_class] class has_univ_quantifier (α : Sort*) := (univ : α → α)

@[notation_class] class has_exists_quantifier (α : Sort*) := (ex : α → α)

@[notation_class] class has_univ_quantifier' (α : Sort*) (β : Sort*):= (univ : α → β)

@[notation_class] class has_exists_quantifier' (α : Sort*) (β : Sort*) := (ex : α → β)

localized "infix (name := has_eq.eq) ` ≃ `:50 := has_eq.eq" in logic_symbol
localized "infix (name := has_prec.prec) ` ≺ `:50 := has_prec.prec" in logic_symbol
localized "infix (name := has_preceq.preceq) ` ≼ `:50 := has_preceq.preceq" in logic_symbol
localized "infix (name := has_elem.elem) ` ∊ `:50 := has_elem.elem" in logic_symbol
localized "prefix (name := has_negation.neg) `∼`:75 := has_negation.neg" in logic_symbol
localized "infixr (name := has_arrow.arrow) ` ⟶ `:60 := has_arrow.arrow" in logic_symbol
localized "prefix (name := has_univ_quantifier.univ) `∀. `:64 := has_univ_quantifier.univ" in logic_symbol
localized "prefix (name := has_exists_quantifier.ex) `∃. `:64 := has_exists_quantifier.ex" in logic_symbol
localized "prefix (name := has_univ_quantifier'.univ) `∀' `:64 := has_univ_quantifier'.univ" in logic_symbol
localized "prefix (name := has_exists_quantifier'.ex) `∃' `:64 := has_exists_quantifier'.ex" in logic_symbol

open_locale logic_symbol

@[reducible] def has_eq.ineq {α : out_param (Sort*)} {β : Sort*}
  [has_eq α β] [has_negation β] (a b : α) : β := ∼(a ≃ b)

localized "infix (name := has_eq.ineq) ` ≄ `:50 := has_eq.ineq" in logic_symbol

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

localized "infix (name := has_arrow.lrarrow) ` ⟷ `:59 := has_arrow.lrarrow" in logic_symbol

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
