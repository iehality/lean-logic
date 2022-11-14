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

@[notation_class] class has_univ_quantifier' (α : ℕ → Sort*) := (univ : Π {n}, α (n + 1) → α n)

@[notation_class] class has_exists_quantifier' (α : ℕ → Sort*) := (ex : Π {n}, α (n + 1) → α n)

localized "infix (name := has_eq.eq) ` =' `:50 := has_eq.eq" in logic_symbol
localized "infix (name := has_prec.prec) ` ≺ `:50 := has_prec.prec" in logic_symbol
localized "infix (name := has_preceq.preceq) ` ≼ `:50 := has_preceq.preceq" in logic_symbol
localized "infix (name := has_elem.elem) ` ∊ `:50 := has_elem.elem" in logic_symbol
localized "prefix (name := has_negation.neg) `∼`:75 := has_negation.neg" in logic_symbol
localized "infixr (name := has_arrow.arrow) ` ⟶ `:60 := has_arrow.arrow" in logic_symbol
localized "prefix (name := has_univ_quantifier.univ) `∀.`:64 := has_univ_quantifier.univ" in logic_symbol
localized "prefix (name := has_exists_quantifier.ex) `∃.`:64 := has_exists_quantifier.ex" in logic_symbol
localized "prefix (name := has_univ_quantifier'.univ) `∀'`:64 := has_univ_quantifier'.univ" in logic_symbol
localized "prefix (name := has_exists_quantifier'.ex) `∃'`:64 := has_exists_quantifier'.ex" in logic_symbol

open_locale logic_symbol

section has_univ_quantifier'
variables  {α : ℕ → Sort*} [has_univ_quantifier' α]

def nforall {n} : Π (k), α (n + k) → α n
| 0     a := a
| (k+1) a := nforall _ ∀'a

@[simp] def universal_closure : Π {n}, α n → α 0
| 0     a := a
| (k+1) a := universal_closure ∀'a

localized "notation (name := universal_closure) `∀'*`:64 := universal_closure" in logic_symbol

end has_univ_quantifier'

section has_exists_quantifier'
variables {α : ℕ → Sort*} [has_exists_quantifier' α]

def nexists {n} : Π (k), α (n + k) → α n
| 0     a := a
| (k+1) a := nexists _ ∃'a

@[simp] def exists_close : Π {n}, α n → α 0
| 0     a := a
| (k+1) a := exists_close ∃'a

localized "notation (name := exists_close) `∃'*`:64 := exists_close" in logic_symbol

end has_exists_quantifier'

@[reducible] def has_eq.ineq {α : out_param (Sort*)} {β : Sort*}
  [has_eq α β] [has_negation β] (a b : α) : β := ∼(a =' b)

localized "infix (name := has_eq.ineq) ` ≠' `:50 := has_eq.ineq" in logic_symbol

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

section 
variables (F : Type*) (top : F) (neg : F → F) (imply : F → F → F)

def logic_simbol_default (F : Type*) (top : F) (neg : F → F) (imply : F → F → F) : has_logic_symbol F :=
{ bot := neg top,
  top := top,
  sup := λ p q, imply (neg p) q,
  inf := λ p q, neg (imply p (neg q)),
  arrow := imply,
  neg := neg }

lemma default_bot_def :
  @has_bot.bot F (@has_logic_symbol.to_has_bot F (logic_simbol_default F top neg imply)) =
  @has_negation.neg F (@has_logic_symbol.to_has_negation F (logic_simbol_default F top neg imply))
    (@has_top.top F (@has_logic_symbol.to_has_top F (logic_simbol_default F top neg imply))) := rfl

lemma default_top_def :
  @has_top.top F (@has_logic_symbol.to_has_top F (logic_simbol_default F top neg imply)) = top := rfl

lemma default_or_def (p q : F) :
  @has_sup.sup F (@has_logic_symbol.to_has_sup F (logic_simbol_default F top neg imply)) p q =
  @has_arrow.arrow F (@has_logic_symbol.to_has_arrow F (logic_simbol_default F top neg imply))
    (@has_negation.neg F (@has_logic_symbol.to_has_negation F (logic_simbol_default F top neg imply)) p) q := rfl

lemma default_and_def (p q : F) :
  @has_inf.inf F (@has_logic_symbol.to_has_inf F (logic_simbol_default F top neg imply)) p q =
  @has_negation.neg F (@has_logic_symbol.to_has_negation F (logic_simbol_default F top neg imply))
    (@has_arrow.arrow F (@has_logic_symbol.to_has_arrow F (logic_simbol_default F top neg imply))
      p (@has_negation.neg F (@has_logic_symbol.to_has_negation F (logic_simbol_default F top neg imply)) q)) := rfl

lemma default_imply_def (p q : F) :
  @has_arrow.arrow F (@has_logic_symbol.to_has_arrow F (logic_simbol_default F top neg imply)) p q = imply p q := rfl

lemma default_neg_def (p : F) :
  @has_negation.neg F (@has_logic_symbol.to_has_negation F (logic_simbol_default F top neg imply)) p = neg p := rfl

end 

