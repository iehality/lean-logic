import deduction

namespace fopl

inductive langf : ℕ → Type
| zero : langf 0
| succ : langf 1
| add  : langf 2
| mult : langf 2

inductive langp : ℕ → Type
| le : langp 2

def AL : language := ⟨langf, langp⟩

def symbol.zero : term AL := vecterm.app langf.zero vecterm.nil

notation `Ż` := symbol.zero

def symbol.succ : term AL → term AL := λ x, vecterm.app langf.succ x

prefix `Ṡ `:max := symbol.succ

def symbol.add : term AL → term AL → term AL := λ x y, vecterm.app langf.add (vecterm.cons x y)

infixl ` +̇ `:92 := symbol.add 

def symbol.mult : term AL → term AL → term AL := λ x y, vecterm.app langf.mult (vecterm.cons x y)

infixl ` ×̇ `:94 := symbol.mult

def symbol.le : term AL → term AL → form AL := λ x y, form.app langp.le (vecterm.cons x y)

infixl ` ≤̇ `:90 := symbol.le

def numeral : ℕ → term AL
| 0     := Ż
| (n+1) := Ṡ (numeral n)

local notation n`˙`:max := numeral n

def bounded_fal (t : term AL) (p : form AL) : form AL := Ȧ(#0 ≤̇ t.sf →̇ p)

notation `[Ȧ`` ≤ `t`]`p := bounded_fal t p

def bounded_ext (t : term AL) (p : form AL) := Ė(#0 ≤̇ t.sf ⩑ p)

notation `[Ė`` ≤ `t`]`p := bounded_ext t p

#check [Ė ≤ #2][Ȧ ≤ #3]Ė[Ȧ ≤ #3](#1 ≤̇ #2)

inductive robinson : theory AL
| q1 : robinson Ȧ(Ż ≠̇ Ṡ #0)
| q2 : robinson ȦȦ(Ṡ #0 =̇ Ṡ #1 →̇ #0 =̇ #1)
| q3 : robinson Ȧ(#0 ≠̇ Ż →̇ Ė(#1 =̇ Ṡ #0))
| q4 : robinson Ȧ(Ż +̇ #0 =̇ #0)
| q5 : robinson ȦȦ(Ṡ #0 +̇ #1 =̇ Ṡ(#0 +̇ #1))
| q6 : robinson Ȧ(Ż ×̇ #0 =̇ Ż)
| q7 : robinson ȦȦ(Ṡ #0 ×̇ #1 =̇ #0 ×̇ #1 +̇ #1)
| q8 : robinson ȦȦ(#0 ≤̇ #1 ↔̇ Ė(#1 +̇ #0 =̇ #2))

notation `𝐐` := robinson
  
inductive peano : theory AL
| q   : ∀ {p}, 𝐐 p → peano p
| ind : ∀ (p : form AL), peano (p.(Ż) →̇ Ȧ(p →̇ (p.ᵉ(Ṡ #0))) →̇ Ȧ p)

notation `𝐏𝐀` := peano

inductive bounded_peano (C : set (form AL)) : theory AL
| q   : ∀ {p}, 𝐐 p → bounded_peano p
| ind : ∀ {p : form AL}, p ∈ C → bounded_peano (p.(Ż) →̇ Ȧ(p →̇ (p.ᵉ(Ṡ #0))) →̇ Ȧ p)

mutual inductive sigma, pie
with sigma : ℕ → form AL → Prop
| op : ∀ {p : form AL}, p.op → sigma 0 p
| bd_fal : ∀ {p} {n t}, sigma n p → sigma n [Ȧ ≤ t]p
| bd_ext : ∀ {p} {n t}, sigma n p → sigma n [Ė ≤ t]p
| qt : ∀ {p} {n}, pie n p → sigma (n+1) Ėp 
with pie : ℕ → form AL → Prop
| op : ∀ {p : form AL}, p.op → pie 0 p
| bd_fal : ∀ {p} {n t}, pie n p → pie n [Ȧ ≤ t]p
| bd_ext : ∀ {p} {n t}, pie n p → pie n [Ė ≤ t]p
| qt : ∀ {p} {n}, sigma n p → pie (n+1) Ȧp 



end fopl
