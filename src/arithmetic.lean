import deduction

open language

inductive langf : ℕ → Type
| zero : langf 0
| succ : langf 1
| add  : langf 2
| mult : langf 2

inductive langp : ℕ → Type
| le : langp 2

def AL : language := ⟨langf, langp⟩

notation `Ż` := AL.symbolf₀ langf.zero

prefix `Ṡ `:max := AL.symbolf₁ langf.succ

infixl ` +̇ `:92 := AL.symbolf₂ langf.add

infixl ` ×̇ `:94 := AL.symbolf₂ langf.mult

infixl ` ≤̇ `:90 := (AL.symbolp₂ langp.le)

def numeral : ℕ → AL.term
| 0     := Ż
| (n+1) := Ṡ (numeral n)

local prefix `˙`:max := numeral

inductive robinson : AL.theory
| q1 : robinson Ȧ(Ż ≠̇ Ṡ #0)
| q2 : robinson ȦȦ(Ṡ #0 =̇ Ṡ #1 →̇ #0 =̇ #1)
| q3 : robinson Ȧ(#0 ≠̇ Ż →̇ Ė(#1 =̇ Ṡ #0))
| q4 : robinson Ȧ(Ż +̇ #0 =̇ #0)
| q5 : robinson ȦȦ(Ṡ #0 +̇ #1 =̇ Ṡ(#0 +̇ #1))
| q6 : robinson Ȧ(Ż ×̇ #0 =̇ Ż)
| q7 : robinson ȦȦ(Ṡ #0 ×̇ #1 =̇ #0 ×̇ #1 +̇ #1)
| q8 : robinson ȦȦ(#0 ≤̇ #1 ↔̇ Ė(#1 +̇ #0 =̇ #2))

notation `𝐐` := robinson
  
inductive peano : AL.theory
| q   : ∀ {p}, 𝐐 p → peano p
| ind : ∀ (p : AL.form), peano (pˢ(Ż) →̇ Ȧ(p →̇ pᵉ(Ṡ #0)) →̇ Ȧ p)

notation `𝐏𝐀` := peano

