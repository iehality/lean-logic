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

prefix `Ṡ`:max := AL.symbolf₁ langf.succ

infixl ` +̇ `:92 := AL.symbolf₂ langf.add

infixl ` ×̇ `:92 := AL.symbolf₂ langf.mult

infixl ` ≤̇ `:90 := (AL.symbolp₂ langp.le)

def numeral : ℕ → AL.term
| 0     := Ż
| (n+1) := Ṡ(numeral n)

local prefix `˙`:max := numeral

inductive Q : AL.theory
| ax1 : Q Ȧ(˙0 ≠̇ #0)
| ax2 : Q ȦȦ(Ṡ #0 =̇ Ṡ #1 →̇ #0 =̇ #1)
| ax3 : Q Ȧ(#0 ≠̇ ˙0 →̇ Ė(#1 =̇ Ṡ #0))
| ax4 : Q Ȧ(˙0 +̇ #0 =̇ #0)
| ax5 : Q ȦȦ((Ṡ #0) +̇ #1 =̇ Ṡ(#0 +̇ #1))
| ax6 : Q Ȧ(˙0 ×̇ #0 =̇ ˙0)
| ax7 : Q ȦȦ((Ṡ #0) ×̇ #1 =̇ (#0 +̇ #1) +̇ #1)
| ax8 : Q ȦȦ(#0 ≤̇ #1 →̇ Ė(#1 +̇ #0 =̇ #2))


#reduce ˙2 +̇ ˙3

#check AL.symbolp₂ langp.le

#check (AL.symbolp₂ langp.le)