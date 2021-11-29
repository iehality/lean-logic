import deduction semantics lindenbaum
open encodable

namespace fopl
variables {L : language.{0}} 

local infix ` ≃₁ `:80 := ((≃) : term L → term L → formula L)
local prefix `∏₁ `:64 := (has_univ_quantifier.univ : formula L → formula L)
local prefix `∐₁ `:64 := (has_exists_quantifier.ex : formula L → formula L)

variables [primcodable (formula L)] [decidable_eq (formula L)]

@[simp] def formula.arrow : formula L → option (formula L × formula L)
| (p ⟶ q) := some (p, q)
| _        := none

lemma arrow_eq {p : formula L} {v} : p.arrow = some v → p = v.1 ⟶ v.2 :=
by { cases p; simp[show ∀ x y : term L, (x ≃ y : formula L).arrow = none, from λ _ _, rfl,
      show ∀ p : formula L, (⁻p).arrow = none, from λ _, rfl,
      show ∀ p : formula L, (∏ p : formula L).arrow = none, from λ _, rfl], rintros rfl, simp* }

inductive proof (L : language.{0}) : ℕ → Type
| root {n} : formula L → proof n
| ge {n} : proof (n + 1)  → proof n
| mp {n} : proof n → proof n → proof n

#check (>>)

@[simp] def proof.conseq : ∀ {n}, proof L n → option (formula L)
| n (proof.root p) := some p
| n (proof.ge φ)   := φ.conseq.map (λ p, ∏ p)
| n (proof.mp φ ψ) :=
    if (φ.conseq >>= formula.arrow).map prod.fst = ψ.conseq then (φ.conseq >>= formula.arrow).map prod.snd 
    else ψ.conseq

inductive formula.is_axiom (T : theory L) (i : ℕ) : formula L → Prop
| p1 {p q} : formula.is_axiom (p ⟶ q ⟶ p)
| p2 {p q r} : formula.is_axiom ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r)
| p3 {p q} : formula.is_axiom ((⁻p ⟶ ⁻q) ⟶ q ⟶ p)
| q1 {p t} : formula.is_axiom (∏₁ p ⟶ p.rew ι[0 ⇝ t])
| q2 {p q} : formula.is_axiom (∏₁ (p ⟶ q) ⟶ ∏₁ p ⟶ ∏₁ q)
| q3 {p} : formula.is_axiom (p ⟶ ∏₁ (p^1))
| e1 : formula.is_axiom ∏₁ #0 ≃₁ #0
| e2 : formula.is_axiom ∏₁ ∏₁ (#0 ≃₁ #1 ⟶ #1 ≃₁ #0)
| e3 : formula.is_axiom ∏₁ ∏₁ ∏₁ (#0 ≃₁ #1 ⟶ #1 ≃₁ #2 ⟶ #0 ≃₁ #2)
| e4 {n} {f : L.fn n} : formula.is_axiom (eq_axiom4 f)
| e5 {n} {r : L.pr n} : formula.is_axiom (eq_axiom5 r)
| by_axiom {p} : p ∈ T^i → formula.is_axiom p

@[simp] def proof.proper : ∀ (T : theory L) {i}, proof L i → Prop
| T i (proof.root p) := p.is_axiom T i
| T i (proof.ge φ)   := φ.proper T
| T i (proof.mp φ ψ) := (φ.proper T) ∧ (ψ.proper T) 

def proof.of (T : theory L) (p : formula L) (i : ℕ) (φ : proof L i) : Prop := φ.proper T ∧ φ.conseq = some p

#check provable.rec'

variables {T : theory L} {i : ℕ}

lemma provable_of_is_axiom {p} (h : is_axiom T i p) : T^i ⊢ p :=
begin
  cases h; try {simp}, { exact provable.e4 }, { exact provable.e5 },
  { exact provable.AX (by simp*) }
end

lemma proof.sound {T : theory L} {i} {p} {φ} : proof.of T p i φ → T^i ⊢ p :=
begin
  induction φ generalizing p; simp[proof.of],
  case root : i p { rintros h rfl, exact provable_of_is_axiom h },
  case ge : i φ IH { rintros proper ψ conseq rfl, exact provable.generalize (IH ⟨proper, conseq⟩) },
  case mp : i φ ψ IHφ IHψ
    { cases φ_conseq : φ.conseq with cφ; cases ψ_conseq : ψ.conseq with cψ; simp[φ_conseq, ψ_conseq], 
      { rintros pφ pψ rfl, exact IHψ ⟨pψ, ψ_conseq⟩ },
      { intros pφ pψ, simp[show (∀ (a b a_1 : formula L), cφ = a_1 → ¬a_1.arrow = some (a, b)) ↔ cφ.arrow = none,
          from ⟨λ h, by { cases C : cφ.arrow with v; simp, exact h v.1 v.2 cφ rfl (by simp[C]) },
           by { rintros h a b _ rfl, simp[h] }⟩],
        cases C : cφ.arrow with v; simp[C] },
      { rintros pφ pψ, cases C : cφ.arrow with v; simp, { rintros rfl, exact IHψ ⟨pψ, ψ_conseq⟩ },
        { by_cases C₂ : v.1 = cψ,
          { simp[←C₂, show ∃ a, v = (v.fst, a), from ⟨v.2, by simp⟩], 
            rintros rfl, rcases C₂ with rfl, rcases arrow_eq C with rfl, 
            exact classical_logic.modus_ponens (IHφ ⟨pφ, φ_conseq⟩) (IHψ ⟨pψ, ψ_conseq⟩) },
          { simp[show ¬∃ (a : formula L), v = (cψ, a), by { simp, rintros s rfl, simp at C₂, contradiction }],
            rintros rfl, exact IHψ ⟨pψ, ψ_conseq⟩ } } } }
end

lemma proof.complete (T : theory L) {i} (p : formula L) : T^i ⊢ p ↔ ∃ φ, proof.of T p i φ :=
⟨λ h,
begin
  apply fopl.provable.rec_on' h,
  { rintros i p _ ⟨φ, φ_proper, φ_conseq⟩, refine ⟨φ.ge, _, _⟩; simp* },
  { rintros i p q _ _ ⟨φ, φ_proper, φ_conseq⟩ ⟨ψ, ψ_proper, ψ_conseq⟩,
    refine ⟨φ.mp ψ, _, _⟩; simp[*, (>>=)] },
  { intros i p _, refine ⟨proof.root p, _, _⟩; simp, exact formula.is_axiom.by_axiom mem },
  { intros i p q, refine ⟨proof.root (p ⟶ q ⟶ p), _, _⟩; simp, exact formula.is_axiom.p1 },
  { intros i p q r, refine ⟨proof.root ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r), _, _⟩; simp, exact formula.is_axiom.p2 },
  { intros i p q, refine ⟨proof.root ((⁻p ⟶ ⁻q) ⟶ q ⟶ p), _, _⟩; simp, exact formula.is_axiom.p3 },
  { intros i p t, refine ⟨proof.root (∏ p ⟶ formula.rew ι[0 ⇝ t] p), _, _⟩; simp, exact formula.is_axiom.q1 },
  { intros i p q, refine ⟨proof.root (∏ (p ⟶ q) ⟶ ∏ p ⟶ ∏ q), _, _⟩; simp, exact formula.is_axiom.q2 },
  { intros i p, refine ⟨proof.root (p ⟶ ∏ p ^ 1), _, _⟩; simp, exact formula.is_axiom.q3 },
  { intros i, refine ⟨proof.root (∏₁ #0 ≃₁ #0), _, _⟩; simp, exact formula.is_axiom.e1 },
  { intros i, refine ⟨proof.root (∏₁ ∏₁ (#0 ≃₁ #1 ⟶ #1 ≃₁ #0)), _, _⟩; simp, exact formula.is_axiom.e2 },
  { intros i, refine ⟨proof.root (∏₁ ∏₁ ∏₁ (#0 ≃₁ #1 ⟶ #1 ≃₁ #2 ⟶ #0 ≃₁ #2)), _, _⟩; simp, exact formula.is_axiom.e3 },
  { intros i m f, refine ⟨proof.root (eq_axiom4 f), _, _⟩; simp, exact formula.is_axiom.e4 },
  { intros i m p, refine ⟨proof.root (eq_axiom5 p), _, _⟩; simp, exact formula.is_axiom.e5 }
end, λ ⟨φ, h⟩, proof.sound h⟩


end fopl