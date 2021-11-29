import deduction semantics lindenbaum
open encodable

namespace fopl
variables {L : language.{0}} 

local infix ` ≃₁ `:80 := ((≃) : term L → term L → formula L)
local prefix `∏₁ `:64 := (has_univ_quantifier.univ : formula L → formula L)
local prefix `∐₁ `:64 := (has_exists_quantifier.ex : formula L → formula L)

variables [decidable_eq (formula L)]

@[simp] def formula.arrow : formula L → option (formula L × formula L)
| (p ⟶ q) := some (p, q)
| _        := none

lemma arrow_eq {p : formula L} {v} : p.arrow = some v → p = v.1 ⟶ v.2 :=
by { cases p; simp[show ∀ x y : term L, (x ≃ y : formula L).arrow = none, from λ _ _, rfl,
      show ∀ p : formula L, (⁻p).arrow = none, from λ _, rfl,
      show ∀ p : formula L, (∏ p : formula L).arrow = none, from λ _, rfl], rintros rfl, simp* }

inductive proof (L : language.{0}) : Type
| root : formula L → proof
| ge : proof → proof
| mp : proof → proof → proof

@[simp] def proof.conseq : proof L → option (formula L)
| (proof.root p) := some p
| (proof.ge φ)   := φ.conseq.map (λ p, ∏ p)
| (proof.mp φ ψ) :=
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

@[simp] def proof.proper (T : theory L) : ℕ → proof L → Prop
| i (proof.root p) := p.is_axiom T i
| i (proof.ge φ)   := φ.proper (i + 1)
| i (proof.mp φ ψ) := (φ.proper i) ∧ (ψ.proper i) 

def proof.of (T : theory L) (i : ℕ) (p : formula L) (φ : proof L) : Prop := φ.proper T i ∧ φ.conseq = some p

variables {T : theory L} {i : ℕ}

lemma provable_of_is_axiom {p} (h : is_axiom T i p) : T^i ⊢ p :=
begin
  cases h; try {simp}, { exact provable.e4 }, { exact provable.e5 },
  { exact provable.AX (by simp*) }
end

lemma proof.sound {T : theory L} {i} {p} {φ} : proof.of T i p φ → T^i ⊢ p :=
begin
  induction φ generalizing p i; simp[proof.of],
  case root : i p { rintros h rfl, exact provable_of_is_axiom h },
  case ge : φ IH p { rintros proper q conseq rfl, exact provable.generalize (IH ⟨proper, conseq⟩) },
  case mp : φ ψ IHφ IHψ
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

lemma proof.complete (T : theory L) {i} (p : formula L) : T^i ⊢ p ↔ ∃ φ, proof.of T i p φ :=
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


namespace proof
open nat

variables [primcodable (formula L)]

def encode_pcode : proof L → ℕ
| (root p) := bit0 $ encode p
| (ge φ)   := bit1 $ bit0 $ encode_pcode φ
| (mp φ ψ) := bit1 $ bit1 $ nat.mkpair (encode_pcode φ) (encode_pcode φ)

def of_nat_pcode : ℕ → option (proof L)
| n :=
match n.bodd, n.div2.bodd with
| ff, _  := (decode (formula L) n).map root
| tt, ff := by {  }
| tt, tt := by {  } 
end

end proof

end fopl