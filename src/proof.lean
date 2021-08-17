import deduction semantics lindenbaum
open encodable

namespace fopl
variables {L : language.{0}} 

inductive proof : ℕ → formula L → Type
| p1 : ∀ {n} p q, proof n (p →̇ q →̇ p)
| p2 : ∀ {n} p q r, proof n ((p →̇ q →̇ r) →̇ (p →̇ q) →̇ p →̇ r)
| p3 : ∀ {n} p q, proof n ((¬̇p →̇ ¬̇q) →̇ q →̇ p)
| q1 : ∀ {n} p t, proof n (∀̇ p →̇ p.rew ι[0 ⇝ t])
| q2 : ∀ {n} p q, proof n (∀̇ (p →̇ q) →̇ ∀̇ p →̇∀̇ q)
| q3 : ∀ {n} p, proof n (p →̇ ∀̇ (p^1))
| e1 : ∀ {n} t, proof n (t =̇ t)
| e2 : ∀ {n} t₁ t₂, proof n (t₁ =̇ t₂ →̇ t₂ =̇ t₁)
| e3 : ∀ {n} t₁ t₂ t₃, proof n (t₁ =̇ t₂ →̇ t₂ =̇ t₃ →̇ t₁ =̇ t₃)
| e4 : ∀ {n m} f (v₁ v₂ : vecterm L m), proof n (v₁ ≡̇ v₂ →̇ vecterm.app f v₁ =̇ vecterm.app f v₂)
| e5 : ∀ {n m} r (v₁ v₂ : vecterm L m), proof n (v₁ ≡̇ v₂ →̇ formula.app r v₁ →̇ formula.app r v₂)
| GE : ∀ {n p}, proof (n + 1) p → proof n (∀̇ p)
| MP : ∀ {n p q}, proof n (p →̇ q) → proof n p → proof n q
| AX : ∀ {n} p, proof n p

variables [primcodable (formula L)] 

@[simp] def proof.wellformed (T : theory L) [prm : ∀ i : ℕ, primrec_theory (T^i)] :
  ∀ {n} {p : formula L}, proof n p → bool
| _ _ (proof.p1 _ _)       := true
| _ _ (proof.p2 _ _ _)     := true
| _ _ (proof.p3 _ _)       := true
| _ _ (proof.q1 _ _)       := true
| _ _ (proof.q2 _ _)       := true
| _ _ (proof.q3 _)         := true
| _ _ (proof.e1 _)         := true
| _ _ (proof.e2 _ _)       := true
| _ _ (proof.e3 _ _ _)     := true
| _ _ (proof.e4 _ _ _)     := true
| _ _ (proof.e5 _ _ _)     := true
| _ _ (proof.GE b)         := b.wellformed
| _ _ (proof.MP b₁ b₂)     := b₁.wellformed && b₂.wellformed
| n _ (proof.AX q)         := @primrec_theory.isaxiom _ _ (T^n) (prm n) q

variables [primcodable (formula L)] (T : theory L) [∀ i : ℕ, primrec_theory (T^i)] 

lemma proof_soundness (n : ℕ) (p : formula L) (b : proof n p) : b.wellformed T → T^n ⊢ p :=
begin
  induction b; try { simp [proof.wellformed] },
  case proof.GE : n p b IH { intros h, refine provable.GE (IH h) },
  case proof.MP : n p q b₁ b₂ IH₁ IH₂ { intros h₁ h₂, refine provable.MP (IH₁ h₁) (IH₂ h₂) },
  case proof.AX : n p { intros h, refine provable.AX h }
end

def proof.encode : ∀ {n} {p : formula L}, proof n p → ℕ
| n p (proof.GE b)         := bit0 $ bit0 b.encode
| n p (proof.MP b₁ b₂) := bit0 $ bit1 (b₁.encode.mkpair b₂.encode)
| n p (proof.AX q)           := bit1 $ bit1 (encode q)

inductive provable' (T : theory L) : ℕ → formula L → Prop
| GE : ∀ {n p}, provable' (n + 1) p → provable' n (∀̇ p)
| MP : ∀ {n p q}, provable' n (p →̇ q) → provable' n p → provable' n q
| AX : ∀ {n p}, p ∈ T → provable' n (p^n)
| p1 : ∀ {n p q}, provable' n (p →̇ q →̇ p)
| p2 : ∀ {n p q r}, provable' n ((p →̇ q →̇ r) →̇ (p →̇ q) →̇ p →̇ r)
| p3 : ∀ {n p q}, provable' n ((¬̇p →̇ ¬̇q) →̇ q →̇ p)
| q1 : ∀ {n p t}, provable' n (∀̇ p →̇ p.rew ι[0 ⇝ t])
| q2 : ∀ {n p q}, provable' n (∀̇ (p →̇ q) →̇ ∀̇ p →̇∀̇ q)
| q3 : ∀ {n p}, provable' n (p →̇ ∀̇ (p^1))
| e1 : ∀ {n t}, provable' n (t =̇ t)
| e2 : ∀ {n t₁ t₂}, provable' n (t₁ =̇ t₂ →̇ t₂ =̇ t₁)
| e3 : ∀ {n t₁ t₂ t₃}, provable' n (t₁ =̇ t₂ →̇ t₂ =̇ t₃ →̇ t₁ =̇ t₃)
| e4 : ∀ {n m} {v₁ v₂ : vecterm L m} {f : L.fn (m+1)},
    provable' n (v₁ ≡̇ v₂ →̇ vecterm.app f v₁ =̇ vecterm.app f v₂)
| e5 : ∀ {n m} {v₁ v₂ : vecterm L m} {r : L.pr (m+1)},
    provable' n (v₁ ≡̇ v₂ →̇ formula.app r v₁ →̇ formula.app r v₂)

lemma proof_completeness (p : formula L) (n : ℕ) : provable' T n p → ∃ (b : proof n p), b.wellformed T = tt :=
begin
  intros h,
  induction h generalizing,
  case provable'.GE : n p h_p IH { rcases IH with ⟨b, eqn⟩, refine ⟨proof.GE b, by simp[eqn]⟩ },
  case provable'.MP : n p q h₁ h₂ IH₁ IH₂
  { rcases IH₁ with ⟨b₁, eqn₁⟩,
    rcases IH₂ with ⟨b₂, eqn₂⟩,
    refine ⟨proof.MP b₁ b₂, by simp[eqn₁, eqn₂]⟩ },
  case provable'.AX : n p h { refine ⟨proof.AX (p^n), _⟩, simp, sorry },

end
end fopl