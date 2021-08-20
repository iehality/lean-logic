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

#check @provable'.rec

@[elab_as_eliminator]
theorem provable.rec'
  {T : theory L} (C : ℕ → formula L → Prop)
  (GE : ∀ {i} {p : formula L} (b : T^(i + 1) ⊢ p), C (i + 1) p → C i (∀̇ p))
  (MP : ∀ {i} {p q : formula L} (b₁ : T^i ⊢ p →̇ q) (b₂ : T^i ⊢ p), C i (p →̇ q) → C i p → C i q)
  (AX : ∀ {i} {p : formula L} (mem : p ∈ T^i), C i p)
  (p1 : ∀ {i} {p q : formula L}, C i (p →̇ q →̇ p))
  (p2 : ∀ {i} {p q r : formula L}, C i ((p →̇ q →̇ r) →̇ (p →̇ q) →̇ p →̇ r))
  (p3 : ∀ {i} {p q : formula L}, C i ((¬̇p →̇ ¬̇q) →̇ q →̇ p))
  (q1 : ∀ {i} {p : formula L} {t : term L}, C i (∀̇ p →̇ p.rew ι[0 ⇝ t]))
  (q2 : ∀ {i} {p q : formula L}, C i (∀̇ (p →̇ q) →̇ ∀̇ p →̇∀̇ q))
  (q3 : ∀ {i} {p : formula L}, C i (p →̇ ∀̇ (p^1)))
  (e1 : ∀ {i} {t : term L}, C i (t =̇ t))
  (e2 : ∀ {i} {t₁ t₂ : term L}, C i (t₁ =̇ t₂ →̇ t₂ =̇ t₁))
  (e3 : ∀ {i} {t₁ t₂ t₃ : term L}, C i (t₁ =̇ t₂ →̇ t₂ =̇ t₃ →̇ t₁ =̇ t₃))
  (e4 : ∀ {i} {m} {f : L.fn (m + 1)} {v₁ v₂ : vecterm L m}, C i (v₁ ≡̇ v₂ →̇ vecterm.app f v₁ =̇ vecterm.app f v₂))
  (e5 : ∀ {i} {m} {r : L.pr (m + 1)} {v₁ v₂ : vecterm L m}, C i (v₁ ≡̇ v₂ →̇ formula.app r v₁ →̇ formula.app r v₂))
  : ∀ {i : ℕ} {p : formula L} (b : T^i ⊢ p), C i p :=
begin
  suffices :
    ∀ {p : formula L} {U : theory L} (b : U ⊢ p) {i : ℕ} (ss : U ⊆ T^i),  C i p,
  { intros i p b, refine this b (by refl) },
  intros p U b,
  induction b,
  case provable.GE : U p b IH
  { intros i ss,
  have ss' : ⇑U ⊆ T ^ (i + 1), { rintros _ ⟨q, mem, rfl⟩, simp[theory.sf_itr_succ], refine ⟨q, ss mem, rfl⟩ },
    have : C (i + 1) p, from @IH (i + 1) ss',
    refine GE (b.inclusion ss') this },
  case provable.MP : U p q b₁ b₂ IH₁ IH₂
  { intros i ss, refine MP (b₁.inclusion ss) (b₂.inclusion ss) (IH₁ ss) (IH₂ ss) },
  case provable.AX : U p mem
  { intros i ss, refine AX (ss mem) },
  { refine λ i ss, p1 },
  { refine λ i ss, p2 },
  { refine λ i ss, p3 },
  { refine λ i ss, q1 },
  { refine λ i ss, q2 },
  { refine λ i ss, q3 },
  { refine λ i ss, e1 },
  { refine λ i ss, e2 },
  { refine λ i ss, e3 },
  { refine λ i ss, e4 },
  { refine λ i ss, e5 }
end

@[elab_as_eliminator]
theorem provable.drec'
  {T : theory L} (C : Π (i : ℕ) (p : formula L), T^i ⊢ p → Prop)
  (GE : ∀ {i} {p : formula L} (b : T^(i + 1) ⊢ p), C (i + 1) p b → C i (∀̇ p) (provable.GE b))
  (MP : ∀ {i} {p q : formula L} (b₁ : T^i ⊢ p →̇ q) (b₂ : T^i ⊢ p), C i (p →̇ q) b₁ → C i p b₂ → C i q (b₁.MP b₂))
  (AX : ∀ {i} {p : formula L} (mem : p ∈ T^i), C i p (provable.AX mem))
  (p1 : ∀ {i} {p q : formula L}, C i (p →̇ q →̇ p) provable.p1)
  (p2 : ∀ {i} {p q r : formula L}, C i ((p →̇ q →̇ r) →̇ (p →̇ q) →̇ p →̇ r) provable.p2)
  (p3 : ∀ {i} {p q : formula L}, C i ((¬̇p →̇ ¬̇q) →̇ q →̇ p) provable.p3)
  (q1 : ∀ {i} {p : formula L} {t : term L}, C i (∀̇ p →̇ p.rew ι[0 ⇝ t]) provable.q1)
  (q2 : ∀ {i} {p q : formula L}, C i (∀̇ (p →̇ q) →̇ ∀̇ p →̇∀̇ q) provable.q2)
  (q3 : ∀ {i} {p : formula L}, C i (p →̇ ∀̇ (p^1)) provable.q3)
  (e1 : ∀ {i} {t : term L}, C i (t =̇ t) provable.e1)
  (e2 : ∀ {i} {t₁ t₂ : term L}, C i (t₁ =̇ t₂ →̇ t₂ =̇ t₁) provable.e2)
  (e3 : ∀ {i} {t₁ t₂ t₃ : term L}, C i (t₁ =̇ t₂ →̇ t₂ =̇ t₃ →̇ t₁ =̇ t₃) provable.e3)
  (e4 : ∀ {i} {m} {f : L.fn (m + 1)} {v₁ v₂ : vecterm L m}, C i (v₁ ≡̇ v₂ →̇ vecterm.app f v₁ =̇ vecterm.app f v₂) provable.e4)
  (e5 : ∀ {i} {m} {r : L.pr (m + 1)} {v₁ v₂ : vecterm L m}, C i (v₁ ≡̇ v₂ →̇ formula.app r v₁ →̇ formula.app r v₂) provable.e5)
  : ∀ {i : ℕ} {p : formula L} (b : T^i ⊢ p), C i p b :=
begin
  suffices :
    ∀ {p : formula L} {U : theory L} (b : U ⊢ p) {i : ℕ} (ss : U ⊆ T^i),  C i p (provable.inclusion b ss),
  { intros i p b, refine this b (by refl) },
  intros p U b,
  induction b,
  case provable.GE : U p _ IH
  { intros i ss,
    have : C (i + 1) p _, from @IH (i + 1)
    (by { rintros _ ⟨q, mem, rfl⟩, simp[theory.sf_itr_succ], refine ⟨q, ss mem, rfl⟩ }),
    refine GE _ this },
  case provable.MP : U p q _ _ IH₁ IH₂
  { intros i ss, refine MP _ _ (IH₁ ss) (IH₂ ss) },
  case provable.AX : U p mem
  { intros i ss, refine AX (ss mem) },
  { refine λ i ss, p1 },
  { refine λ i ss, p2 },
  { refine λ i ss, p3 },
  { refine λ i ss, q1 },
  { refine λ i ss, q2 },
  { refine λ i ss, q3 },
  { refine λ i ss, e1 },
  { refine λ i ss, e2 },
  { refine λ i ss, e3 },
  { refine λ i ss, e4 },
  { refine λ i ss, e5 }
end




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