import fopl

universe u

namespace language
variables {L : language.{u}}

def theory (L : language) := L.form → Prop

inductive theory.sf (T : L.theory) : L.theory
| intro : ∀ {p : L.form}, T p → theory.sf p.sf

prefix `⇑`:max := theory.sf

inductive provable : L.theory → L.form → Prop
| gen : ∀ {T : theory L} {p}, provable (⇑T) p → provable T (Ȧp)
| mp  : ∀ {T : theory L} {p q}, provable T (p →̇ q) → provable T p → provable T q
| ax  : ∀ {T : theory L} {p}, T p → provable T p
| p1  : ∀ (T : theory L) (p q), provable T (p →̇ q →̇ p)
| p2  : ∀ (T : theory L) (p q r), provable T ((p →̇ q →̇ r) →̇ (p →̇ q) →̇ p →̇ r)
| p3  : ∀ (T : theory L) (p q), provable T ((¬̇ p →̇ ¬̇ q) →̇ q →̇ p)
| q1  : ∀ (T : theory L) (p t), provable T (Ȧ p →̇ p.(t))
| q2  : ∀ (T : theory L) (p q), provable T (Ȧ (p →̇ q) →̇ Ȧ p →̇ Ȧ q)
| q3  : ∀ (T : theory L) (p), provable T (p →̇ Ȧ p.sf)
| e1  : ∀ (T : theory L) (t), provable T (t =̇ t)
| e2  : ∀ (T : theory L) (p : L.form) (t u), provable T (t =̇ u →̇ p.(t) →̇ p.(u))

infix ` ⊢̇ `:60 := provable

attribute [simp] provable.p1 provable.p2 provable.p3 provable.q1 provable.q2 provable.q3
  provable.e1 provable.e2

def theory.consistent (T : L.theory) : Prop := ¬∃p, (T ⊢̇ p) ∧ (T ⊢̇ ¬̇p) 

inductive theory.add (T : L.theory) (p : L.form) : L.theory 
| new : theory.add p
| old : ∀ {q}, T q → theory.add q

infixl ` ¦ `:60 := theory.add

def theory.delete (T : L.theory) (p : L.form) : L.theory := λ q, T q ∧ q ≠ p

def theory.include (T U : L.theory) : Prop := ∀ p, T p → U p

instance : has_subset L.theory := ⟨theory.include⟩

namespace provable
variables (T : L.theory)

@[simp] lemma pp (p) : T ⊢̇ p →̇ p :=
begin
  have l₀ : T ⊢̇ (p →̇ (p →̇ p) →̇ p) →̇ (p →̇ p →̇ p) →̇ p →̇ p, simp,
  have l₁ : T ⊢̇ p →̇ (p →̇ p) →̇ p, simp,
  have l₂ : T ⊢̇ (p →̇ p →̇ p) →̇ p →̇ p, refine l₀.mp l₁,
  have l₃ : T ⊢̇ p →̇ p →̇ p, simp,
  refine l₂.mp l₃
end

variables {T}

@[simp] lemma imp_r {p} (h : T ⊢̇ p) (q) : T ⊢̇ q →̇ p :=
by { have : T ⊢̇ p →̇ q →̇ p, simp,
     exact this.mp h }

lemma imp_trans {p q r} : (T ⊢̇ p →̇ q) → (T ⊢̇ q →̇ r) → (T ⊢̇ p →̇ r) := λ h₁ h₂,
begin
  have l₁ : T ⊢̇ (p →̇ q →̇ r) →̇ (p →̇ q) →̇ (p →̇ r), simp,  
  have l₂ : T ⊢̇ (p →̇ q →̇ r), simp[h₂],
  have l₃ : T ⊢̇ (p →̇ q) →̇ (p →̇ r), from l₁.mp l₂,
  exact l₃.mp h₁
end

lemma inclusion {p} (h : T ⊢̇ p) : ∀ {U}, T ⊆ U → U ⊢̇ p :=
begin
  induction h with T p hyp_p IH T p q hyp_pq hyp_p IH₁ IH₂ T p hyp_p; try { simp },
  { intros U hyp, refine gen (IH (λ x h, _)), cases h with p hp,
    refine theory.sf.intro _, exact hyp _ hp },
  { intros U hyp, exact (IH₁ hyp).mp (IH₂ hyp) },
  { intros U hyp, exact ax (hyp _ hyp_p) }
end

@[simp] lemma weakening {q} (h : T ⊢̇ q) (p) : T ¦ p ⊢̇ q :=
inclusion h (λ x h, theory.add.old h)

private lemma delete_imply {p} (h : T ⊢̇ p) : ∀ q, (T.delete q) ⊢̇ q →̇ p :=
begin
  induction h with T p hyp_p IH T p₁ p₂ hyp_p₁₂ hyp_p₁ IH₁ IH₂ T p hyp_p;
    try { intros q, apply imp_r, simp }; intros q,
  { have IH : (⇑T).delete q.sf ⊢̇ q.sf →̇ p := IH q.sf,
    have lmm₁ : T.delete q ⊢̇ q →̇ Ȧ q.sf, { simp },
    have lmm₂ : T.delete q ⊢̇ Ȧ q.sf →̇ Ȧ p,
    { suffices : T.delete q ⊢̇ Ȧ(q.sf →̇ p),
      { have lmm : T.delete q ⊢̇ Ȧ(q.sf →̇ p) →̇ Ȧ q.sf →̇ Ȧ p, simp,
        exact lmm.mp this },
      refine gen (inclusion IH (λ x h, _)), 
      rcases h with ⟨h, neq⟩, rcases h with ⟨p', h'⟩,
      refine theory.sf.intro ⟨h', λ c, _⟩,
      rw c at neq, exact neq rfl },
    exact lmm₁.imp_trans lmm₂ },
  { have : T.delete q ⊢̇ (q →̇ p₁ →̇ p₂) →̇ (q →̇ p₁) →̇ (q →̇ p₂), simp, 
    have : T.delete q ⊢̇ (q →̇ p₁) →̇ q →̇ p₂, from this.mp (IH₁ _),
    exact this.mp (IH₂ _) },
  { by_cases eqn : p = q,
    { simp[eqn] },
    { have : T.delete q ⊢̇ p, from ax ⟨hyp_p, eqn⟩,
      simp[this] } }
end

theorem deduction {p q} : (T ¦ p ⊢̇ q) → (T ⊢̇ p →̇ q) := λ h,
by { have : (T ¦ p).delete p ⊢̇ p →̇ q, from delete_imply h p,
     refine inclusion this (λ x h, _), rcases h with ⟨h, neq⟩,
     cases h; simp* at* }


end provable

end language