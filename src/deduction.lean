import fopl theory

universe u

namespace fopl
variables {L : language.{u}}

@[simp] def formula.equals : ∀ {n}, vecterm L n → vecterm L n → formula L
| 0     t₁                   t₂                   := t₁ =̇ t₂
| (n+1) (vecterm.cons t₁ v₁) (vecterm.cons t₂ v₂) := t₁ =̇ t₂ ⩑ formula.equals v₁ v₂
infix ` ≡̇ `:90 := formula.equals

@[simp] lemma equals_rew : ∀ {n} (v₁ v₂ : vecterm L n) (s), (v₁ ≡̇ v₂).rew s = (v₁.rew s) ≡̇ (v₂.rew s)
| 0     _                    _                    _ := rfl
| (n+1) (vecterm.cons t₁ v₁) (vecterm.cons t₂ v₂) s :=
    by simp[formula.rew, vecterm.rew, equals_rew v₁ v₂]

inductive provable : theory L → formula L → Prop
| GE : ∀ {T : theory L} {p}, provable ⇑T p → provable T (∀̇ p)
| MP : ∀ {T : theory L} {p q}, provable T (p →̇ q) → provable T p → provable T q
| AX : ∀ {T : theory L} {p}, p ∈ T → provable T p
| p1 : ∀ {T : theory L} {p q}, provable T (p →̇ q →̇ p)
| p2 : ∀ {T : theory L} {p q r}, provable T ((p →̇ q →̇ r) →̇ (p →̇ q) →̇ p →̇ r)
| p3 : ∀ {T : theory L} {p q}, provable T ((¬̇p →̇ ¬̇q) →̇ q →̇ p)
| q1 : ∀ {T : theory L} {p t}, provable T (∀̇ p →̇ p.rew ι[0 ⇝ t])
| q2 : ∀ {T : theory L} {p q}, provable T (∀̇ (p →̇ q) →̇ ∀̇ p →̇∀̇ q)
| q3 : ∀ {T : theory L} {p}, provable T (p →̇ ∀̇ (p^1))
| e1 : ∀ {T : theory L} {t}, provable T (t =̇ t)
| e2 : ∀ {T : theory L} {t₁ t₂}, provable T (t₁ =̇ t₂ →̇ t₂ =̇ t₁)
| e3 : ∀ {T : theory L} {t₁ t₂ t₃}, provable T (t₁ =̇ t₂ →̇ t₂ =̇ t₃ →̇ t₁ =̇ t₃)
| e4 : ∀ {T : theory L} {n} {v₁ v₂ : vecterm L n} {f : L.fn (n+1)},
    provable T (v₁ ≡̇ v₂ →̇ vecterm.app f v₁ =̇ vecterm.app f v₂)
| e5 : ∀ {T : theory L} {n} {v₁ v₂ : vecterm L n} {r : L.pr (n+1)},
    provable T (v₁ ≡̇ v₂ →̇ formula.app r v₁ →̇ formula.app r v₂)

infix ` ⊢ `:60 := provable

attribute [simp] provable.p1 provable.p2 provable.p3 provable.q1 provable.q2 provable.q3
  provable.e1 provable.e2 provable.e3 provable.e4 provable.e5

def theory.consistent (T : theory L) : Prop := ¬∃p, (T ⊢ p) ∧ (T ⊢ ¬̇p) 

class consistent (T : theory L) := (consistent : theory.consistent T)

def theory.le (T U : theory L) : Prop := ∀ p, T ⊢ p → U ⊢ p

instance : has_le (theory L) := ⟨theory.le⟩

def theory.th (T : theory L) : theory L := {p | T ⊢ p}

def conjunction : list (formula L) → formula L
| []        := ⊤̇
| (p :: ps) := p ⩑ conjunction ps

lemma ss_le {U : ℕ → theory L} (hyp : ∀ s, U s ⊆ U (s+1)) : ∀ {s₁ s₂}, s₁ ≤ s₂ → U s₁ ⊆ U s₂ :=
by { intros s₁, suffices : ∀ t, U s₁ ⊆ U (s₁ + t),
      { intros s₂ eqn, have := this (s₂ - s₁),
        rw (show s₁ + (s₂ - s₁) = s₂, from nat.add_sub_of_le eqn) at this, exact this },
      intros t, induction t with t IH, simp, rw[nat.add_succ],  refine λ x hx, hyp _ (IH hx) }

def formula.equiv (T : theory L) (p₁ p₂ : formula L) : Prop := T ⊢ p₁ ↔̇ p₂

def term.equiv (T : theory L) (t₁ t₂ : term L) : Prop := T ⊢ t₁ =̇ t₂

namespace provable
variables (T : theory L)

@[simp] lemma pp (p) : T ⊢ p →̇ p :=
begin
  have l₀ : T ⊢ (p →̇ (p →̇ p) →̇ p) →̇ (p →̇ p →̇ p) →̇ p →̇ p, simp,
  have l₁ : T ⊢ p →̇ (p →̇ p) →̇ p, simp,
  have l₂ : T ⊢ (p →̇ p →̇ p) →̇ p →̇ p, refine l₀.MP l₁,
  have l₃ : T ⊢ p →̇ p →̇ p, simp,
  refine l₂.MP l₃
end

@[simp] lemma top : T ⊢ ⊤̇ := by simp[formula.top]; exact GE (by simp)

@[simp] lemma add (p) : T+{p} ⊢ p :=
AX (theory.add.new)

variables {T}

lemma GE_cl {T : theory L} [closed_theory T] {p} (h : T ⊢ p) : T ⊢ ∀̇ p :=
by { apply provable.GE, simp[h] }

@[simp] lemma imp_r {p} (h : T ⊢ p) (q) : T ⊢ q →̇ p :=
by { have : T ⊢ p →̇ q →̇ p, simp,
     exact this.MP h }

lemma imp_trans {p q r} : (T ⊢ p →̇ q) → (T ⊢ q →̇ r) → (T ⊢ p →̇ r) := λ h₁ h₂,
begin
  have l₁ : T ⊢ (p →̇ q →̇ r) →̇ (p →̇ q) →̇ (p →̇ r), simp,  
  have l₂ : T ⊢ (p →̇ q →̇ r), simp[h₂],
  have l₃ : T ⊢ (p →̇ q) →̇ (p →̇ r), from l₁.MP l₂,
  exact l₃.MP h₁
end

lemma GE_itr : ∀ {n p}, T^n ⊢ p → T ⊢ nfal p n
| 0     p h := by simp* at*
| (n+1) p h := by { simp at*, have := GE_itr (GE h), simp* at* }

lemma subst_itr (T : theory L) : ∀ (n) (p : formula L) (s : ℕ → term L),
  T ⊢ nfal p n →̇ p.rew (λ x, if x < n then s x else #(x-n))
| 0     p s := by simp
| (n+1) p s := by { simp,
    have lmm₁ : T ⊢ ∀̇ (nfal p n) →̇ nfal (p.rew $ ι[0 ⇝ s n]^n) n,
    { have := @provable.q1 _ T (nfal p n) (s n), simp[formula.nfal_rew] at this,
      exact this },
    have s' := s,
    have lmm₂ := subst_itr n (p.rew $ ι[0 ⇝ s n]^n) s,
    simp[formula.nested_rew] at lmm₂,
    have : (λ x, (ι[0 ⇝ s n]^n $ x).rew (λ x, ite (x < n) (s x) #(x - n))) =
      (λ x, ite (x < n + 1) (s x) #(x - (n + 1))),
    { simp[subst_pow], ext x, have C : x < n ∨ x = n ∨ n < x, from trichotomous _ _,
      cases C,
      { simp[C, nat.lt.step C] }, cases C, { simp[C, term.pow_eq] },
      { have eqn₁ : ¬x - 1 < n, from not_lt.mpr (nat.le_pred_of_lt C),
        have eqn₂ : ¬x < n + 1, from not_lt.mpr (nat.succ_le_iff.mpr C),
        simp[C, eqn₁, eqn₂, nat.sub_sub, add_comm 1 n] } },
    simp[this] at lmm₂,
    exact lmm₁.imp_trans lmm₂ }

lemma subst_itr' {n} {p : formula L} (h : T ⊢ nfal p n ) (s : ℕ → term L) :
  T ⊢ p.rew (λ x, if x < n then s x else #(x-n)) := (subst_itr T n p s).MP h

lemma inclusion {p} (h : T ⊢ p) : ∀ {U}, T ⊆ U → U ⊢ p :=
begin
  induction h with T p hyp_p IH T p q hyp_pq hyp_p IH₁ IH₂ T p hyp_p; try { simp },
  { intros U hyp, refine GE (IH (λ x h, _)), rcases h with ⟨p, hp, rfl⟩,
    refine ⟨p, hyp hp, rfl⟩ },
  { intros U hyp, exact (IH₁ hyp).MP (IH₂ hyp) },
  { intros U hyp, exact AX (hyp hyp_p) }
end

@[elab_as_eliminator]
theorem provable.rec' {T : theory L} (C : ℕ → formula L → Prop)
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
theorem provable.drec' {T : theory L} (C : Π (i : ℕ) (p : formula L), T^i ⊢ p → Prop)
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

@[simp] lemma weakening {q} (h : T ⊢ q) (p) : T+{p} ⊢ q :=
inclusion h (λ x h, theory.add.old h)

private lemma delete_imply {p} (h : T ⊢ p) : ∀ q, T \ {q} ⊢ q →̇ p :=
begin
  induction h with T p hyp_p IH T p₁ p₂ hyp_p₁₂ hyp_p₁ IH₁ IH₂ T p hyp_p;
    try { intros q, apply imp_r, simp }; intros q,
  { have IH : ⇑T \ {q^1} ⊢ q^1 →̇ p := IH (q^1),
    have lmm₁ : T \ {q} ⊢ q →̇ ∀̇ (q^1), { simp },
    have lmm₂ : T \ {q} ⊢ ∀̇ (q^1) →̇ ∀̇ p,
    { suffices : T \ {q} ⊢ ∀̇ (q^1 →̇ p),
      { have lmm : T \ {q} ⊢ ∀̇ (q^1 →̇ p) →̇ ∀̇ (q^1) →̇ ∀̇ p, simp,
        exact lmm.MP this },
      refine GE (inclusion IH (λ x h, _)), 
      rcases h with ⟨h, neq⟩, rcases h with ⟨p', h', rfl⟩,
      refine ⟨p', ⟨h', λ c, _⟩, rfl⟩, simp at c,
      rw c at neq, exact neq rfl },
    exact lmm₁.imp_trans lmm₂ },
  { have : T \ {q} ⊢ (q →̇ p₁ →̇ p₂) →̇ (q →̇ p₁) →̇ (q →̇ p₂), simp, 
    have : T \ {q} ⊢ (q →̇ p₁) →̇ q →̇ p₂, from this.MP (IH₁ _),
    exact this.MP (IH₂ _) },
  { by_cases eqn : p = q,
    { simp[eqn] },
    { have : T \ {q} ⊢ p, from AX ⟨hyp_p, eqn⟩,
      simp[this] } }
end

theorem deduction {p q} : (T+{p} ⊢ q) ↔ (T ⊢ p →̇ q) :=
⟨λ h, by { have : (T+{p}) \ {p} ⊢ p →̇ q, from delete_imply h p,
           refine inclusion this (λ x h, _), rcases h with ⟨h, neq⟩,
           cases h; simp* at*, },
 λ h, by { have : T+{p} ⊢ p →̇ q, from weakening h p,
           exact this.MP (by simp) }⟩

theorem proof_compact : ∀ {T : ℕ → theory L}, (∀ s, T s ⊆ T (s+1)) →
  ∀ {p}, {p | ∃ s, T s p} ⊢ p → ∃ s, T s ⊢ p :=
begin
  suffices : ∀ {p} {U : theory L}, U ⊢ p → ∀ {T : ℕ → theory L},
    (∀ s, T s ⊆ T (s+1)) → U ⊆ {p | ∃ s, T s p} → ∃ s, T s ⊢ p,
  { refine λ T hyp p h, this h hyp (λ x hx, hx) },
  intros p U h,
  induction h,
  case fopl.provable.GE : T p h IH
  { intros U hyp ss,
    let U' := λ s, ⇑(U s),
    have hyp' : ∀ s, U' s ⊆ U' (s + 1),
    { simp[U'], intros s p hyp_p, rcases hyp_p with ⟨p', hyp_q', rfl⟩,
      refine ⟨p', hyp _ hyp_q', rfl⟩ },
    have ss' : ⇑T ⊆ {p : formula L | ∃ s, U' s p},
    { intros q hyp_q, rcases hyp_q with ⟨q', hyp_q', rfl⟩, rcases (ss hyp_q') with ⟨s, hyp_s⟩,
      refine ⟨s, _, hyp_s, rfl⟩ },
    have : ∃ s, U' s ⊢ p, from IH hyp' ss', rcases this with ⟨s, h⟩,
    refine ⟨s, provable.GE h⟩ },
  case fopl.provable.MP : T p q hyp_pq hyp_p IH₁ IH₂
  { intros U hyp ss,
    have : ∃ s, U s ⊢ p →̇ q, from IH₁ hyp ss, rcases this with ⟨s₁, lmm₁⟩,
    have : ∃ s, U s ⊢ p, from IH₂ hyp ss, rcases this with ⟨s₂, lmm₂⟩,
    refine ⟨max s₁ s₂, _⟩,
    have lmm₁ : U (max s₁ s₂) ⊢ p →̇ q, from provable.inclusion lmm₁ (ss_le hyp (by simp)),
    have lmm₂ : U (max s₁ s₂) ⊢ p, from provable.inclusion lmm₂ (ss_le hyp (by simp)),
    exact lmm₁.MP lmm₂ },
  case fopl.provable.AX : T p hyp_p
  { intros U hyp ss, rcases (ss hyp_p) with ⟨s, hyp_s⟩,
    refine ⟨s, provable.AX hyp_s⟩ },
  { refine λ _ _ _, ⟨0, by simp⟩ },
  { refine λ _ _ _, ⟨0, by simp⟩ },
  { refine λ _ _ _, ⟨0, by simp⟩ },
  { refine λ _ _ _, ⟨0, by simp⟩ },
  { refine λ _ _ _, ⟨0, by simp⟩ },
  { refine λ _ _ _, ⟨0, by simp⟩ },
  { refine λ _ _ _, ⟨0, by simp⟩ },
  { refine λ _ _ _, ⟨0, by simp⟩ },
  { refine λ _ _ _, ⟨0, by simp⟩ },
  { refine λ _ _ _, ⟨0, by simp⟩ },
  { refine λ _ _ _, ⟨0, by simp⟩ }
end

@[simp] lemma dne (p) : T ⊢ ¬̇¬̇p →̇ p :=
begin
  have lmm₁ : T+{¬̇¬̇p} ⊢ ¬̇¬̇p, simp,   
  have lmm₂ : T+{¬̇¬̇p} ⊢ ¬̇¬̇p →̇ ¬̇¬̇¬̇¬̇p →̇ ¬̇¬̇p, simp,
  have lmm₃ : T+{¬̇¬̇p} ⊢ ¬̇¬̇¬̇¬̇p →̇ ¬̇¬̇p, from lmm₂.MP lmm₁,
  have lmm₄ : T+{¬̇¬̇p} ⊢ (¬̇¬̇¬̇¬̇p →̇ ¬̇¬̇p) →̇ ¬̇p →̇ ¬̇¬̇¬̇p, simp,
  have lmm₅ : T+{¬̇¬̇p} ⊢ ¬̇p →̇ ¬̇¬̇¬̇p, from lmm₄.MP lmm₃,
  have lmm₆ : T+{¬̇¬̇p} ⊢ (¬̇p →̇ ¬̇¬̇¬̇p) →̇ ¬̇¬̇p →̇ p, simp,
  have lmm₇ : T+{¬̇¬̇p} ⊢ ¬̇¬̇p →̇ p, from lmm₆.MP lmm₅,
  have lmm₈ : T+{¬̇¬̇p} ⊢ p, from lmm₇.MP lmm₁,
  exact deduction.mp lmm₈  
end

@[simp] lemma dni (p) : T ⊢ p →̇ ¬̇¬̇p :=
by { have : T ⊢ (¬̇¬̇¬̇p →̇ ¬̇p) →̇ p →̇ ¬̇¬̇p, simp,
     exact this.MP (by simp) }

@[simp] lemma dn_iff {p} : T ⊢ ¬̇¬̇p ↔ T ⊢ p :=
⟨λ h, (show T ⊢ ¬̇¬̇p →̇ p, by simp).MP h, λ h,(show T ⊢ p →̇ ¬̇¬̇p, by simp).MP h⟩

@[simp] lemma dn1_iff {p q} : (T ⊢ ¬̇¬̇p →̇ q) ↔ (T ⊢ p →̇ q) :=
⟨(dni _).imp_trans, (dne _).imp_trans⟩

@[simp] lemma dn2_iff {p q} : (T ⊢ p →̇ ¬̇¬̇q) ↔ (T ⊢ p →̇ q) :=
⟨λ h, h.imp_trans (dne _), λ h, h.imp_trans (dni _)⟩

lemma explosion {p} (h₁ : T ⊢ p) (h₂ : T ⊢ ¬̇p) {q} : T ⊢ q :=
begin
  have : T ⊢ ¬̇p →̇ ¬̇q →̇ ¬̇p, simp,
  have : T ⊢ ¬̇q →̇ ¬̇p, from this.MP h₂,
  have : T ⊢ p →̇ q, from (show T ⊢ (¬̇q →̇ ¬̇p) →̇ p →̇ q, by simp).MP this,
  exact this.MP h₁
end

lemma contrapose {p q} : (T ⊢ ¬̇p →̇ ¬̇q) ↔ (T ⊢ q →̇ p) :=
⟨λ h, (show T ⊢ (¬̇p →̇ ¬̇q) →̇ q →̇ p, by simp).MP h, λ h,
  by { refine (show T ⊢ (¬̇¬̇q →̇ ¬̇¬̇p) →̇ ¬̇p →̇ ¬̇q, by simp).MP _,
       have : T ⊢ ¬̇¬̇q →̇ p, from (show T ⊢ ¬̇¬̇q →̇ q, by simp).imp_trans h,
       exact this.imp_trans (show T ⊢ p →̇ ¬̇¬̇p, by simp) }⟩

lemma neg_hyp {p} (h : T ⊢ p →̇ ¬̇p) : T ⊢ ¬̇p :=
begin
  have : T+{p} ⊢ ¬̇(p →̇ ¬̇p),
  { have lmm₁ : T+{p} ⊢ p, simp,
    have lmm₂ : T+{p} ⊢ ¬̇p, from (weakening h _).MP lmm₁,
    exact explosion lmm₁ lmm₂ },
  have : T ⊢ p →̇ ¬̇(p →̇ ¬̇p), from deduction.mp this,
  have : T ⊢ (p →̇ ¬̇p) →̇ ¬̇p, from (dni _).imp_trans (contrapose.mpr this),
  exact this.MP h
end

lemma raa {p} (q) (h₁ : T+{p} ⊢ q) (h₂ : T+{p} ⊢ ¬̇q) : T ⊢ ¬̇p :=
neg_hyp (deduction.mp (explosion h₁ h₂))

@[simp] lemma hyp_bot (p) : T ⊢ ⊥̇ →̇ p :=
by { simp[formula.bot], apply deduction.mp, refine explosion (show T+{¬̇⊤̇} ⊢ ⊤̇, by simp) (add _ _) }

@[simp] lemma and {p q} : (T ⊢ p ⩑ q) ↔ (T ⊢ p ∧ T ⊢ q) :=
⟨λ h, by { simp[formula.and] at h, split,
   { have : T+{¬̇p}+{p} ⊢ ¬̇q, 
     from explosion (show T+{¬̇p}+{p} ⊢ p, by simp) (show T+{¬̇p}+{p} ⊢ ¬̇p, by simp),
     have : T ⊢ ¬̇p →̇ p →̇ ¬̇q, from (deduction.mp (deduction.mp this)),
     have : T ⊢ ¬̇(p →̇ ¬̇q) →̇ p := (contrapose.mpr this).imp_trans (by simp),
     exact this.MP h },
   { have : T ⊢ ¬̇q →̇ p →̇ ¬̇q, simp,
     have : T ⊢ ¬̇(p →̇ ¬̇q) →̇ q, from (contrapose.mpr this).imp_trans (by simp),
     exact this.MP h } },
 λ h, by {simp[formula.and], rcases h with ⟨h₁, h₂⟩,
   show T ⊢ ¬̇(p →̇ ¬̇q),
   have : T+{p →̇ ¬̇q} ⊢ ¬̇q, from (add _ _).MP (by simp[h₁]),
   have : T ⊢ (p →̇ ¬̇q) →̇ ¬̇q, from deduction.mp this,
   have : T ⊢ q →̇ ¬̇(p →̇ ¬̇q), from (dni _).imp_trans (contrapose.mpr this),
   exact this.MP h₂ }⟩

@[simp] lemma iff {p q} : (T ⊢ p ↔̇ q) ↔ (T ⊢ p →̇ q ∧ T ⊢ q →̇ p) :=
by simp[formula.iff]

@[simp] lemma neg_imp {p q} : (T ⊢ ¬̇(p →̇ q)) ↔ (T ⊢ p ⩑ ¬̇q) :=
begin
  simp only [formula.and], split; intros h,
  { apply raa (p →̇ q),
    { have : T+{p →̇ ¬̇¬̇q} ⊢ p →̇ ¬̇¬̇q, from add _ _, simp* at * },
    { simp[h] } },
  { apply raa (p →̇ ¬̇¬̇q); simp[h] }
end

lemma or_l (p q) : T ⊢ p →̇ p ⩒ q :=
by simp[formula.or]; refine deduction.mp (deduction.mp (explosion (show T+{p}+{¬̇p} ⊢ p, by simp) (by simp)))

lemma or_r (p q) : T ⊢ q →̇ p ⩒ q :=
by simp[formula.or]; refine deduction.mp (weakening h _)

lemma hyp_or {p₁ p₂ q} : (T ⊢ p₁ →̇ q) → (T ⊢ p₂ →̇ q) → (T ⊢ p₁ ⩒ p₂ →̇ q) := λ h₁ h₂,
begin
  simp[formula.or], apply contrapose.mp, refine deduction.mp _, simp,
  refine ⟨deduction.mpr (contrapose.mpr h₁), deduction.mpr (contrapose.mpr h₂)⟩, 
end

lemma hyp_and_left {p₁ p₂ q} : (T ⊢ p₁ →̇ q) → (T ⊢ p₁ ⩑ p₂ →̇ q) := λ h,
begin
  have : T+{p₁ ⩑ p₂} ⊢ p₁, { have : T+{p₁ ⩑ p₂} ⊢ p₁ ⩑ p₂, from add _ _, simp* at * },
  refine deduction.mp ((show T+{p₁ ⩑ p₂} ⊢ p₁ →̇ q, by simp[h]).MP this)
end

lemma hyp_and_right {p₁ p₂ q} : (T ⊢ p₂ →̇ q) → (T ⊢ p₁ ⩑ p₂ →̇ q) := λ h,
begin
  have : T+{p₁ ⩑ p₂} ⊢ p₂, { have : T+{p₁ ⩑ p₂} ⊢ p₁ ⩑ p₂, from add _ _, simp* at * },
  refine deduction.mp ((show T+{p₁ ⩑ p₂} ⊢ p₂ →̇ q, by simp[h]).MP this)
end

lemma axiom_and {p₁ p₂ q} : T+{p₁ ⩑ p₂} ⊢ q ↔ T+{p₁}+{p₂} ⊢ q :=
⟨λ h,
 by { have lmm₁ : T+{p₁}+{p₂} ⊢ p₁ ⩑ p₂, by simp,
      have lmm₂ : T+{p₁}+{p₂} ⊢ p₁ ⩑ p₂ →̇ q, simp[deduction.mp h],
      exact lmm₂.MP lmm₁ },
 λ h,
 by { have lmm₁ : T+{p₁ ⩑ p₂} ⊢ p₁ →̇ p₂ →̇ q, simp[deduction.mp (deduction.mp h)],
      have lmm₂ : T+{p₁ ⩑ p₂} ⊢ p₁ ⩑ p₂, from add _ _, simp at lmm₂,
      exact (lmm₁.MP lmm₂.1).MP lmm₂.2 }  ⟩

lemma conjunction_mem {P : list (formula L)} : ∀ {p}, p ∈ P → ∅ ⊢ conjunction P →̇ p :=
begin
  induction P with p P IH; simp[conjunction],
  have lmm₁ : ∅ ⊢ p ⩑ conjunction P →̇ p, from hyp_and_left (by simp),
  have lmm₂ : ∀ q, q ∈ P → ∅ ⊢ p ⩑ conjunction P →̇ q, from λ q hq, hyp_and_right (IH hq),
  refine ⟨lmm₁, lmm₂⟩
end

lemma conjunction_inclusion {P Q : list (formula L)} : 
  Q ⊆ P → ∅ ⊢ conjunction P →̇ conjunction Q :=
begin
  induction Q with q Q IH; simp[conjunction],
  intros hyp_q hyp_Q,
  have lmm₁ : ∅+{conjunction P} ⊢ q, from deduction.mpr (conjunction_mem hyp_q),  
  have lmm₂ : ∅+{conjunction P} ⊢ conjunction Q, from deduction.mpr (IH hyp_Q),
  refine deduction.mp (and.mpr ⟨lmm₁, lmm₂⟩)
end

private lemma conjunction_sf (P₀ : list (formula L)) : (∀ p, p ∈ P₀ → ⇑T p) →
  ∃ P, (conjunction P)^1 = conjunction P₀ ∧ (∀ p, p ∈ P → T p) :=
begin
  induction P₀ with p₀ P₀ IHl, { refine λ _, ⟨[], _⟩, simp[conjunction] },
  { intros hyp,
    have : ∀ p, p ∈ P₀ → ⇑T p,
    { intros p hyp_p, refine hyp _ _, simp[hyp_p] },
    rcases IHl this with ⟨P, hyp_P⟩,
    have := hyp p₀ (by simp),
    rcases this with ⟨p, hyp_p, rfl⟩,
    have lmm₁ : (conjunction (p :: P))^1= conjunction (p^1 :: P₀),
    { simp[conjunction, hyp_P] },
    have lmm₂ : ∀ (q : formula L), q ∈ (p :: P) → T q,
    { simp, refine ⟨hyp_p, hyp_P.2⟩ },
    refine ⟨p :: P, lmm₁, lmm₂⟩ }
end

theorem proof_conjunction {T : theory L} {p} :
  T ⊢ p → ∃ P : list (formula L), (∀ p, p ∈ P → T p) ∧ ∅ ⊢ conjunction P →̇ p := λ h,
begin
  induction h,
  case fopl.provable.GE : T p hyp IH
  { rcases IH with ⟨P₀, hyp_P₀, prov⟩,
    have : ∃ P, (conjunction P)^1 = conjunction P₀ ∧ ∀ p, p ∈ P → T p, from conjunction_sf _ hyp_P₀,
    rcases this with ⟨P, eqn, hyp_P⟩,
    have : ∅ ⊢ conjunction P →̇ ∀̇ p,
    { refine deduction.mp (GE _),
      rw [←sf_dsb, eqn], refine deduction.mpr (inclusion prov (λ x hx, _)), cases hx },
    refine ⟨P, hyp_P, this⟩ },
  case fopl.provable.MP : T p q hyp_pq hyp_p IH₁ IH₂
  { rcases IH₁ with ⟨P₁, IH₁, prov₁⟩, rcases IH₂ with ⟨P₂, IH₂, prov₂⟩,
    refine ⟨P₁ ++ P₂, _, _⟩,
    { simp, intros p h, cases h, refine IH₁ _ h, refine IH₂ _ h },
    { have : ∅+{conjunction (P₁ ++ P₂)} ⊢ conjunction P₂, from deduction.mpr (conjunction_inclusion (by simp)),
      have lmm₁ : ∅+{conjunction (P₁ ++ P₂)} ⊢ p, from (show _ ⊢ conjunction P₂ →̇ p, by simp[prov₂]).MP this,
      have : ∅+{conjunction (P₁ ++ P₂)} ⊢ conjunction P₁, from deduction.mpr (conjunction_inclusion (by simp)),
      have lmm₂ : ∅+{conjunction (P₁ ++ P₂)} ⊢ p →̇ q,
      from (show _ ⊢ conjunction P₁ →̇ p →̇ q, by simp[prov₁]).MP this,
      refine deduction.mp (lmm₂.MP lmm₁) } },
  case fopl.provable.AX : T p hyp_p
  { refine ⟨[p], _⟩, simp[conjunction],
    have : ∅ ⊢ p ⩑ ⊤̇ →̇ p,
    { apply deduction.mp, have : ∅+{p ⩑ ⊤̇} ⊢ p ⩑ ⊤̇, from add _ _ , simp* at* },
    refine ⟨hyp_p, this⟩ },
  { refine ⟨[], _⟩, simp },
  { refine ⟨[], _⟩, simp },
  { refine ⟨[], _⟩, simp },
  { refine ⟨[], _⟩, simp },
  { refine ⟨[], _⟩, simp },
  { refine ⟨[], _⟩, simp },
  { refine ⟨[], _⟩, simp },
  { refine ⟨[], _⟩, simp },
  { refine ⟨[], _⟩, simp },
  { refine ⟨[], _⟩, simp },
  { refine ⟨[], _⟩, simp }
end

lemma fal_subst {p} (h : T ⊢ ∀̇ p) (t) : T ⊢ p.rew ι[0 ⇝ t] :=
(show T ⊢ ∀̇ p →̇ p.rew ι[0 ⇝ t], by simp).MP h

lemma add_sf (p) : ⇑(T +{∀̇ p}) ⊢ p :=
by { have : ⇑(T +{∀̇ p}) ⊢ (∀̇ p)^1, rw ← sf_dsb, simp, 
     have := fal_subst this #0, simp[formula.nested_rew] at this,
     have eqn : (λ x, (((λ x, #(x + 1) : ℕ → term _)^1) x).rew ι[0 ⇝ #0]) = (ι : ℕ → vecterm L 0),
     { funext n, cases n; refl }, exact this }

private lemma rgerg {P : list (formula L)} : (∀ p, p ∈ P → T p) → T ⊢ conjunction P :=
begin
  induction P with p P IH; simp[conjunction],
  refine λ hyp_p hyp, ⟨AX hyp_p, IH hyp⟩,
end

lemma cl_prove_rew [cl : closed_theory T] : ∀ {p : formula L}, T ⊢ p → ∀ s, T ⊢ p.rew s :=
begin
  suffices : ∀ {p : formula L} {T}, T ⊢ p → closed_theory T → ∀ s, T ⊢ p.rew s,
  { refine λ p h s, this h cl _ },
  intros p T h,
  induction h,
  case GE : T p hyp IH
  { intros cl s, rw[@closed_theory_sf_eq _ _ cl] at IH,
    refine GE _, simp[@closed_theory_sf_eq _ _ cl], exact IH cl _ },
  case MP : T p q hyp_pq hyp_p IH₁ IH₂
  { intros cl s, simp[formula.rew, @closed_theory_sf_eq _ _ cl] at*, refine (IH₁ cl _).MP (IH₂ cl _) },
  case AX : T p hyp
  { intros cl s, simp[@closed_theory.cl _ _ cl _ hyp], exact AX hyp },
  { simp[formula.rew] },
  { simp[formula.rew] },
  { simp[formula.rew] },
  { intros, simp[formula.rew, formula.subst_sf_rew] },
  { simp[formula.rew] },
  case q3 : T p { intros,
    simp[formula.rew],
    have : (p^1).rew (s^1) = (p.rew s)^1,
    { simp[formula.pow_eq, formula.rew, formula.nested_rew], refl },
    simp[this] },
  { simp[formula.rew] },
  { simp[formula.rew] },
  { simp[formula.rew] },
  { simp[formula.rew, vecterm.rew] },
  { simp[formula.rew] },
end

lemma pp_prove_rew {n} (pp : proper_at n T) :
  ∀ {p : formula L}, T ⊢ p → ∀ s, T ⊢ p.rew (s^n) :=
begin
  suffices : ∀ {p : formula L} {T},
    T ⊢ p → ∀ {n}, proper_at n T → ∀ s, T ⊢ p.rew (s^n),
  { refine λ p h s, this h @pp _ },
  intros p T h,
  induction h,
  case GE : T p hyp IH
  { intros n pp s,
    refine GE _, refine @IH (n+1) (@proper_theory_sf_itr _ _ _ @pp 1) s },
  case MP : T p q hyp_pq hyp_p IH₁ IH₂
  { intros n pp s, refine (IH₁ @pp _).MP (IH₂ @pp _) },
  case AX : T p hyp
  { intros n pp s, refine AX (pp _ _ hyp) },
  { simp[formula.rew] },
  { simp[formula.rew] },
  { simp[formula.rew] },
  { intros, simp[formula.rew, formula.subst_sf_rew] },
  { simp[formula.rew] },
  case q3 : T p { intros,
    simp[formula.rew],
    simp[←formula.pow_rew_distrib] },
  { simp[formula.rew] },
  { simp[formula.rew] },
  { simp[formula.rew] },
  { simp[formula.rew, vecterm.rew] },
  { simp[formula.rew] },
end

lemma ppc_prove_rew (n) [pp : proper n T] :
  ∀ {p : formula L}, T ⊢ p → ∀ s, T ⊢ p.rew (s^n) := @pp_prove_rew _ _ n pp.proper

lemma ppc0_prove_rew [pp : proper 0 T] :
  ∀ {p : formula L}, T ⊢ p → ∀ s, T ⊢ p.rew s := @pp_prove_rew _ _ 0 pp.proper

lemma cl_fal_elim [closed_theory T] {p} : T ⊢ ∀̇ p ↔ T ⊢ p :=
⟨λ h, by { have : T ⊢ (∀̇ p)^1,  from cl_prove_rew h _,
           have lmm : T ⊢ (p.rew (#0 ⌢ λ n, #(n+2))).rew ι[0 ⇝ #0], from this.fal_subst #0,
           have : (p.rew (#0 ⌢ λ n, #(n+2))).rew ι[0 ⇝ #0] = p,
           { suffices : (p.rew (#0 ⌢ λ n, #(n+2))).rew ι[0 ⇝ #0] = p.rew ι, simp* at*,
             simp[formula.nested_rew, -formula.rew_ι], congr,
             ext n, cases n; simp[concat, vecterm.rew] },
           rw[this] at lmm, exact lmm },
 λ h, GE $ by simp[h]⟩

private lemma conjunction_rew_eq : ∀ (P : list (formula L)) (s),
  (conjunction P).rew s = conjunction (P.map (λ p, p.rew s))
| []       _ := by simp[conjunction, formula.rew]
| (p :: P) s := by simp[conjunction, formula.rew, conjunction_rew_eq P]

lemma conjunction_provable : ∀ {P : list (formula L)} (h : ∀ p, p ∈ P → T ⊢ p), T ⊢ conjunction P
| []       h := by simp[conjunction]
| (p :: P) h := by { simp[conjunction],
    have lmm₁ : T ⊢ p, { refine h _ _, simp },
    have lmm₂ : T ⊢ conjunction P, { refine conjunction_provable (λ p hyp, h _ _), simp, right, exact hyp },
    refine ⟨lmm₁, lmm₂⟩ }

lemma sf_sf {p : formula L} : ⇑T ⊢ p^1 ↔ T ⊢ p :=
⟨λ h, by { have := (GE h).fal_subst #0, simp* at* },
 λ h, by { have : ∃ P, (∀ p, p ∈ P → p ∈ T) ∧ ∅ ⊢ conjunction P →̇ p,
  from proof_conjunction h, rcases this with ⟨P, hyp_P, prov⟩,
  have lmm₁ : ⇑T ⊢ conjunction (P.map (λ p, p^1)),
  { refine conjunction_provable (λ p hyp, AX _), simp at hyp, rcases hyp with ⟨p', p'_mem, rfl⟩,
    refine ⟨p', hyp_P p' p'_mem, rfl⟩ },
  have lmm₂ : ⇑T ⊢ conjunction (P.map (λ p, p^1)) →̇ p^1,
  { have : ∅ ⊢ (conjunction P)^1 →̇ p^1, from cl_prove_rew prov _,
    simp[formula.pow_eq, conjunction_rew_eq] at this,
    refine inclusion this (λ p h, _), exfalso, exact h },
  refine lmm₂.MP lmm₁ }⟩

lemma sf_itr_sf_itr : ∀ (i : ℕ) (p : formula L),
  T^i ⊢ p^i ↔ T ⊢ p
| 0     p := by simp
| (i+1) p := by simp[theory.sf_itr_succ];
    rw [show p^(i + 1) = (p^i)^1, by simp[formula.pow_add], sf_sf, @sf_itr_sf_itr i]

lemma pow_rew' [pp : proper 0 T] (i : ℕ) {p : formula L} (h : T^(i + 1) ⊢ p) (s u : ℕ → term L) :
  T^i ⊢ p.rew (λ x, if x < i + 1 then s x else (u (x - i - 1))^i) :=
begin
  have t := #0,
  let f : ℕ → term L := λ x, if x < i + 1 then s x else (u (x - i - 1))^i,
  have : T^i ⊢ ∀̇ (nfal p (i+1) ^ (i+1)), from GE ((sf_itr_sf_itr (i + 1) _).mpr (GE_itr h)),
  have := this.fal_subst t,
  have := (ppc_prove_rew i this u),
  simp[formula.nfal_pow, formula.nested_rew, -nfal] at this,
  have := subst_itr' this s, simp[formula.nested_rew, vecterm.nested_rew, ι] at this,
  simp[subst_pow, rewriting_sf_itr.pow_add] at this,
  have eqn : (λ x, (ite (x < i + 1) #x #(x + (i + 1))).rew (λ x, (ι[(i + 1) ⇝ t ^ (i + 1)] x).rew
    (λ x, (u^(i + (i + 1)) $ x).rew (λ x, ite (x < i+1) (s x) #(x - (i+1))) ))) = f,
  { funext x₀, by_cases C : x₀ < i + 1; simp[C],
    { simp[f, rewriting_sf_itr.pow_eq'],
      have : x₀ < i + (i + 1), exact nat.lt_add_left _ _ _ C,
      simp[this, C] },
    { have : i + 1 < x₀ + (i + 1), { omega },
      simp[f, this, rewriting_sf_itr.pow_eq', vecterm.pow_eq], 
      have : ¬x₀ + i < i + (i + 1), { omega }, simp[this],
      have e₁ : ∀ x, ¬x + (i + (i + 1)) < i + 1, { intros x, omega },
      have e₂ : ∀ x, x + (i + (i + 1)) - (i + 1) = x + i, { omega },
      simp[e₁, e₂],
      have : i + 1 ≤ x₀, { exact not_lt.mp C },
      simp[←nat.sub_sub, C] } },
  rw eqn at this,
  exact this
end

lemma pow_subst' [pp : proper 0 T] (i : ℕ) {p : formula L} (h : T^(i + 1) ⊢ p) (t : term L) :
  T^i ⊢ p.rew ι[i ⇝ t] :=
by { have := pow_rew' i h ι[i ⇝ t] ι,
     have eqn : (λ x, ite (x < i + 1) (ι[i ⇝ t] x) (ι (x - i - 1) ^ i)) = ι[i ⇝ t],
     { funext x, by_cases C₁ : x < i + 1; simp[C₁],
       have : i < x, exact nat.succ_le_iff.mp (not_lt.mp C₁),
       simp[this, ι, nat.sub_sub, ←nat.sub_sub_assoc (not_lt.mp C₁) i.le_succ] },
     rw eqn at this, exact this }

lemma use {p : formula L} (t) (h : T ⊢ p.rew ι[0 ⇝ t]) : T ⊢ ∃̇p :=
begin
  simp[formula.ex],
  refine raa (p.rew ι[0 ⇝ t]) (by simp[h]) (deduction.mpr _),
  have : ¬̇p.rew ι[0 ⇝ t] = (¬̇p).rew ι[0 ⇝ t] := rfl,
  rw[this], refine provable.q1
end

lemma eq_symm : ∀ {t u}, (T ⊢ t =̇ u) ↔ (T ⊢ u =̇ t) :=
begin
  suffices : ∀ t u, (T ⊢ t =̇ u) → (T ⊢ u =̇ t),
  { intros t u, refine ⟨this _ _, this _ _⟩ },
  intros t u h,
  have : T ⊢ t =̇ u →̇ u =̇ t, simp,
  refine this.MP h
end

lemma eq_trans {t₁ t₂ t₃} : (T ⊢ t₁ =̇ t₂) → (T ⊢ t₂ =̇ t₃) → (T ⊢ t₁ =̇ t₃) := λ h₁ h₂,
by { have : T ⊢ t₁ =̇ t₂ →̇ t₂ =̇ t₃ →̇ t₁ =̇ t₃, simp, exact (this.MP h₁).MP h₂ }

lemma equal_rew_equals : ∀ {n} (v : vecterm L n) (s₁ s₂ : ℕ → term L) (e : ∀ n, T ⊢ s₁ n =̇ s₂ n),
  T ⊢ v.rew s₁ ≡̇ v.rew s₂
| _ (vecterm.cons t v) _ _ eqn := by simp[vecterm.rew];
    exact ⟨equal_rew_equals t _ _ eqn, equal_rew_equals v _ _ eqn⟩
| _ (#n)               _ _ eqn := by simp[vecterm.rew]; exact eqn _
| _ (vecterm.const c)  _ _ eqn := by simp[vecterm.rew]
| _ (vecterm.app f v)  _ _ eqn := by simp[vecterm.rew];
    exact provable.e4.MP (equal_rew_equals v _ _ eqn)

lemma equal_rew_equals_term : ∀ (t : term L) (s₁ s₂ : ℕ → term L) (e : ∀ n, T ⊢ s₁ n =̇ s₂ n),
  T ⊢ t.rew s₁ =̇ t.rew s₂ := equal_rew_equals

lemma equal_fal_subst_equals {n} (v : vecterm L n) {t₁ t₂} (h : T ⊢ t₁ =̇ t₂) :
  T ⊢ v.rew (t₁ ⌢ ι) ≡̇ v.rew (t₂ ⌢ ι) :=
by { refine equal_rew_equals v _ _ (λ n, _), { cases n; simp[concat, h] } }

lemma equal_rew_iff (p : formula L) : ∀ {s₁ s₂ : ℕ → term L} {T : theory L} (eqn : ∀ n, T ⊢ s₁ n =̇ s₂ n),
  T ⊢ p.rew s₁ ↔̇ p.rew s₂ :=
begin
  induction p,
  case const { by simp[formula.rew] },
  case app : n p v { intros, simp[formula.rew],
    exact ⟨(provable.e5.MP (equal_rew_equals v _ _ eqn)),
      (provable.e5.MP (equal_rew_equals v _ _ (λ n, eq_symm.mp $ eqn n)))⟩ },
  case equal : t₁ t₂ { intros, simp[formula.rew],
    refine ⟨deduction.mp _, deduction.mp _⟩,
    { have lmm₁ : T+{t₁.rew s₁ =̇ t₂.rew s₁} ⊢ t₁.rew s₂ =̇ t₁.rew s₁,
      { refine equal_rew_equals t₁ s₂ s₁ (λ n, eq_symm.mp _), simp[eqn n] },
      have lmm₂ : T+{t₁.rew s₁ =̇ t₂.rew s₁} ⊢ t₁.rew s₁ =̇ t₂.rew s₁, { simp },
      have lmm₃ : T+{t₁.rew s₁ =̇ t₂.rew s₁} ⊢ t₂.rew s₁ =̇ t₂.rew s₂,
      { refine equal_rew_equals t₂ s₁ s₂ (λ n, _), simp[eqn n]  },
      refine lmm₁.eq_trans (lmm₂.eq_trans lmm₃) },
    { have lmm₁ : T+{t₁.rew s₂ =̇ t₂.rew s₂} ⊢ t₁.rew s₁ =̇ t₁.rew s₂,
      { refine equal_rew_equals t₁ s₁ s₂ (λ n, _), simp[eqn n] },
      have lmm₂ : T+{t₁.rew s₂ =̇ t₂.rew s₂} ⊢ t₁.rew s₂ =̇ t₂.rew s₂, { simp },
      have lmm₃ : T+{t₁.rew s₂ =̇ t₂.rew s₂} ⊢ t₂.rew s₂ =̇ t₂.rew s₁,
      { refine equal_rew_equals t₂ s₂ s₁ (λ n, eq_symm.mp _), simp[eqn n]  },
      refine lmm₁.eq_trans (lmm₂.eq_trans lmm₃) } },
  case imply : p q IH₁ IH₂
  { intros, have IH₁ := IH₁ eqn, have IH₂ := IH₂ eqn,
    simp[formula.rew] at*, split,
    { refine deduction.mp (deduction.mp _), 
      have : T+{p.rew s₁ →̇ q.rew s₁}+{p.rew s₂} ⊢ p.rew s₂, simp,
      have : T+{p.rew s₁ →̇ q.rew s₁}+{p.rew s₂} ⊢ p.rew s₁, from MP (by simp[IH₁]) this,
      have : T+{p.rew s₁ →̇ q.rew s₁}+{p.rew s₂} ⊢ q.rew s₁,
        from MP (show _ ⊢ p.rew s₁ →̇ q.rew s₁, by simp) this,
      from MP (by simp[IH₂]) this },
    { refine deduction.mp (deduction.mp _),
      have : T+{p.rew s₂ →̇ q.rew s₂}+{p.rew s₁} ⊢ p.rew s₁, simp,
      have : T+{p.rew s₂ →̇ q.rew s₂}+{p.rew s₁} ⊢ p.rew s₂, from MP (by simp[IH₁]) this,
      have : T+{p.rew s₂ →̇ q.rew s₂}+{p.rew s₁} ⊢ q.rew s₂,
        from MP (show _ ⊢ p.rew s₂ →̇ q.rew s₂, by simp) this,
      from MP (by simp[IH₂]) this } },
  case neg : p IH
  { intros, simp[formula.rew] at*,
    refine ⟨contrapose.mpr _, contrapose.mpr _⟩; simp[IH eqn] },
  case fal : p IH
  { intros, simp[formula.rew],
    have := @IH (s₁^1) (s₂^1) ⇑T
      (λ n, by { cases n; simp, exact sf_sf.mpr (eqn n) }),
    simp at this, 
    refine ⟨provable.q2.MP (GE this.1), provable.q2.MP (GE this.2)⟩ }
end

lemma dummy_fal_quantifir (p) : T ⊢ p ↔̇ ∀̇ (p^1) :=
by { have : T ⊢ ∀̇ (p^1) →̇ (p^1).rew ι[0 ⇝ #0], from provable.q1, simp* at * }

lemma dummy_fal_quantifir_iff {p : formula L} : T ⊢ ∀̇ (p^1) ↔ T ⊢ p :=
by { have := provable.iff.mp (@dummy_fal_quantifir _ T p), split,
     { refine λ h, (this.2.MP h) },
     { refine λ h, (this.1.MP h) } }

lemma dummy_ex_quantifir (p) : T ⊢ p ↔̇ ∃̇ (p^1) :=
by { simp[formula.ex], split,
     { refine contrapose.mp _, simp, exact (provable.iff.mp (dummy_fal_quantifir ¬̇p)).2 },
     { refine contrapose.mp _, simp, exact (provable.iff.mp (dummy_fal_quantifir ¬̇p)).1 } }

@[simp] lemma T_hyp_eliminate {p} : T ⊢ ⊤̇ →̇ p ↔ T ⊢ p :=
⟨λ h, by { have : T ⊢ ⊤̇, simp, exact h.MP this }, λ h, by simp[h]⟩

end provable

lemma inclusion_le {T U : theory L} : T ⊆ U → T ≤ U := λ hyp p h,
h.inclusion hyp

end fopl