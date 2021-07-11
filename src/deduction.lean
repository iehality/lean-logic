import fopl

universe u

namespace fopl
variables {L : language.{u}}

def theory (L : language) := set (formula L)

notation `theory `L:max := set (formula L)

inductive theory.sf (T : theory L) : theory L
| intro : ∀ {p : formula L}, p ∈ T → theory.sf p.sf
prefix `⇑`:max := theory.sf

@[simp] def theory.sf_itr (T : theory L) : ℕ → theory L
| 0     := T
| (n+1) := theory.sf (theory.sf_itr n)
instance sf_itr_pow : has_pow (theory L) ℕ := ⟨theory.sf_itr⟩

@[simp] lemma sf_itr_0 (T : theory L) : T^0 = T := rfl
@[simp] lemma sf_itr_succ (T : theory L) (n) : T^(n+1) = ⇑(T^n) := rfl

@[simp] def formula.equals : ∀ {n}, vecterm L n → vecterm L n → formula L
| 0     t₁                   t₂                   := t₁ =̇ t₂
| (n+1) (vecterm.cons t₁ v₁) (vecterm.cons t₂ v₂) := t₁ =̇ t₂ ⩑ formula.equals v₁ v₂
infix ` ≡̇ `:90 := formula.equals

@[simp] lemma equals_rew : ∀ {n} (v₁ v₂ : vecterm L n) (s), (v₁ ≡̇ v₂).rew s = (v₁.rew s) ≡̇ (v₂.rew s)
| 0     _                    _                    _ := rfl
| (n+1) (vecterm.cons t₁ v₁) (vecterm.cons t₂ v₂) s :=
    by simp[formula.rew, vecterm.rew, equals_rew v₁ v₂]

inductive provable : theory L → formula L → Prop
| GE : ∀ {T : theory L} {p}, provable ⇑T p → provable T (∀̇p)
| MP : ∀ {T : theory L} {p q}, provable T (p →̇ q) → provable T p → provable T q
| AX : ∀ {T : theory L} {p}, p ∈ T → provable T p
| p1 : ∀ {T : theory L} {p q}, provable T (p →̇ q →̇ p)
| p2 : ∀ {T : theory L} {p q r}, provable T ((p →̇ q →̇ r) →̇ (p →̇ q) →̇ p →̇ r)
| p3 : ∀ {T : theory L} {p q}, provable T ((¬̇p →̇ ¬̇q) →̇ q →̇ p)
| q1 : ∀ {T : theory L} {p t}, provable T (∀̇p →̇ p.rew ₛ[t])
| q2 : ∀ {T : theory L} {p q}, provable T (∀̇(p →̇ q) →̇ ∀̇p →̇∀̇q)
| q3 : ∀ {T : theory L} {p}, provable T (p →̇ ∀̇p.sf)
| e1 : ∀ {T : theory L} {t}, provable T (t =̇ t)
| e2 : ∀ {T : theory L} {t₁ t₂}, provable T (t₁ =̇ t₂ →̇ t₂ =̇ t₁)
| e3 : ∀ {T : theory L} {t₁ t₂ t₃}, provable T (t₁ =̇ t₂ →̇ t₂ =̇ t₃ →̇ t₁ =̇ t₃)
| e4 : ∀ {T : theory L} {n} {v₁ v₂ : vecterm L n} {f : L.fn (n+1)},
    provable T (v₁ ≡̇ v₂ →̇ vecterm.app f v₁ =̇ vecterm.app f v₂)
| e5 : ∀ {T : theory L} {n} {v₁ v₂ : vecterm L n} {r : L.pr (n+1)},
    provable T (v₁ ≡̇ v₂ →̇ formula.app r v₁ →̇ formula.app r v₂)

infix ` ⊢̇ `:60 := provable

attribute [simp] provable.p1 provable.p2 provable.p3 provable.q1 provable.q2 provable.q3
  provable.e1 provable.e2 provable.e3 provable.e4 provable.e5

def theory.consistent (T : theory L) : Prop := ¬∃p, (T ⊢̇ p) ∧ (T ⊢̇ ¬̇p) 

inductive theory.add (T : theory L) (p : formula L) : theory L 
| new : theory.add p
| old : ∀ {q}, q ∈ T → theory.add q

notation T`+{`:max p`}` := theory.add T p

def theory.le (T U : theory L) : Prop := ∀ p, T ⊢̇ p → U ⊢̇ p
instance : has_le (theory L) := ⟨theory.le⟩

class closed_theory (T : theory L) := (cl : ∀ {p}, p ∈ T → sentence p)

def proper_at (n : ℕ) (T : theory L) : Prop := ∀ (p : formula L) (s), p ∈ T → p.rew (s^n) ∈ T

def ordered_p (T : theory L) : Prop := ∀ (p : formula L), p ∈ T → p.sf ∈ T

class ordered (T : theory L) := (ordered : ordered_p T)

lemma oedered_p_theory_sf (T : theory L) : ordered_p T → ordered_p ⇑T := λ h p hyp,
by { cases hyp with p hyp_p, exact theory.sf.intro (h _ hyp_p) }

instance ordered_theory_sf {T : theory L} [od : ordered T] :
  ordered ⇑T := ⟨oedered_p_theory_sf _ od.ordered⟩

instance ordered_theory_sf_itr {T : theory L} [od : ordered T] : ∀ n : ℕ,
  ordered (T^n)
| 0 := od
| (n+1) := @fopl.ordered_theory_sf _ _  (ordered_theory_sf_itr n)

class proper (n : ℕ) (T : theory L) := (proper : proper_at n T)

instance ordered_proper {T : theory L} [pp : proper 0 T] : ordered T :=
⟨λ p h, by { have := pp.proper, exact this _ (λ x, #(x+1)) h }⟩

lemma proper.proper0 {T : theory L} [proper 0 T] :
  ∀ {p : formula L} {s}, p ∈ T → p.rew s ∈ T := @proper.proper _ 0 T _

instance : closed_theory (∅ : theory L) := ⟨λ _ h, by exfalso; exact h⟩

instance (n) : proper n (∅ : theory L) := ⟨λ _ _ h, by exfalso; exact h⟩

instance (n) : proper n (set.univ : theory L) := ⟨λ p s h, by simp⟩

def openform : theory L := {p | p.Open = tt}

instance (n) : proper n (openform : theory L) :=
⟨λ p s h, by { induction p; simp[openform] at*; simp* at* }⟩

lemma theory_sf_itr_sf_itr {T : theory L} : ∀ {n} {p : formula L},
  p ∈ T^n → ∃ q : formula L, p = (q.rew (λ x, #(x+n))) ∧ q ∈ T
| 0 p h := by { simp, exact h }
| (n+1) p h := by { simp at h, cases h with p' hyp_p',
    have IH := theory_sf_itr_sf_itr hyp_p', rcases IH with ⟨q, hyp_q⟩,
    refine ⟨q, _⟩,
    have : q.rew (λ x, #(x + (n + 1))) = (q.rew (λ x, #(x + n))).sf,
    { simp[formula.sf, formula.nested_rew, add_assoc] }, simp[this, hyp_q], refl }

lemma mem_theory_sf_itr {T : theory L} : ∀ (n) {p : formula L},
  p ∈ T → p.sf_itr n ∈ T^n
| 0     p h := by simp[has_pow.pow, formula.sf_itr, h]
| (n+1) p h := by { simp[formula.sf_itr],
    have lmm₁ : (p.sf_itr n).sf ∈ ⇑(T^n) := theory.sf.intro (@mem_theory_sf_itr n _ h),
    have : p.rew (λ x, #(x + (n + 1))) = (p.sf_itr n).sf,
    { simp[formula.sf, formula.sf_itr, formula.nested_rew, add_assoc] },
    simp[this], exact lmm₁ }

lemma proper_sf_inclusion (T : theory L) [proper 0 T] (n) :
  T^(n+1) ⊆ T^n := λ p h,
by { have := theory_sf_itr_sf_itr h, rcases this with ⟨q, rfl, lmm⟩,
     have : q.sf ∈ T, { simp[formula.sf, proper.proper0 lmm] },
     have : q.sf.sf_itr n ∈ T^n, from mem_theory_sf_itr n this,
     have eqn : q.rew (λ x, #(x + (n + 1))) = q.sf.sf_itr n,
     { simp[formula.sf, formula.sf_itr, formula.nested_rew, nat.succ_add_eq_succ_add] },
     simp[eqn], exact this }

lemma ordered_inclusion (T : theory L) [ordered T] : ⇑T ⊆ T := λ p h,
by { cases h with p hyp, exact ordered.ordered _ hyp }

lemma formula.sf_rew_sf_eq (s) (p : formula L) : p.sf.rew s⁺¹ = (p.rew s).sf :=
by { simp[formula.sf, formula.nested_rew] }

lemma proper_theory_sf {n : ℕ} {T : theory L} (pp : proper_at n T) :
  proper_at (n+1) ⇑T := λ p s h,
by { simp, cases h with p hyp_p,
     show p.sf.rew (s^n)⁺¹ ∈ ⇑T, simp[formula.sf_rew_sf_eq],
     refine theory.sf.intro (pp _ _ hyp_p) }

instance properc_theory_sf {n : ℕ} {T : theory L} [pp : proper n T] :
  proper (n+1) (⇑T) := ⟨
by { have : proper_at n T, from @proper.proper L n T pp,
     have : proper_at (n+1) ⇑T, from proper_theory_sf this, exact this }⟩

lemma proper_theory_sf_itr {n : ℕ} {T : theory L} (pp : proper_at n T) : ∀ m,
  proper_at (n+m) (T^m)
| 0     := by { simp, exact @pp }
| (m+1) := by { simp[←add_assoc], exact proper_theory_sf (proper_theory_sf_itr m) }

instance properc_theory_sf_itr {T : theory L} [pp : proper 0 T] {n} :
  proper n (T^n) := ⟨by { have := proper_theory_sf_itr pp.proper n, simp* at* }⟩ 

lemma closed_proper {T : theory L} [cl : closed_theory T] : proper_at 0 T :=
λ p s h, by { simp[@closed_theory.cl _ _ cl _ h], exact h }

@[simp] lemma closed_theory_sf_eq {T : theory L} [cl : closed_theory T] : ⇑T = T :=
by { ext p, refine ⟨λ hyp, _, λ hyp, _⟩, cases hyp with p hyp_p,
     simp[formula.sentence_rew (closed_theory.cl hyp_p), hyp_p],
     rw ← (formula.sentence_sf (closed_theory.cl hyp)), refine theory.sf.intro hyp }

lemma sf_dsb (T : theory L) (p : formula L) : ⇑T+{p.sf} = ⇑(T+{p}) :=
begin
  ext x, split; intros h,
  { cases h with h hx, refine theory.sf.intro theory.add.new,
    cases hx with p hp, refine theory.sf.intro (theory.add.old hp) },
  { cases h with q hq, cases hq with _ hq, refine theory.add.new,
    refine theory.add.old (theory.sf.intro hq) }
end

def theory.th (T : theory L) : theory L := {p | T ⊢̇ p}

def conjunction : list (formula L) → formula L
| []        := ⊤̇
| (p :: ps) := p ⩑ conjunction ps

lemma ss_le {U : ℕ → theory L} (hyp : ∀ s, U s ⊆ U (s+1)) : ∀ {s₁ s₂}, s₁ ≤ s₂ → U s₁ ⊆ U s₂ :=
by { intros s₁, suffices : ∀ t, U s₁ ⊆ U (s₁ + t),
      { intros s₂ eqn, have := this (s₂ - s₁),
        rw (show s₁ + (s₂ - s₁) = s₂, from nat.add_sub_of_le eqn) at this, exact this },
      intros t, induction t with t IH, simp, rw[nat.add_succ],  refine λ x hx, hyp _ (IH hx) }

def formula.equiv (T : theory L) (p₁ p₂ : formula L) : Prop := T ⊢̇ p₁ ↔̇ p₂

def term.equiv (T : theory L) (t₁ t₂ : term L) : Prop := T ⊢̇ t₁ =̇ t₂

namespace provable
variables (T : theory L)

@[simp] lemma pp (p) : T ⊢̇ p →̇ p :=
begin
  have l₀ : T ⊢̇ (p →̇ (p →̇ p) →̇ p) →̇ (p →̇ p →̇ p) →̇ p →̇ p, simp,
  have l₁ : T ⊢̇ p →̇ (p →̇ p) →̇ p, simp,
  have l₂ : T ⊢̇ (p →̇ p →̇ p) →̇ p →̇ p, refine l₀.MP l₁,
  have l₃ : T ⊢̇ p →̇ p →̇ p, simp,
  refine l₂.MP l₃
end

@[simp] lemma top : T ⊢̇ ⊤̇ := by simp[formula.top]; exact GE (by simp)

@[simp] lemma add (p) : T+{p} ⊢̇ p :=
AX (theory.add.new)

variables {T}

lemma GE_cl {T : theory L} [closed_theory T] {p} (h : T ⊢̇ p) : T ⊢̇ ∀̇p :=
by { apply provable.GE, simp[h] }

@[simp] lemma imp_r {p} (h : T ⊢̇ p) (q) : T ⊢̇ q →̇ p :=
by { have : T ⊢̇ p →̇ q →̇ p, simp,
     exact this.MP h }

lemma imp_trans {p q r} : (T ⊢̇ p →̇ q) → (T ⊢̇ q →̇ r) → (T ⊢̇ p →̇ r) := λ h₁ h₂,
begin
  have l₁ : T ⊢̇ (p →̇ q →̇ r) →̇ (p →̇ q) →̇ (p →̇ r), simp,  
  have l₂ : T ⊢̇ (p →̇ q →̇ r), simp[h₂],
  have l₃ : T ⊢̇ (p →̇ q) →̇ (p →̇ r), from l₁.MP l₂,
  exact l₃.MP h₁
end

lemma nfal_eq : ∀ (n) (p : formula L), nfal (∀̇p) n = ∀̇(nfal (p) n)
| 0     p := rfl
| (n+1) p := by simp; exact nfal_eq n p

lemma GE_itr : ∀ {n p}, T^n ⊢̇ p → T ⊢̇ nfal p n
| 0     p h := by simp* at*
| (n+1) p h := by { simp[←nfal_eq] at*, exact GE_itr (GE h) }

lemma subst_itr : ∀ (n) (p : formula L) (s : ℕ → term L),
  T ⊢̇ nfal p n →̇ p.rew (λ x, if x < n then s x else #(x-n))
| 0 p s := by simp
| (n+1) p s := by { simp,
    have lmm₁ : T ⊢̇ ∀̇(nfal p n) →̇ nfal (p.rew $ ₛ[s n]^n) n,
    { have := @provable.q1 _ T (nfal p n) (s n), simp[formula.nfal_rew] at this,
      have eqn : (λ m, ite (m < n) #m ((ₛ[s n] (m - n)).rew (λ x, #(x+n)))) = ₛ[s n]^n,
      { ext m,
        by_cases C : m < n; simp[C],
        have C₁ : n = m ∨ n < m, from eq_or_lt_of_le (not_lt.mp C),
        cases C₁, { simp[C₁] },
        { have : m - n > 0, exact nat.sub_pos_of_lt C₁,
          rw[nat.pos_succ this], simp[C₁, this], 
          simp[nat.pos_pred_add(nat.succ_le_iff.mpr this), nat.sub_add_cancel (le_of_lt C₁)] } },
      simp[eqn] at this,
      exact this },
    have s' := s,
    have lmm₂ := subst_itr n (p.rew $ ₛ[s n]^n) s,
    simp[formula.nested_rew] at lmm₂,
    have : (λ x, vecterm.rew (λ x, ite (x < n) (s x) #(x - n)) (ₛ[s n]^n $ x)) =
      (λ x, ite (x < n + 1) (s x) #(x - (n + 1))),
    { ext x, have C : x < n ∨ x = n ∨ n < x, from trichotomous _ _,
      cases C,
      { simp[C, nat.lt.step C] }, cases C; simp[C],
      { have eqn₁ : n ≤ x - 1, from nat.le_pred_of_lt C,
        have eqn₂ : n + 1 ≤ x, from nat.succ_le_iff.mpr C,
        have := not_lt.mpr eqn₁,
        simp[not_lt.mpr eqn₁, not_lt.mpr eqn₂, nat.sub_sub, add_comm 1 n] } },
    simp[this] at lmm₂,
    exact lmm₁.imp_trans lmm₂ }

lemma inclusion {p} (h : T ⊢̇ p) : ∀ {U}, T ⊆ U → U ⊢̇ p :=
begin
  induction h with T p hyp_p IH T p q hyp_pq hyp_p IH₁ IH₂ T p hyp_p; try { simp },
  { intros U hyp, refine GE (IH (λ x h, _)), cases h with p hp,
    refine theory.sf.intro _, exact hyp hp },
  { intros U hyp, exact (IH₁ hyp).MP (IH₂ hyp) },
  { intros U hyp, exact AX (hyp hyp_p) }
end

@[simp] lemma weakening {q} (h : T ⊢̇ q) (p) : T+{p} ⊢̇ q :=
inclusion h (λ x h, theory.add.old h)

private lemma delete_imply {p} (h : T ⊢̇ p) : ∀ q, T \ {q} ⊢̇ q →̇ p :=
begin
  induction h with T p hyp_p IH T p₁ p₂ hyp_p₁₂ hyp_p₁ IH₁ IH₂ T p hyp_p;
    try { intros q, apply imp_r, simp }; intros q,
  { have IH : ⇑T \ {q.sf} ⊢̇ q.sf →̇ p := IH q.sf,
    have lmm₁ : T \ {q} ⊢̇ q →̇ ∀̇ q.sf, { simp },
    have lmm₂ : T \ {q} ⊢̇ ∀̇ q.sf →̇ ∀̇ p,
    { suffices : T \ {q} ⊢̇ ∀̇(q.sf →̇ p),
      { have lmm : T \ {q} ⊢̇ ∀̇(q.sf →̇ p) →̇ ∀̇ q.sf →̇ ∀̇ p, simp,
        exact lmm.MP this },
      refine GE (inclusion IH (λ x h, _)), 
      rcases h with ⟨h, neq⟩, rcases h with ⟨p', h'⟩,
      refine theory.sf.intro ⟨h', λ c, _⟩, simp at c,
      rw c at neq, exact neq rfl },
    exact lmm₁.imp_trans lmm₂ },
  { have : T \ {q} ⊢̇ (q →̇ p₁ →̇ p₂) →̇ (q →̇ p₁) →̇ (q →̇ p₂), simp, 
    have : T \ {q} ⊢̇ (q →̇ p₁) →̇ q →̇ p₂, from this.MP (IH₁ _),
    exact this.MP (IH₂ _) },
  { by_cases eqn : p = q,
    { simp[eqn] },
    { have : T \ {q} ⊢̇ p, from AX ⟨hyp_p, eqn⟩,
      simp[this] } }
end

theorem deduction {p q} : (T+{p} ⊢̇ q) ↔ (T ⊢̇ p →̇ q) :=
⟨λ h, by { have : (T+{p}) \ {p} ⊢̇ p →̇ q, from delete_imply h p,
           refine inclusion this (λ x h, _), rcases h with ⟨h, neq⟩,
           cases h; simp* at*, },
 λ h, by { have : T+{p} ⊢̇ p →̇ q, from weakening h p,
           exact this.MP (by simp) }⟩

theorem proof_compact : ∀ {T : ℕ → theory L}, (∀ s, T s ⊆ T (s+1)) →
  ∀ {p}, {p | ∃ s, T s p} ⊢̇ p → ∃ s, T s ⊢̇ p :=
begin
  suffices : ∀ {p} {U : theory L}, U ⊢̇ p → ∀ {T : ℕ → theory L},
    (∀ s, T s ⊆ T (s+1)) → U ⊆ {p | ∃ s, T s p} → ∃ s, T s ⊢̇ p,
  { refine λ T hyp p h, this h hyp (λ x hx, hx) },
  intros p U h,
  induction h,
  case fopl.provable.GE : T p h IH
  { intros U hyp ss,
    let U' := λ s, ⇑(U s),
    have hyp' : ∀ s, U' s ⊆ U' (s + 1),
    { simp[U'], intros s p hyp_p, cases hyp_p with p' hyp_q', refine theory.sf.intro (hyp _ hyp_q') },
    have ss' : ⇑T ⊆ {p : formula L | ∃ s, U' s p},
    { intros q hyp_q, cases hyp_q with q' hyp_q', rcases (ss hyp_q') with ⟨s, hyp_s⟩,
      refine ⟨s, theory.sf.intro hyp_s⟩ },
    have : ∃ s, U' s ⊢̇ p, from IH hyp' ss', rcases this with ⟨s, h⟩,
    refine ⟨s, provable.GE h⟩ },
  case fopl.provable.MP : T p q hyp_pq hyp_p IH₁ IH₂
  { intros U hyp ss,
    have : ∃ s, U s ⊢̇ p →̇ q, from IH₁ hyp ss, rcases this with ⟨s₁, lmm₁⟩,
    have : ∃ s, U s ⊢̇ p, from IH₂ hyp ss, rcases this with ⟨s₂, lmm₂⟩,
    refine ⟨max s₁ s₂, _⟩,
    have lmm₁ : U (max s₁ s₂) ⊢̇ p →̇ q, from provable.inclusion lmm₁ (ss_le hyp (by simp)),
    have lmm₂ : U (max s₁ s₂) ⊢̇ p, from provable.inclusion lmm₂ (ss_le hyp (by simp)),
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

@[simp] lemma dne (p) : T ⊢̇ ¬̇¬̇p →̇ p :=
begin
  have lmm₁ : T+{¬̇¬̇p} ⊢̇ ¬̇¬̇p, simp,   
  have lmm₂ : T+{¬̇¬̇p} ⊢̇ ¬̇¬̇p →̇ ¬̇¬̇¬̇¬̇p →̇ ¬̇¬̇p, simp,
  have lmm₃ : T+{¬̇¬̇p} ⊢̇ ¬̇¬̇¬̇¬̇p →̇ ¬̇¬̇p, from lmm₂.MP lmm₁,
  have lmm₄ : T+{¬̇¬̇p} ⊢̇ (¬̇¬̇¬̇¬̇p →̇ ¬̇¬̇p) →̇ ¬̇p →̇ ¬̇¬̇¬̇p, simp,
  have lmm₅ : T+{¬̇¬̇p} ⊢̇ ¬̇p →̇ ¬̇¬̇¬̇p, from lmm₄.MP lmm₃,
  have lmm₆ : T+{¬̇¬̇p} ⊢̇ (¬̇p →̇ ¬̇¬̇¬̇p) →̇ ¬̇¬̇p →̇ p, simp,
  have lmm₇ : T+{¬̇¬̇p} ⊢̇ ¬̇¬̇p →̇ p, from lmm₆.MP lmm₅,
  have lmm₈ : T+{¬̇¬̇p} ⊢̇ p, from lmm₇.MP lmm₁,
  exact deduction.mp lmm₈  
end

@[simp] lemma dni (p) : T ⊢̇ p →̇ ¬̇¬̇p :=
by { have : T ⊢̇ (¬̇¬̇¬̇p →̇ ¬̇p) →̇ p →̇ ¬̇¬̇p, simp,
     exact this.MP (by simp) }

@[simp] lemma dn_iff {p} : T ⊢̇ ¬̇¬̇p ↔ T ⊢̇ p :=
⟨λ h, (show T ⊢̇ ¬̇¬̇p →̇ p, by simp).MP h, λ h,(show T ⊢̇ p →̇ ¬̇¬̇p, by simp).MP h⟩

@[simp] lemma dn1_iff {p q} : (T ⊢̇ ¬̇¬̇p →̇ q) ↔ (T ⊢̇ p →̇ q) :=
⟨(dni _).imp_trans, (dne _).imp_trans⟩

@[simp] lemma dn2_iff {p q} : (T ⊢̇ p →̇ ¬̇¬̇q) ↔ (T ⊢̇ p →̇ q) :=
⟨λ h, h.imp_trans (dne _), λ h, h.imp_trans (dni _)⟩

lemma explosion {p} (h₁ : T ⊢̇ p) (h₂ : T ⊢̇ ¬̇p) {q} : T ⊢̇ q :=
begin
  have : T ⊢̇ ¬̇p →̇ ¬̇q →̇ ¬̇p, simp,
  have : T ⊢̇ ¬̇q →̇ ¬̇p, from this.MP h₂,
  have : T ⊢̇ p →̇ q, from (show T ⊢̇ (¬̇q →̇ ¬̇p) →̇ p →̇ q, by simp).MP this,
  exact this.MP h₁
end

lemma contrapose {p q} : (T ⊢̇ ¬̇p →̇ ¬̇q) ↔ (T ⊢̇ q →̇ p) :=
⟨λ h, (show T ⊢̇ (¬̇p →̇ ¬̇q) →̇ q →̇ p, by simp).MP h, λ h,
  by { refine (show T ⊢̇ (¬̇¬̇q →̇ ¬̇¬̇p) →̇ ¬̇p →̇ ¬̇q, by simp).MP _,
       have : T ⊢̇ ¬̇¬̇q →̇ p, from (show T ⊢̇ ¬̇¬̇q →̇ q, by simp).imp_trans h,
       exact this.imp_trans (show T ⊢̇ p →̇ ¬̇¬̇p, by simp) }⟩

lemma neg_hyp {p} (h : T ⊢̇ p →̇ ¬̇p) : T ⊢̇ ¬̇p :=
begin
  have : T+{p} ⊢̇ ¬̇(p →̇ ¬̇p),
  { have lmm₁ : T+{p} ⊢̇ p, simp,
    have lmm₂ : T+{p} ⊢̇ ¬̇p, from (weakening h _).MP lmm₁,
    exact explosion lmm₁ lmm₂ },
  have : T ⊢̇ p →̇ ¬̇(p →̇ ¬̇p), from deduction.mp this,
  have : T ⊢̇ (p →̇ ¬̇p) →̇ ¬̇p, from (dni _).imp_trans (contrapose.mpr this),
  exact this.MP h
end

lemma raa {p} (q) (h₁ : T+{p} ⊢̇ q) (h₂ : T+{p} ⊢̇ ¬̇q) : T ⊢̇ ¬̇p :=
neg_hyp (deduction.mp (explosion h₁ h₂))

@[simp] lemma hyp_bot (p) : T ⊢̇ ⊥̇ →̇ p :=
by { simp[formula.bot], apply deduction.mp, refine explosion (show T+{¬̇⊤̇} ⊢̇ ⊤̇, by simp) (add _ _) }

@[simp] lemma and {p q} : (T ⊢̇ p ⩑ q) ↔ (T ⊢̇ p ∧ T ⊢̇ q) :=
⟨λ h, by { simp[formula.and] at h, split,
   { have : T+{¬̇p}+{p} ⊢̇ ¬̇q, 
     from explosion (show T+{¬̇p}+{p} ⊢̇ p, by simp) (show T+{¬̇p}+{p} ⊢̇ ¬̇p, by simp),
     have : T ⊢̇ ¬̇p →̇ p →̇ ¬̇q, from (deduction.mp (deduction.mp this)),
     have : T ⊢̇ ¬̇(p →̇ ¬̇q) →̇ p := (contrapose.mpr this).imp_trans (by simp),
     exact this.MP h },
   { have : T ⊢̇ ¬̇q →̇ p →̇ ¬̇q, simp,
     have : T ⊢̇ ¬̇(p →̇ ¬̇q) →̇ q, from (contrapose.mpr this).imp_trans (by simp),
     exact this.MP h } },
 λ h, by {simp[formula.and], rcases h with ⟨h₁, h₂⟩,
   show T ⊢̇ ¬̇(p →̇ ¬̇q),
   have : T+{p →̇ ¬̇q} ⊢̇ ¬̇q, from (add _ _).MP (by simp[h₁]),
   have : T ⊢̇ (p →̇ ¬̇q) →̇ ¬̇q, from deduction.mp this,
   have : T ⊢̇ q →̇ ¬̇(p →̇ ¬̇q), from (dni _).imp_trans (contrapose.mpr this),
   exact this.MP h₂ }⟩

@[simp] lemma iff {p q} : (T ⊢̇ p ↔̇ q) ↔ (T ⊢̇ p →̇ q ∧ T ⊢̇ q →̇ p) :=
by simp[formula.iff]

@[simp] lemma neg_imp {p q} : (T ⊢̇ ¬̇(p →̇ q)) ↔ (T ⊢̇ p ⩑ ¬̇q) :=
begin
  simp only [formula.and], split; intros h,
  { apply raa (p →̇ q),
    { have : T+{p →̇ ¬̇¬̇q} ⊢̇ p →̇ ¬̇¬̇q, from add _ _, simp* at * },
    { simp[h] } },
  { apply raa (p →̇ ¬̇¬̇q); simp[h] }
end

lemma or_l (p q) : T ⊢̇ p →̇ p ⩒ q :=
by simp[formula.or]; refine deduction.mp (deduction.mp (explosion (show T+{p}+{¬̇p} ⊢̇ p, by simp) (by simp)))

lemma or_r (p q) : T ⊢̇ q →̇ p ⩒ q :=
by simp[formula.or]; refine deduction.mp (weakening h _)

lemma hyp_or {p₁ p₂ q} : (T ⊢̇ p₁ →̇ q) → (T ⊢̇ p₂ →̇ q) → (T ⊢̇ p₁ ⩒ p₂ →̇ q) := λ h₁ h₂,
begin
  simp[formula.or], apply contrapose.mp, refine deduction.mp _, simp,
  refine ⟨deduction.mpr (contrapose.mpr h₁), deduction.mpr (contrapose.mpr h₂)⟩, 
end

lemma hyp_and_left {p₁ p₂ q} : (T ⊢̇ p₁ →̇ q) → (T ⊢̇ p₁ ⩑ p₂ →̇ q) := λ h,
begin
  have : T+{p₁ ⩑ p₂} ⊢̇ p₁, { have : T+{p₁ ⩑ p₂} ⊢̇ p₁ ⩑ p₂, from add _ _, simp* at * },
  refine deduction.mp ((show T+{p₁ ⩑ p₂} ⊢̇ p₁ →̇ q, by simp[h]).MP this)
end

lemma hyp_and_right {p₁ p₂ q} : (T ⊢̇ p₂ →̇ q) → (T ⊢̇ p₁ ⩑ p₂ →̇ q) := λ h,
begin
  have : T+{p₁ ⩑ p₂} ⊢̇ p₂, { have : T+{p₁ ⩑ p₂} ⊢̇ p₁ ⩑ p₂, from add _ _, simp* at * },
  refine deduction.mp ((show T+{p₁ ⩑ p₂} ⊢̇ p₂ →̇ q, by simp[h]).MP this)
end

lemma axiom_and {p₁ p₂ q} : T+{p₁ ⩑ p₂} ⊢̇ q ↔ T+{p₁}+{p₂} ⊢̇ q :=
⟨λ h,
 by { have lmm₁ : T+{p₁}+{p₂} ⊢̇ p₁ ⩑ p₂, by simp,
      have lmm₂ : T+{p₁}+{p₂} ⊢̇ p₁ ⩑ p₂ →̇ q, simp[deduction.mp h],
      exact lmm₂.MP lmm₁ },
 λ h,
 by { have lmm₁ : T+{p₁ ⩑ p₂} ⊢̇ p₁ →̇ p₂ →̇ q, simp[deduction.mp (deduction.mp h)],
      have lmm₂ : T+{p₁ ⩑ p₂} ⊢̇ p₁ ⩑ p₂, from add _ _, simp at lmm₂,
      exact (lmm₁.MP lmm₂.1).MP lmm₂.2 }  ⟩

lemma conjunction_mem {P : list (formula L)} : ∀ {p}, p ∈ P → ∅ ⊢̇ conjunction P →̇ p :=
begin
  induction P with p P IH; simp[conjunction],
  have lmm₁ : ∅ ⊢̇ p ⩑ conjunction P →̇ p, from hyp_and_left (by simp),
  have lmm₂ : ∀ q, q ∈ P → ∅ ⊢̇ p ⩑ conjunction P →̇ q, from λ q hq, hyp_and_right (IH hq),
  refine ⟨lmm₁, lmm₂⟩
end

lemma conjunction_inclusion {P Q : list (formula L)} : 
  Q ⊆ P → ∅ ⊢̇ conjunction P →̇ conjunction Q :=
begin
  induction Q with q Q IH; simp[conjunction],
  intros hyp_q hyp_Q,
  have lmm₁ : ∅+{conjunction P} ⊢̇ q, from deduction.mpr (conjunction_mem hyp_q),  
  have lmm₂ : ∅+{conjunction P} ⊢̇ conjunction Q, from deduction.mpr (IH hyp_Q),
  refine deduction.mp (and.mpr ⟨lmm₁, lmm₂⟩)
end

private lemma conjunction_sf (P₀ : list (formula L)) : (∀ p, p ∈ P₀ → ⇑T p) →
  ∃ P, (conjunction P).sf = conjunction P₀ ∧ (∀ p, p ∈ P → T p) :=
begin
  induction P₀ with p₀ P₀ IHl, { refine λ _, ⟨[], _⟩, simp[conjunction] },
  { intros hyp,
    have : ∀ p, p ∈ P₀ → ⇑T p,
    { intros p hyp_p, refine hyp _ _, simp[hyp_p] },
    rcases IHl this with ⟨P, hyp_P⟩,
    have := hyp p₀ (by simp),
    cases this with p hyp_p,
    have lmm₁ : (conjunction (p :: P)).sf = conjunction (p.sf :: P₀),
    { simp[conjunction, hyp_P] },
    have lmm₂ : ∀ (q : formula L), q ∈ (p :: P) → T q,
    { simp, refine ⟨hyp_p, hyp_P.2⟩ },
    refine ⟨p :: P, lmm₁, lmm₂⟩ }
end

theorem proof_conjunction {T : theory L} {p} :
  T ⊢̇ p → ∃ P : list (formula L), (∀ p, p ∈ P → T p) ∧ ∅ ⊢̇ conjunction P →̇ p := λ h,
begin
  induction h,
  case fopl.provable.GE : T p hyp IH
  { rcases IH with ⟨P₀, hyp_P₀, prov⟩,
    have : ∃ P, (conjunction P).sf = conjunction P₀ ∧ ∀ p, p ∈ P → T p, from conjunction_sf _ hyp_P₀,
    rcases this with ⟨P, eqn, hyp_P⟩,
    have : ∅ ⊢̇ conjunction P →̇ ∀̇p,
    { refine deduction.mp (GE _),
      rw [←sf_dsb, eqn], refine deduction.mpr (inclusion prov (λ x hx, _)), cases hx },
    refine ⟨P, hyp_P, this⟩ },
  case fopl.provable.MP : T p q hyp_pq hyp_p IH₁ IH₂
  { rcases IH₁ with ⟨P₁, IH₁, prov₁⟩, rcases IH₂ with ⟨P₂, IH₂, prov₂⟩,
    refine ⟨P₁ ++ P₂, _, _⟩,
    { simp, intros p h, cases h, refine IH₁ _ h, refine IH₂ _ h },
    { have : ∅+{conjunction (P₁ ++ P₂)} ⊢̇ conjunction P₂, from deduction.mpr (conjunction_inclusion (by simp)),
      have lmm₁ : ∅+{conjunction (P₁ ++ P₂)} ⊢̇ p, from (show _ ⊢̇ conjunction P₂ →̇ p, by simp[prov₂]).MP this,
      have : ∅+{conjunction (P₁ ++ P₂)} ⊢̇ conjunction P₁, from deduction.mpr (conjunction_inclusion (by simp)),
      have lmm₂ : ∅+{conjunction (P₁ ++ P₂)} ⊢̇ p →̇ q,
      from (show _ ⊢̇ conjunction P₁ →̇ p →̇ q, by simp[prov₁]).MP this,
      refine deduction.mp (lmm₂.MP lmm₁) } },
  case fopl.provable.AX : T p hyp_p
  { refine ⟨[p], _⟩, simp[conjunction],
    have : ∅ ⊢̇ p ⩑ ⊤̇ →̇ p,
    { apply deduction.mp, have : ∅+{p ⩑ ⊤̇} ⊢̇ p ⩑ ⊤̇, from add _ _ , simp* at* },
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

lemma fal_subst {p} (h : T ⊢̇ ∀̇p) (t) : T ⊢̇ p.rew ₛ[t] :=
(show T ⊢̇ ∀̇p →̇ p.rew ₛ[t], by simp).MP h

lemma add_sf (p) : ⇑(T +{∀̇p}) ⊢̇ p :=
by { have : ⇑(T +{∀̇p}) ⊢̇ (∀̇p).sf, rw ← sf_dsb, simp,simp[formula.sf] at this,
     have := fal_subst this #0, simp[formula.nested_rew] at this,
     have eqn : (λ x, vecterm.rew ₛ[#0] ((λ x, #(x + 1))⁺¹ x)) = (idvar : ℕ → vecterm L 0),
      { funext n, cases n; simp[vecterm.rew] }, simp [eqn] at this, exact this }

private lemma rgerg {P : list (formula L)} : (∀ p, p ∈ P → T p) → T ⊢̇ conjunction P :=
begin
  induction P with p P IH; simp[conjunction],
  refine λ hyp_p hyp, ⟨AX hyp_p, IH hyp⟩,
end

lemma cl_prove_rew [cl : closed_theory T] : ∀ {p : formula L}, T ⊢̇ p → ∀ s, T ⊢̇ p.rew s :=
begin
  suffices : ∀ {p : formula L} {T}, T ⊢̇ p → closed_theory T → ∀ s, T ⊢̇ p.rew s,
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
    simp[formula.rew, vecterm.sf],
    have : p.sf.rew s⁺¹ = (p.rew s).sf,
    { simp[formula.sf, formula.rew, formula.nested_rew] },
    simp[this] },
  { simp[formula.rew] },
  { simp[formula.rew] },
  { simp[formula.rew] },
  { simp[formula.rew, vecterm.rew] },
  { simp[formula.rew] },
end

lemma pp_prove_rew {n} (pp : proper_at n T) :
  ∀ {p : formula L}, T ⊢̇ p → ∀ s, T ⊢̇ p.rew (rewriting_sf_itr s n) :=
begin
  suffices : ∀ {p : formula L} {T},
    T ⊢̇ p → ∀ {n}, proper_at n T → ∀ s, T ⊢̇ p.rew (rewriting_sf_itr s n),
  { refine λ p h s, this h @pp _ },
  intros p T h,
  induction h,
  case GE : T p hyp IH
  { intros n pp s,
    refine GE _, refine @IH (n+1) (@proper_theory_sf _ _ _ @pp) s },
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
    simp[formula.rew, vecterm.sf],
    simp[formula.sf_rew_sf_eq] },
  { simp[formula.rew] },
  { simp[formula.rew] },
  { simp[formula.rew] },
  { simp[formula.rew, vecterm.rew] },
  { simp[formula.rew] },
end

lemma ppc_prove_rew (n) [pp : proper n T] :
  ∀ {p : formula L}, T ⊢̇ p → ∀ s, T ⊢̇ p.rew (rewriting_sf_itr s n) := @pp_prove_rew _ _ n pp.proper

lemma ppc0_prove_rew [pp : proper 0 T] :
  ∀ {p : formula L}, T ⊢̇ p → ∀ s, T ⊢̇ p.rew s := @pp_prove_rew _ _ 0 pp.proper

lemma cl_fal_elim [closed_theory T] {p} : T ⊢̇ ∀̇p ↔ T ⊢̇ p :=
⟨λ h, by { have : T ⊢̇ (∀̇p).rew (λ n, #(n+1)),  from cl_prove_rew h _,
           have lmm : T ⊢̇ (p.rew (#0 ^ˢ λ n, #(n+2))).rew ₛ[#0], from this.fal_subst #0,
           have : (p.rew (#0 ^ˢ λ n, #(n+2))).rew ₛ[#0] = p,
           { suffices : (p.rew (#0 ^ˢ λ n, #(n+2))).rew ₛ[#0] = p.rew idvar, simp* at*,
             simp[formula.nested_rew, -formula.rew_idvar], congr,
             ext n, cases n; simp[vecterm.rew], },
           simp[this] at lmm, exact lmm },
 λ h, GE $ by simp[h]⟩

private lemma conjunction_rew_eq : ∀ (P : list (formula L)) (s),
  (conjunction P).rew s = conjunction (P.map (λ p, p.rew s))
| []       _ := by simp[conjunction, formula.rew]
| (p :: P) s := by simp[conjunction, formula.rew, conjunction_rew_eq P]

lemma conjunction_provable : ∀ {P : list (formula L)} (h : ∀ p, p ∈ P → T ⊢̇ p), T ⊢̇ conjunction P
| []       h := by simp[conjunction]
| (p :: P) h := by { simp[conjunction],
    have lmm₁ : T ⊢̇ p, { refine h _ _, simp },
    have lmm₂ : T ⊢̇ conjunction P, { refine conjunction_provable (λ p hyp, h _ _), simp, right, exact hyp },
    refine ⟨lmm₁, lmm₂⟩ }

lemma sf_sf {p : formula L} : ⇑T ⊢̇ p.sf ↔ T ⊢̇ p :=
⟨λ h, by { have := (GE h).fal_subst #0, simp* at* },
 λ h, by { have : ∃ P, (∀ p, p ∈ P → p ∈ T) ∧ ∅ ⊢̇ conjunction P →̇ p,
  from proof_conjunction h, rcases this with ⟨P, hyp_P, prov⟩,
  have lmm₁ : ⇑T ⊢̇ conjunction (P.map formula.sf),
  { refine conjunction_provable (λ p hyp, AX _), simp at hyp, rcases hyp with ⟨p', p'_mem, rfl⟩,
    refine theory.sf.intro (hyp_P p' p'_mem) },
  have lmm₂ : ⇑T ⊢̇ conjunction (P.map formula.sf) →̇ p.sf,
  { have : ∅ ⊢̇ (conjunction P).sf →̇ p.sf, from cl_prove_rew prov _,
    simp[conjunction_rew_eq, formula.sf] at this,
    refine inclusion this (λ p h, _), exfalso, exact h },
  refine lmm₂.MP lmm₁ }⟩

lemma sf_itr_sf_itr : ∀ {n} {p : formula L},
  T^n ⊢̇ p.rew (λ x, #(x+n)) ↔ T ⊢̇ p
| 0     p := by simp
| (n+1) p := by { simp[←add_assoc],
    have : p.rew (λ x, #(x + n + 1)) = (p.rew (λ x, #(x+n))).sf,
    { simp[formula.sf, formula.nested_rew] }, simp[this, sf_sf],
    exact sf_itr_sf_itr }

lemma use {p : formula L} (t) (h : T ⊢̇ p.rew ₛ[t]) : T ⊢̇ Ėp :=
begin
  simp[formula.ex],
  refine raa (p.rew ₛ[t]) (by simp[h]) (deduction.mpr _),
  have : ¬̇p.rew ₛ[t] = (¬̇p).rew ₛ[t] := rfl,
  rw[this], refine provable.q1
end

lemma eq_symm : ∀ {t u}, (T ⊢̇ t =̇ u) ↔ (T ⊢̇ u =̇ t) :=
begin
  suffices : ∀ t u, (T ⊢̇ t =̇ u) → (T ⊢̇ u =̇ t),
  { intros t u, refine ⟨this _ _, this _ _⟩ },
  intros t u h,
  have : T ⊢̇ t =̇ u →̇ u =̇ t, simp,
  refine this.MP h
end

lemma eq_trans {t₁ t₂ t₃} : (T ⊢̇ t₁ =̇ t₂) → (T ⊢̇ t₂ =̇ t₃) → (T ⊢̇ t₁ =̇ t₃) := λ h₁ h₂,
by { have : T ⊢̇ t₁ =̇ t₂ →̇ t₂ =̇ t₃ →̇ t₁ =̇ t₃, simp, exact (this.MP h₁).MP h₂ }

lemma equal_rew_equals : ∀ {n} (v : vecterm L n) (s₁ s₂ : ℕ → term L) (e : ∀ n, T ⊢̇ s₁ n =̇ s₂ n),
  T ⊢̇ v.rew s₁ ≡̇ v.rew s₂
| _ (vecterm.cons t v) _ _ eqn := by simp[vecterm.rew];
    exact ⟨equal_rew_equals t _ _ eqn, equal_rew_equals v _ _ eqn⟩
| _ (#n)               _ _ eqn := by simp[vecterm.rew]; exact eqn _
| _ (vecterm.const c)  _ _ eqn := by simp[vecterm.rew]
| _ (vecterm.app f v)  _ _ eqn := by simp[vecterm.rew];
    exact provable.e4.MP (equal_rew_equals v _ _ eqn)

lemma equal_rew_equals_term : ∀ (t : term L) (s₁ s₂ : ℕ → term L) (e : ∀ n, T ⊢̇ s₁ n =̇ s₂ n),
  T ⊢̇ t.rew s₁ =̇ t.rew s₂ := equal_rew_equals

lemma equal_fal_subst_equals {n} (v : vecterm L n) {t₁ t₂} (h : T ⊢̇ t₁ =̇ t₂) :
  T ⊢̇ v.rew (t₁ ^ˢ idvar) ≡̇ v.rew (t₂ ^ˢ idvar) :=
by { refine equal_rew_equals v _ _ (λ n, _), { cases n; simp[h] } }

lemma equal_rew_iff (p : formula L) : ∀ {s₁ s₂ : ℕ → term L} {T : theory L} (eqn : ∀ n, T ⊢̇ s₁ n =̇ s₂ n),
  T ⊢̇ p.rew s₁ ↔̇ p.rew s₂ :=
begin
  induction p,
  case const { by simp[formula.rew] },
  case app : n p v { intros, simp[formula.rew],
    exact ⟨(provable.e5.MP (equal_rew_equals v _ _ eqn)),
      (provable.e5.MP (equal_rew_equals v _ _ (λ n, eq_symm.mp $ eqn n)))⟩ },
  case equal : t₁ t₂ { intros, simp[formula.rew],
    refine ⟨deduction.mp _, deduction.mp _⟩,
    { have lmm₁ : T+{t₁.rew s₁ =̇ t₂.rew s₁} ⊢̇ t₁.rew s₂ =̇ t₁.rew s₁,
      { refine equal_rew_equals t₁ s₂ s₁ (λ n, eq_symm.mp _), simp[eqn n] },
      have lmm₂ : T+{t₁.rew s₁ =̇ t₂.rew s₁} ⊢̇ t₁.rew s₁ =̇ t₂.rew s₁, { simp },
      have lmm₃ : T+{t₁.rew s₁ =̇ t₂.rew s₁} ⊢̇ t₂.rew s₁ =̇ t₂.rew s₂,
      { refine equal_rew_equals t₂ s₁ s₂ (λ n, _), simp[eqn n]  },
      refine lmm₁.eq_trans (lmm₂.eq_trans lmm₃) },
    { have lmm₁ : T+{t₁.rew s₂ =̇ t₂.rew s₂} ⊢̇ t₁.rew s₁ =̇ t₁.rew s₂,
      { refine equal_rew_equals t₁ s₁ s₂ (λ n, _), simp[eqn n] },
      have lmm₂ : T+{t₁.rew s₂ =̇ t₂.rew s₂} ⊢̇ t₁.rew s₂ =̇ t₂.rew s₂, { simp },
      have lmm₃ : T+{t₁.rew s₂ =̇ t₂.rew s₂} ⊢̇ t₂.rew s₂ =̇ t₂.rew s₁,
      { refine equal_rew_equals t₂ s₂ s₁ (λ n, eq_symm.mp _), simp[eqn n]  },
      refine lmm₁.eq_trans (lmm₂.eq_trans lmm₃) } },
  case imply : p q IH₁ IH₂
  { intros, have IH₁ := IH₁ eqn, have IH₂ := IH₂ eqn,
    simp[formula.rew] at*, split,
    { refine deduction.mp (deduction.mp _), 
      have : T+{p.rew s₁ →̇ q.rew s₁}+{p.rew s₂} ⊢̇ p.rew s₂, simp,
      have : T+{p.rew s₁ →̇ q.rew s₁}+{p.rew s₂} ⊢̇ p.rew s₁, from MP (by simp[IH₁]) this,
      have : T+{p.rew s₁ →̇ q.rew s₁}+{p.rew s₂} ⊢̇ q.rew s₁,
        from MP (show _ ⊢̇ p.rew s₁ →̇ q.rew s₁, by simp) this,
      from MP (by simp[IH₂]) this },
    { refine deduction.mp (deduction.mp _),
      have : T+{p.rew s₂ →̇ q.rew s₂}+{p.rew s₁} ⊢̇ p.rew s₁, simp,
      have : T+{p.rew s₂ →̇ q.rew s₂}+{p.rew s₁} ⊢̇ p.rew s₂, from MP (by simp[IH₁]) this,
      have : T+{p.rew s₂ →̇ q.rew s₂}+{p.rew s₁} ⊢̇ q.rew s₂,
        from MP (show _ ⊢̇ p.rew s₂ →̇ q.rew s₂, by simp) this,
      from MP (by simp[IH₂]) this } },
  case neg : p IH
  { intros, simp[formula.rew] at*,
    refine ⟨contrapose.mpr _, contrapose.mpr _⟩; simp[IH eqn] },
  case fal : p IH
  { intros, simp[formula.rew],
    have := @IH s₁⁺¹ s₂⁺¹ ⇑T
      (λ n, by { cases n; simp, exact sf_sf.mpr (eqn n) }),
    simp at this, 
    refine ⟨provable.q2.MP (GE this.1), provable.q2.MP (GE this.2)⟩ }
end

lemma dummy_fal_quantifir (p) : T ⊢̇ p ↔̇ ∀̇(p.sf) :=
by { have : T ⊢̇ ∀̇p.sf →̇ p.sf.rew ₛ[#0], from provable.q1, simp* at * }

lemma dummy_fal_quantifir_iff {p : formula L} : T ⊢̇ ∀̇(p.sf) ↔ T ⊢̇ p :=
by { have := provable.iff.mp (@dummy_fal_quantifir _ T p), split,
     { refine λ h, (this.2.MP h) },
     { refine λ h, (this.1.MP h) } }

lemma dummy_ex_quantifir (p) : T ⊢̇ p ↔̇ Ė(p.sf) :=
by { simp[formula.ex], split,
     { refine contrapose.mp _, simp, exact (provable.iff.mp (dummy_fal_quantifir ¬̇p)).2 },
     { refine contrapose.mp _, simp, exact (provable.iff.mp (dummy_fal_quantifir ¬̇p)).1 } }

@[simp] lemma T_hyp_eliminate {p} : T ⊢̇ ⊤̇ →̇ p ↔ T ⊢̇ p :=
⟨λ h, by { have : T ⊢̇ ⊤̇, simp, exact h.MP this }, λ h, by simp[h]⟩

end provable

lemma inclusion_le {T U : theory L} : T ⊆ U → T ≤ U := λ hyp p h,
h.inclusion hyp

end fopl