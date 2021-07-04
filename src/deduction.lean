import fopl

universe u

namespace fopl
variables {L : language.{u}}

def theory (L : language) := set (form L)

notation `theory `L:max := set (form L)

inductive theory.sf (T : theory L) : theory L
| intro : ∀ {p : form L}, p ∈ T → theory.sf p.sf

instance : has_emptyc (theory L) := ⟨λ p, false⟩

prefix `⇑`:max := theory.sf

@[simp] def form.equals : ∀ {n}, vecterm L n → vecterm L n → form L
| 0     t₁                   t₂                   := t₁ =̇ t₂
| (n+1) (vecterm.cons t₁ v₁) (vecterm.cons t₂ v₂) := t₁ =̇ t₂ ⩑ form.equals v₁ v₂

infix ` ≡̇ `:90 := form.equals

inductive provable : theory L → form L → Prop
| GE : ∀ {T : theory L} {p}, provable ⇑T p → provable T (Ȧp)
| MP : ∀ {T : theory L} {p q}, provable T (p →̇ q) → provable T p → provable T q
| AX : ∀ {T : theory L} {p}, p ∈ T → provable T p
| p1 : ∀ {T : theory L} {p q}, provable T (p →̇ q →̇ p)
| p2 : ∀ {T : theory L} {p q r}, provable T ((p →̇ q →̇ r) →̇ (p →̇ q) →̇ p →̇ r)
| p3 : ∀ {T : theory L} {p q}, provable T ((¬̇ p →̇ ¬̇ q) →̇ q →̇ p)
| q1 : ∀ {T : theory L} {p t}, provable T (Ȧ p →̇ p.(t))
| q2 : ∀ {T : theory L} {p q}, provable T (Ȧ (p →̇ q) →̇ Ȧ p →̇ Ȧ q)
| q3 : ∀ {T : theory L} {p}, provable T (p →̇ Ȧ p.sf)
| e1 : ∀ {T : theory L} {t}, provable T (t =̇ t)
| e2 : ∀ {T : theory L} {t₁ t₂}, provable T (t₁ =̇ t₂ →̇ t₂ =̇ t₁)
| e3 : ∀ {T : theory L} {t₁ t₂ t₃}, provable T (t₁ =̇ t₂ →̇ t₂ =̇ t₃ →̇ t₁ =̇ t₃)
| e4 : ∀ {T : theory L} {n} {v₁ v₂ : vecterm L n} {f : L.fn (n+1)},
    provable T (v₁ ≡̇ v₂ →̇ vecterm.app f v₁ =̇ vecterm.app f v₂)
| e5 : ∀ {T : theory L} {n} {v₁ v₂ : vecterm L n} {r : L.pr (n+1)},
    provable T (v₁ ≡̇ v₂ →̇ form.app r v₁ →̇ form.app r v₂)

infix ` ⊢̇ `:60 := provable

attribute [simp] provable.p1 provable.p2 provable.p3 provable.q1 provable.q2 provable.q3
  provable.e1 provable.e2 provable.e3 provable.e4 provable.e5

def theory.consistent (T : theory L) : Prop := ¬∃p, (T ⊢̇ p) ∧ (T ⊢̇ ¬̇p) 

inductive theory.add (T : theory L) (p : form L) : theory L 
| new : theory.add p
| old : ∀ {q}, q ∈ T → theory.add q

notation T`+{`:max p`}` := theory.add T p

def theory.le (T U : theory L) : Prop := ∀ p, T ⊢̇ p → U ⊢̇ p
instance : has_le (theory L) := ⟨theory.le⟩

def theory.sentence (T : theory L) : Prop := ∀ {p}, p ∈ T → sentence p

lemma theory_sentence_eq {T : theory L} (h : theory.sentence T) : ⇑T = T :=
by { ext p, refine ⟨λ hyp, _, λ hyp, _⟩, cases hyp with p hyp_p, simp[form.sentence_rew (h hyp_p), hyp_p],
     rw ← (form.sentence_sf (h hyp)), refine theory.sf.intro hyp }

lemma sf_dsb (T : theory L) (p : form L) : ⇑T+{p.sf} = ⇑(T+{p}) :=
begin
  ext x, split; intros h,
  { cases h with h hx, refine theory.sf.intro theory.add.new,
    cases hx with p hp, refine theory.sf.intro (theory.add.old hp) },
  { cases h with q hq, cases hq with _ hq, refine theory.add.new,
    refine theory.add.old (theory.sf.intro hq) }
end

def theory.th (T : theory L) : theory L := {p | T ⊢̇ p}

def conjunction : list (form L) → form L
| []        := ⊤̇
| (p :: ps) := p ⩑ conjunction ps

lemma ss_le {U : ℕ → theory L} (hyp : ∀ s, U s ⊆ U (s+1)) : ∀ {s₁ s₂}, s₁ ≤ s₂ → U s₁ ⊆ U s₂ :=
by { intros s₁, suffices : ∀ t, U s₁ ⊆ U (s₁ + t),
      { intros s₂ eqn, have := this (s₂ - s₁),
        rw (show s₁ + (s₂ - s₁) = s₂, from nat.add_sub_of_le eqn) at this, exact this },
      intros t, induction t with t IH, simp, rw[nat.add_succ],  refine λ x hx, hyp _ (IH hx) }

def form.equiv (T : theory L) (p₁ p₂ : form L) : Prop := T ⊢̇ p₁ ↔̇ p₂

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

@[simp] lemma top : T ⊢̇ ⊤̇ := by simp[form.top]; exact GE (by simp)

@[simp] lemma add (p) : T+{p} ⊢̇ p :=
AX (theory.add.new)

variables {T}

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
    have lmm₁ : T \ {q} ⊢̇ q →̇ Ȧ q.sf, { simp },
    have lmm₂ : T \ {q} ⊢̇ Ȧ q.sf →̇ Ȧ p,
    { suffices : T \ {q} ⊢̇ Ȧ(q.sf →̇ p),
      { have lmm : T \ {q} ⊢̇ Ȧ(q.sf →̇ p) →̇ Ȧ q.sf →̇ Ȧ p, simp,
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
    have ss' : ⇑T ⊆ {p : form L | ∃ s, U' s p},
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
by { simp[form.bot], apply deduction.mp, refine explosion (show T+{¬̇⊤̇} ⊢̇ ⊤̇, by simp) (add _ _) }

@[simp] lemma and {p q} : (T ⊢̇ p ⩑ q) ↔ (T ⊢̇ p ∧ T ⊢̇ q) :=
⟨λ h, by { simp[form.and] at h, split,
   { have : T+{¬̇p}+{p} ⊢̇ ¬̇q, 
     from explosion (show T+{¬̇p}+{p} ⊢̇ p, by simp) (show T+{¬̇p}+{p} ⊢̇ ¬̇p, by simp),
     have : T ⊢̇ ¬̇p →̇ p →̇ ¬̇q, from (deduction.mp (deduction.mp this)),
     have : T ⊢̇ ¬̇(p →̇ ¬̇q) →̇ p := (contrapose.mpr this).imp_trans (by simp),
     exact this.MP h },
   { have : T ⊢̇ ¬̇q →̇ p →̇ ¬̇q, simp,
     have : T ⊢̇ ¬̇(p →̇ ¬̇q) →̇ q, from (contrapose.mpr this).imp_trans (by simp),
     exact this.MP h } },
 λ h, by {simp[form.and], rcases h with ⟨h₁, h₂⟩,
   show T ⊢̇ ¬̇(p →̇ ¬̇q),
   have : T+{p →̇ ¬̇q} ⊢̇ ¬̇q, from (add _ _).MP (by simp[h₁]),
   have : T ⊢̇ (p →̇ ¬̇q) →̇ ¬̇q, from deduction.mp this,
   have : T ⊢̇ q →̇ ¬̇(p →̇ ¬̇q), from (dni _).imp_trans (contrapose.mpr this),
   exact this.MP h₂ }⟩

@[simp] lemma iff {p q} : (T ⊢̇ p ↔̇ q) ↔ (T ⊢̇ p →̇ q ∧ T ⊢̇ q →̇ p) :=
by simp[form.iff]

@[simp] lemma neg_imp {p q} : (T ⊢̇ ¬̇(p →̇ q)) ↔ (T ⊢̇ p ⩑ ¬̇q) :=
begin
  simp only [form.and], split; intros h,
  { apply raa (p →̇ q),
    { have : T+{p →̇ ¬̇¬̇q} ⊢̇ p →̇ ¬̇¬̇q, from add _ _, simp* at * },
    { simp[h] } },
  { apply raa (p →̇ ¬̇¬̇q); simp[h] }
end

lemma or_l (p q) : T ⊢̇ p →̇ p ⩒ q :=
by simp[form.or]; refine deduction.mp (deduction.mp (explosion (show T+{p}+{¬̇p} ⊢̇ p, by simp) (by simp)))

lemma or_r (p q) : T ⊢̇ q →̇ p ⩒ q :=
by simp[form.or]; refine deduction.mp (weakening h _)

lemma hyp_or {p₁ p₂ q} : (T ⊢̇ p₁ →̇ q) → (T ⊢̇ p₂ →̇ q) → (T ⊢̇ p₁ ⩒ p₂ →̇ q) := λ h₁ h₂,
begin
  simp[form.or], apply contrapose.mp, refine deduction.mp _, simp,
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

lemma conjunction_mem {P : list (form L)} : ∀ {p}, p ∈ P → ∅ ⊢̇ conjunction P →̇ p :=
begin
  induction P with p P IH; simp[conjunction],
  have lmm₁ : ∅ ⊢̇ p ⩑ conjunction P →̇ p, from hyp_and_left (by simp),
  have lmm₂ : ∀ q, q ∈ P → ∅ ⊢̇ p ⩑ conjunction P →̇ q, from λ q hq, hyp_and_right (IH hq),
  refine ⟨lmm₁, lmm₂⟩
end

lemma conjunction_inclusion {P Q : list (form L)} : 
  Q ⊆ P → ∅ ⊢̇ conjunction P →̇ conjunction Q :=
begin
  induction Q with q Q IH; simp[conjunction],
  intros hyp_q hyp_Q,
  have lmm₁ : ∅+{conjunction P} ⊢̇ q, from deduction.mpr (conjunction_mem hyp_q),  
  have lmm₂ : ∅+{conjunction P} ⊢̇ conjunction Q, from deduction.mpr (IH hyp_Q),
  refine deduction.mp (and.mpr ⟨lmm₁, lmm₂⟩)
end

private lemma conjunction_sf (P₀ : list (form L)) : (∀ p, p ∈ P₀ → ⇑T p) →
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
    have lmm₂ : ∀ (q : form L), q ∈ (p :: P) → T q,
    { simp, refine ⟨hyp_p, hyp_P.2⟩ },
    refine ⟨p :: P, lmm₁, lmm₂⟩ }
end

theorem proof_conjunction {T : theory L} {p} :
  T ⊢̇ p → ∃ P : list (form L), (∀ p, p ∈ P → T p) ∧ ∅ ⊢̇ conjunction P →̇ p := λ h,
begin
  induction h,
  case fopl.provable.GE : T p hyp IH
  { rcases IH with ⟨P₀, hyp_P₀, prov⟩,
    have : ∃ P, (conjunction P).sf = conjunction P₀ ∧ ∀ p, p ∈ P → T p, from conjunction_sf _ hyp_P₀,
    rcases this with ⟨P, eqn, hyp_P⟩,
    have : ∅ ⊢̇ conjunction P →̇ Ȧp,
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

lemma subst₁ {p} (h : T ⊢̇ Ȧp) (t) : T ⊢̇ p.(t) :=
(show T ⊢̇ Ȧp →̇ p.(t), by simp).MP h

lemma add_sf (p) : ⇑(T +{Ȧp}) ⊢̇ p :=
by { have : ⇑(T +{Ȧp}) ⊢̇ (Ȧp).sf, rw ← sf_dsb, simp,simp[form.sf] at this,
     have := subst₁ this #0, simp[form.subst₁] at this,
     have eqn : (λ n, (#0 ^ˢ (λ x, #(x + 1 + 1)) $ n).rew (#0 ^ˢ vecterm.var)) = (idvar : ℕ → vecterm L 0),
      { funext n, cases n; simp[vecterm.rew] }, simp [eqn] at this, exact this }

private lemma rgerg {P : list (form L)} : (∀ p, p ∈ P → T p) → T ⊢̇ conjunction P :=
begin
  induction P with p P IH; simp[conjunction],
  refine λ hyp_p hyp, ⟨AX hyp_p, IH hyp⟩,
end

private lemma prove_emp_sf : ∀ {p : form L}, ∅ ⊢̇ p → ∅ ⊢̇ p.sf :=
begin
  suffices : ∀ {p : form L} {T}, T ⊢̇ p → T = ∅ → ∅ ⊢̇ p.sf,
  { refine λ p hp, this hp rfl },
  intros p T h,
  induction h with T p hyp_p IH T p q hyp_pq hyp_p IH₁ IH₂ T p hyp; try {simp[form.sf, form.rew] },

end

lemma sf_sf {p} (h : T ⊢̇ p) : ⇑T ⊢̇ p.sf :=
begin
  have : ∃ P, (∀ p, p ∈ P → T p) ∧ ∅ ⊢̇ conjunction P →̇ p, from proof_conjunction h, rcases this with ⟨P, hyp, prov⟩,

end


lemma use {p : form L} (t) (h : T ⊢̇ p.(t)) : T ⊢̇ Ėp :=
begin
  simp[form.ex],
  refine raa (p.(t)) (by simp[h]) (deduction.mpr _),
  have : ¬̇p.(t) = (¬̇p).(t) := rfl,
  simp[this],
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

lemma dummy_fal_quantifir (p) : T ⊢̇ p ↔̇ Ȧ(p.sf) :=
by { have : T ⊢̇ Ȧp.sf →̇ p.sf.(#0), from provable.q1, simp* at * }

@[simp] lemma dummy_fal_quantifir_iff {p : form L} : T ⊢̇ Ȧ(p.sf) ↔ T ⊢̇ p :=
by { have := provable.iff.mp (@dummy_fal_quantifir _ T p), split,
     { refine λ h, (this.2.MP h) },
     { refine λ h, (this.1.MP h) } }

lemma dummy_ex_quantifir (p) : T ⊢̇ p ↔̇ Ė(p.sf) :=
by { simp[form.ex], split,
     { refine contrapose.mp _, simp, exact (provable.iff.mp (dummy_fal_quantifir ¬̇p)).2 },
     { refine contrapose.mp _, simp, exact (provable.iff.mp (dummy_fal_quantifir ¬̇p)).1 } }

lemma prenex_fal_quantifir_imp1 (p q) : T ⊢̇ (Ȧp →̇ q) ↔̇ Ė(p →̇ q.sf) :=
begin
  simp[form.ex], split,
  { apply contrapose.mp, simp, apply deduction.mp,
    have : ⇑(T+{Ȧ¬̇(p →̇ q.sf)}) ⊢̇ ¬̇(p →̇ q.sf), from add_sf _,
    have lmm₂ : T+{Ȧ¬̇(p →̇ q.sf)} ⊢̇ Ȧp, { simp at this, refine GE this.1 },
    have lmm₃ : T+{Ȧ¬̇(p →̇ q.sf)} ⊢̇ ¬̇q,
    { simp at this, rw ← dummy_fal_quantifir_iff, refine GE this.2 },
    simp, refine ⟨lmm₂, lmm₃⟩ },
  { apply contrapose.mp, simp, refine deduction.mp (GE _), simp,
    have : ⇑(T +{¬̇(Ȧp →̇ q)}) ⊢̇ (¬̇(Ȧp →̇ q)).sf,
    { rw ← sf_dsb, from add _ _ },
    simp[form.sf, form.rew] at this,
    have lmm₁ : ⇑(T+{¬̇(Ȧp →̇ q)}) ⊢̇ p,
    { have := this.1.subst₁ #0, simp[form.subst₁, form.rew] at this,
      have eqn : (λ n, (#0 ^ˢ (λ x, #(x + 1 + 1)) $ n).rew (#0 ^ˢ vecterm.var)) = (idvar : ℕ → vecterm L 0),
      { funext n, cases n; simp[vecterm.rew] }, simp[eqn] at this, exact this },
    have lmm₂ : ⇑(T+{¬̇(Ȧp →̇ q)}) ⊢̇ ¬̇q.sf,
    { exact this.2 },
    refine ⟨lmm₁, lmm₂⟩ }
end

lemma prenex_ex_quantifir_imp2 (p q) : T ⊢̇ (p →̇ Ėq) ↔̇ Ė(p.sf →̇ q) :=
begin
  have := @prenex_fal_quantifir_imp1 _ T ¬̇q ¬̇p, simp at*, split,
  {  }




end


end provable

lemma inclusion_le {T U : theory L} : T ⊆ U → T ≤ U := λ hyp p h,
h.inclusion hyp

end fopl