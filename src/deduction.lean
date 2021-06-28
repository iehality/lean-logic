import fopl

universe u

namespace fopl
variables {L : language.{u}}

local attribute [instance, priority 0] classical.prop_decidable

def theory (L : language) := form L → Prop

inductive theory.sf (T : theory L) : theory L
| intro : ∀ {p : form L}, T p → theory.sf p.sf

prefix `⇑`:max := theory.sf

inductive provable : theory L → form L → Prop
| GE : ∀ {T : theory L} {p}, provable ⇑T p → provable T (Ȧp)
| MP : ∀ {T : theory L} {p q}, provable T (p →̇ q) → provable T p → provable T q
| AX : ∀ {T : theory L} {p}, T p → provable T p
| p1 : ∀ {T : theory L} {p q}, provable T (p →̇ q →̇ p)
| p2 : ∀ {T : theory L} {p q r}, provable T ((p →̇ q →̇ r) →̇ (p →̇ q) →̇ p →̇ r)
| p3 : ∀ {T : theory L} {p q}, provable T ((¬̇ p →̇ ¬̇ q) →̇ q →̇ p)
| q1 : ∀ {T : theory L} {p t}, provable T (Ȧ p →̇ p.(t))
| q2 : ∀ {T : theory L} {p q}, provable T (Ȧ (p →̇ q) →̇ Ȧ p →̇ Ȧ q)
| q3 : ∀ {T : theory L} {p}, provable T (p →̇ Ȧ p.sf)
| e1 : ∀ {T : theory L} {t}, provable T (t =̇ t)
| e2 : ∀ {T : theory L} {p : form L} {t u}, provable T (t =̇ u →̇ p.(t) →̇ p.(u))

infix ` ⊢̇ `:60 := provable

attribute [simp] provable.p1 provable.p2 provable.p3 provable.q1 provable.q2 provable.q3
  provable.e1 provable.e2

def theory.consistent (T : theory L) : Prop := ¬∃p, (T ⊢̇ p) ∧ (T ⊢̇ ¬̇p) 

inductive theory.add (T : theory L) (p : form L) : theory L 
| new : theory.add p
| old : ∀ {q}, T q → theory.add q

infixl ` ¦ `:60 := theory.add

def theory.delete (T : theory L) (p : form L) : theory L := λ q, T q ∧ q ≠ p

def theory.include (T U : theory L) : Prop := ∀ p, T p → U p
instance : has_subset (theory L) := ⟨theory.include⟩

def theory.le (T U : theory L) : Prop := ∀ p, T ⊢̇ p → U ⊢̇ p
instance : has_le (theory L) := ⟨theory.le⟩

lemma sf_dsb (T : theory L) (p : form L) : ⇑T ¦ p.sf = ⇑(T ¦ p) :=
begin
  ext x, split; intros h,
  { cases h with h hx, refine theory.sf.intro theory.add.new,
    cases hx with p hp, refine theory.sf.intro (theory.add.old hp) },
  { cases h with q hq, cases hq with _ hq, refine theory.add.new,
    refine theory.add.old (theory.sf.intro hq) }
end

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

@[simp] lemma prT : T ⊢̇ ⊤̇ := GE (by simp)

@[simp] lemma add (p) : T ¦ p ⊢̇ p :=
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
    refine theory.sf.intro _, exact hyp _ hp },
  { intros U hyp, exact (IH₁ hyp).MP (IH₂ hyp) },
  { intros U hyp, exact AX (hyp _ hyp_p) }
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
        exact lmm.MP this },
      refine GE (inclusion IH (λ x h, _)), 
      rcases h with ⟨h, neq⟩, rcases h with ⟨p', h'⟩,
      refine theory.sf.intro ⟨h', λ c, _⟩,
      rw c at neq, exact neq rfl },
    exact lmm₁.imp_trans lmm₂ },
  { have : T.delete q ⊢̇ (q →̇ p₁ →̇ p₂) →̇ (q →̇ p₁) →̇ (q →̇ p₂), simp, 
    have : T.delete q ⊢̇ (q →̇ p₁) →̇ q →̇ p₂, from this.MP (IH₁ _),
    exact this.MP (IH₂ _) },
  { by_cases eqn : p = q,
    { simp[eqn] },
    { have : T.delete q ⊢̇ p, from AX ⟨hyp_p, eqn⟩,
      simp[this] } }
end

theorem deduction {p q} : (T ¦ p ⊢̇ q) ↔ (T ⊢̇ p →̇ q) :=
⟨λ h, by { have : (T ¦ p).delete p ⊢̇ p →̇ q, from delete_imply h p,
           refine inclusion this (λ x h, _), rcases h with ⟨h, neq⟩,
           cases h; simp* at* },
 λ h, by { have : T ¦ p ⊢̇ p →̇ q, from weakening h p,
           exact this.MP (by simp) }⟩ 

@[simp] lemma dne (p) : T ⊢̇ ¬̇¬̇p →̇ p :=
begin
  have llm₁ : T ¦ ¬̇¬̇p ⊢̇ ¬̇¬̇p, simp,   
  have llm₂ : T ¦ ¬̇¬̇p ⊢̇ ¬̇¬̇p →̇ ¬̇¬̇¬̇¬̇p →̇ ¬̇¬̇p, simp,
  have llm₃ : T ¦ ¬̇¬̇p ⊢̇ ¬̇¬̇¬̇¬̇p →̇ ¬̇¬̇p, from llm₂.MP llm₁,
  have llm₄ : T ¦ ¬̇¬̇p ⊢̇ (¬̇¬̇¬̇¬̇p →̇ ¬̇¬̇p) →̇ ¬̇p →̇ ¬̇¬̇¬̇p, simp,
  have llm₅ : T ¦ ¬̇¬̇p ⊢̇ ¬̇p →̇ ¬̇¬̇¬̇p, from llm₄.MP llm₃,
  have llm₆ : T ¦ ¬̇¬̇p ⊢̇ (¬̇p →̇ ¬̇¬̇¬̇p) →̇ ¬̇¬̇p →̇ p, simp,
  have llm₇ : T ¦ ¬̇¬̇p ⊢̇ ¬̇¬̇p →̇ p, from llm₆.MP llm₅,
  have llm₈ : T ¦ ¬̇¬̇p ⊢̇ p, from llm₇.MP llm₁,
  exact deduction.mp llm₈  
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
  have : T ¦ p ⊢̇ ¬̇(p →̇ ¬̇p),
  { have lmm₁ : T ¦ p ⊢̇ p, simp,
    have lmm₂ : T ¦ p ⊢̇ ¬̇p, from (weakening h _).MP lmm₁,
    exact explosion lmm₁ lmm₂ },
  have : T ⊢̇ p →̇ ¬̇(p →̇ ¬̇p), from deduction.mp this,
  have : T ⊢̇ (p →̇ ¬̇p) →̇ ¬̇p, from (dni _).imp_trans (contrapose.mpr this),
  exact this.MP h
end

lemma raa {p} (q) (h₁ : T ¦ p ⊢̇ q) (h₂ : T ¦ p ⊢̇ ¬̇q) : T ⊢̇ ¬̇p :=
neg_hyp (deduction.mp (explosion h₁ h₂))

@[simp] lemma and {p q} : (T ⊢̇ p ⩑ q) ↔ (T ⊢̇ p ∧ T ⊢̇ q) :=
⟨λ h, by { simp[form.and] at h, split,
   { have : T ¦ ¬̇p ¦ p ⊢̇ ¬̇q, 
     from explosion (show T ¦ ¬̇p ¦ p ⊢̇ p, by simp) (show T ¦ ¬̇p ¦ p ⊢̇ ¬̇p, by simp),
     have : T ⊢̇ ¬̇p →̇ p →̇ ¬̇q, from (deduction.mp (deduction.mp this)),
     have : T ⊢̇ ¬̇(p →̇ ¬̇q) →̇ p := (contrapose.mpr this).imp_trans (by simp),
     exact this.MP h },
   { have : T ⊢̇ ¬̇q →̇ p →̇ ¬̇q, simp,
     have : T ⊢̇ ¬̇(p →̇ ¬̇q) →̇ q, from (contrapose.mpr this).imp_trans (by simp),
     exact this.MP h } },
 λ h, by {simp[form.and], rcases h with ⟨h₁, h₂⟩,
   show T ⊢̇ ¬̇(p →̇ ¬̇q),
   have : T ¦ p →̇ ¬̇q ⊢̇ ¬̇q, from (add _ _).MP (by simp[h₁]),
   have : T ⊢̇ (p →̇ ¬̇q) →̇ ¬̇q, from deduction.mp this,
   have : T ⊢̇ q →̇ ¬̇(p →̇ ¬̇q), from (dni _).imp_trans (contrapose.mpr this),
   exact this.MP h₂ }⟩

@[simp] lemma iff {p q} : (T ⊢̇ p ↔̇ q) ↔ (T ⊢̇ p →̇ q ∧ T ⊢̇ q →̇ p) :=
by simp[form.iff]

@[simp] lemma neg_imp {p q} : (T ⊢̇ ¬̇(p →̇ q)) ↔ (T ⊢̇ p ⩑ ¬̇q) :=
begin
  simp only [form.and], split; intros h,
  { apply raa (p →̇ q),
    { have : T ¦ p →̇ ¬̇¬̇q ⊢̇ p →̇ ¬̇¬̇q, from add _ _, simp* at * },
    { simp[h] } },
  { apply raa (p →̇ ¬̇¬̇q); simp[h] }
end

lemma subst₁ {p} (h : T ⊢̇ Ȧp) (t) : T ⊢̇ p.(t) :=
(show T ⊢̇ Ȧp →̇ p.(t), by simp).MP h

lemma subst₂ {p} (h : T ⊢̇ ȦȦp) (t u) : T ⊢̇ p.(t, u) :=
begin
  have : p.(t, u) = (p.rew (#0 ^ˢ u.sf ^ᵉ idvar)).(t),
  { simp [form.subst₂, form.subst₁, form.nested_rew],
    congr, funext n,
    cases n; simp[slide, vecterm.rew],
    cases n; simp[slide, embed, vecterm.rew] },
  sorry
end

lemma add_sf (p) : ⇑(T ¦ Ȧp) ⊢̇ p :=
by { have : ⇑(T ¦ Ȧp) ⊢̇ (Ȧp).sf, rw ← sf_dsb, simp,simp[form.sf] at this,
     have := subst₁ this #0, simp[form.subst₁] at this,
     have eqn : (λ n, (#0 ^ˢ (λ x, #(x + 1 + 1)) $ n).rew (#0 ^ˢ vecterm.var)) = (idvar : ℕ → vecterm L 1),
      { funext n, cases n; simp[vecterm.rew] }, simp [eqn] at this, exact this }


lemma sf_sf {p} (h : T ⊢̇ p) : ⇑T ⊢̇ p.sf :=
begin
  induction h,
  case fopl.provable.GE : T p h IH
  { simp[form.sf, form.rew], 
    have := GE IH, }
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
  have : ∀ v, v =̇ t = (#0 =̇ t.sf).(v),
  { intros v, simp[form.subst₁, form.rew, vecterm.rew, slide] },
  have : T ⊢̇ t =̇ u →̇ t =̇ t →̇ u =̇ t, { rw [this t, this u], simp },
  exact (this.MP h).MP (by simp)
end

lemma eq_trans {t₁ t₂ t₃} : (T ⊢̇ t₁ =̇ t₂) → (T ⊢̇ t₂ =̇ t₃) → (T ⊢̇ t₁ =̇ t₃) := λ h₁ h₂,
begin
  have : ∀ u v : term L, u =̇ v = (u.sf =̇ #0).(v),
  { intros v, simp[form.subst₁, form.rew, vecterm.rew, slide] },
  have : T ⊢̇ t₂ =̇ t₃ →̇ t₁ =̇ t₂ →̇ t₁ =̇ t₃, { rw [this t₁ t₂, this t₁ t₃], simp },
  exact (this.MP h₂).MP h₁
end

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
    have : ⇑(T ¦ Ȧ¬̇(p →̇ q.sf)) ⊢̇ ¬̇(p →̇ q.sf), from add_sf _,
    have lmm₂ : T ¦ Ȧ¬̇(p →̇ q.sf) ⊢̇ Ȧp, { simp at this, refine GE this.1 },
    have lmm₃ : T ¦ Ȧ¬̇(p →̇ q.sf) ⊢̇ ¬̇q,
    { simp at this, rw ← dummy_fal_quantifir_iff, refine GE this.2 },
    simp, refine ⟨lmm₂, lmm₃⟩ },
  { apply contrapose.mp, simp, refine deduction.mp (GE _), simp,
    have : ⇑(T ¦ ¬̇(Ȧp →̇ q)) ⊢̇ (¬̇(Ȧp →̇ q)).sf,
    { rw ← sf_dsb, from add _ _ },
    simp[form.sf, form.rew] at this,
    have lmm₁ : ⇑(T ¦ ¬̇(Ȧp →̇ q)) ⊢̇ p,
    { have := this.1.subst₁ #0, simp[form.subst₁, form.rew] at this,
      have eqn : (λ n, (#0 ^ˢ (λ x, #(x + 1 + 1)) $ n).rew (#0 ^ˢ vecterm.var)) = (idvar : ℕ → vecterm L 1),
      { funext n, cases n; simp[vecterm.rew] }, simp[eqn] at this, exact this },
    have lmm₂ : ⇑(T ¦ ¬̇(Ȧp →̇ q)) ⊢̇ ¬̇q.sf,
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