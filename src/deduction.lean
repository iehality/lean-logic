import fopl theory provability

universe u

namespace fopl
variables {L : language.{u}}

local infix ` ≃₁ `:80 := ((≃) : term L → term L → formula L)

def eq_axiom4 {n} (f : L.fn n) : formula L :=
  ∏[2*n] (conjunction' n (λ i, #i ≃₁ #(n + i)) ⟶ term.app f (λ i, #i) ≃ term.app f (λ i, #(n + i)))

def eq_axiom5 {n} (r : L.pr n) : formula L :=
  ∏[2*n] (conjunction' n (λ i, #i ≃₁ #(n + i)) ⟶ formula.app r (λ i, #i) ⟶ formula.app r (λ i, #(n + i)))

lemma eq_axiom4_sentence {n} {f : L.fn n} :
  sentence (eq_axiom4 f) :=
by { simp[sentence, eq_axiom4],
     cases n, { simp },
     have lmm₁ : ∀ m n, finitary.Max 0 (λ (i : fin (n + 1)), m + ↑i + 1) = m + n + 1,
     { intros m n, induction n with n0 IH, simp[finitary.Max], simp[finitary.Max, fin.add', ←nat.add_one, ←add_assoc, IH] },
     have lmm₂ : finitary.Max 0 (λ (i : fin (n + 1)), ↑i + 1) = n + 1,
     { have := lmm₁ 0 n, simp at this, exact this },
     simp only [lmm₁ n.succ n, lmm₂, ← nat.add_one],
     simp[max_add_add_left (n + 1) 0 (n + 1), two_mul, add_assoc] }

lemma eq_axiom5_sentence {n} {r : L.pr n} :
  sentence (eq_axiom5 r) :=
by { simp[sentence, eq_axiom5],
     cases n, { simp },
     have lmm₁ : ∀ m n, finitary.Max 0 (λ (i : fin (n + 1)), m + ↑i + 1) = m + n + 1,
     { intros m n, induction n with n0 IH, simp[finitary.Max], simp[finitary.Max, fin.add', ←nat.add_one, ←add_assoc, IH] },
     have lmm₂ : finitary.Max 0 (λ (i : fin (n + 1)), ↑i + 1) = n + 1,
     { have := lmm₁ 0 n, simp at this, exact this },
     simp only [lmm₁ n.succ n, lmm₂, ← nat.add_one],
     simp[max_add_add_left (n + 1) 0 (n + 1), two_mul, add_assoc] }

inductive provable : theory L → formula L → Prop
| GE : ∀ {T p}, provable ⇑T p → provable T (∏ p)
| MP : ∀ {T p q}, provable T (p ⟶ q) → provable T p → provable T q
| AX : ∀ {T p}, p ∈ T → provable T p
| p1 : ∀ {T p q}, provable T (p ⟶ q ⟶ p)
| p2 : ∀ {T p q r}, provable T ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r)
| p3 : ∀ {T p q}, provable T ((⁻p ⟶ ⁻q) ⟶ q ⟶ p)
| q1 : ∀ {T p t}, provable T (∏ p ⟶ p.rew ι[0 ⇝ t])
| q2 : ∀ {T p q}, provable T (∏ (p ⟶ q) ⟶ ∏ p ⟶∏ q)
| q3 : ∀ {T p}, provable T (p ⟶ ∏ (p^1))
| e1 : ∀ {T}, provable T ∏ (#0 ≃₁ #0)
| e2 : ∀ {T}, provable T ∏ ∏ (#0 ≃₁ #1 ⟶ #1 ≃₁ #0)
| e3 : ∀ {T}, provable T ∏ ∏ ∏ (#0 ≃₁ #1 ⟶ #1 ≃₁ #2 ⟶ #0 ≃₁ #2)
| e4 : ∀ {T n} {f : L.fn n}, provable T (eq_axiom4 f)
| e5 : ∀ {T n} {r : L.pr n}, provable T (eq_axiom5 r)

instance : axiomatic_classical_logic' (formula L) :=
{ turnstile := provable,
  classical := λ T,
  { modus_ponens := @provable.MP L T,
    imply₁ := @provable.p1 L T, 
    imply₂ := @provable.p2 L T,
    contraposition := @provable.p3 L T,
    provable_top := by { simp[has_top.top, formula.top], refine provable.e1 },
    bot_eq := by simp[has_bot.bot, formula.bot],
    and_def := λ p q, rfl,
    or_def := λ p q, rfl },
  by_axiom := @provable.AX L }

open axiomatic_classical_logic' axiomatic_classical_logic classical_logic

local infixl ` ⨀ `:90 := axiomatic_classical_logic'.modus_ponens

@[simp] lemma mem_iff_prov (p : formula L) (T : set (formula L)) :
  (@has_mem.mem (formula L) (set (formula L)) _) p (provable T) ↔ T ⊢ p := by refl

def theory.consistent (T : theory L) : Prop := ¬ ∃p : formula L, (T ⊢ p) ∧ (T ⊢ ⁻p) 

class consistent (T : theory L) := (consistent : theory.consistent T)

def theory.le (T U : theory L) : Prop := ∀ p : formula L, T ⊢ p → U ⊢ p

instance : has_le (theory L) := ⟨theory.le⟩

def theory.th (T : theory L) : theory L := {p | T ⊢ p}


lemma ss_le {U : ℕ → theory L} (hyp : ∀ s, U s ⊆ U (s+1)) : ∀ {s₁ s₂}, s₁ ≤ s₂ → U s₁ ⊆ U s₂ :=
by { intros s₁, suffices : ∀ t, U s₁ ⊆ U (s₁ + t),
      { intros s₂ eqn, have := this (s₂ - s₁),
        rw (show s₁ + (s₂ - s₁) = s₂, from nat.add_sub_of_le eqn) at this, exact this },
      intros t, induction t with t IH, simp, rw[nat.add_succ],  refine λ x hx, hyp _ (IH hx) }

def formula.equiv (T : theory L) : formula L → formula L → Prop := equiv T

def term.equiv (T : theory L) (t₁ t₂ : term L) : Prop := T ⊢ t₁ ≃₁ t₂

namespace provable
variables {T : theory L}

@[simp] lemma provable.q1' (p : formula L) (t) : T ⊢ ∏ p ⟶ p.rew ι[0 ⇝ t] := provable.q1

@[simp] lemma provable.q2' (p q : formula L) : T ⊢ ∏ (p ⟶ q) ⟶ ∏ p ⟶∏ q := provable.q2

@[simp] lemma provable.q3' (p : formula L) : T ⊢ p ⟶ ∏ (p^1) := provable.q3

@[simp] lemma provable.e1' : T ⊢ ∏ (#0 ≃₁ #0) := provable.e1

@[simp] lemma provable.e2' : T ⊢ ∏ ∏ (#0 ≃₁ #1 ⟶ #1 ≃₁ #0) := provable.e2

@[simp] lemma provable.e3' : T ⊢ ∏ ∏ ∏ (#0 ≃₁ #1 ⟶ #1 ≃₁ #2 ⟶ #0 ≃₁ #2) := provable.e3

@[simp] lemma provable.e4' {n} (f : L.fn n) : T ⊢ eq_axiom4 f := provable.e4

@[simp] lemma provable.e5' {n} (r : L.pr n) : T ⊢ eq_axiom5 r := provable.e5

lemma GE_cl {T : theory L} [closed_theory T] {p} (h : T ⊢ p) : T ⊢ ∏ p :=
by { apply provable.GE, simp[h], exact h }

lemma GE_itr : ∀ {n p}, T^n ⊢ p → T ⊢ ∏[n] p
| 0     p h := by simp* at*
| (n+1) p h := by { simp at*, have := GE_itr (GE h), simp* at* }

lemma nfal_subst (T : theory L) : ∀ (n) (p : formula L) (s : ℕ → term L),
  T ⊢ (∏[n] p) ⟶ p.rew (λ x, if x < n then s x else #(x-n))
| 0     p s := by simp
| (n+1) p s := by { simp,
    have lmm₁ : T ⊢ ∏ (∏[n] p) ⟶ nfal (p.rew $ ι[0 ⇝ s n]^n) n,
    { have := @provable.q1 _ T (∏[n] p) (s n), simp[formula.nfal_rew] at this,
      exact this },
    have s' := s,
    have lmm₂ := nfal_subst n (p.rew $ ι[0 ⇝ s n]^n) s,
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
    exact impl_trans lmm₁ lmm₂ }

lemma nfal_subst' {n} {p : formula L} (h : T ⊢ ∏[n] p ) (s : ℕ → term L) :
  T ⊢ p.rew (λ x, if x < n then s x else #(x-n)) := (nfal_subst T n p s).MP h

lemma weakening {p} (h : T ⊢ p) : ∀ {U}, T ⊆ U → U ⊢ p :=
begin
  induction h with T p hyp_p IH T p q hyp_pq hyp_p IH₁ IH₂ T p hyp_p; try { simp },
  { intros U hyp, refine GE (IH (λ x h, _)), rcases h with ⟨p, hp, rfl⟩,
    refine ⟨p, hyp hp, rfl⟩ },
  { intros U hyp, exact (IH₁ hyp).MP (IH₂ hyp) },
  { intros U hyp, exact AX (hyp hyp_p) },
end

lemma weakening' {U : theory L} {p : formula L} : T ⊆ U → T ⊢ p → U ⊢ p := λ hi hp,
weakening hp hi

private lemma delete_imply {p} (h : T ⊢ p) : ∀ q, T \ {q} ⊢ q ⟶ p :=
begin
  induction h with T p hyp_p IH T p₁ p₂ hyp_p₁₂ hyp_p₁ IH₁ IH₂ T p hyp_p;
    try { intros q, simp }; intros q,
  { have IH : ⇑T \ {q^1} ⊢ q^1 ⟶ p := IH (q^1),
    have lmm₁ : T \ {q} ⊢ q ⟶ ∏ (q^1), { simp },
    have lmm₂ : T \ {q} ⊢ ∏ (q^1) ⟶ ∏ p,
    { suffices : T \ {q} ⊢ ∏ (q^1 ⟶ p),
      { have lmm : T \ {q} ⊢ ∏ (q^1 ⟶ p) ⟶ ∏ (q^1) ⟶ ∏ p, simp,
        exact lmm.MP this },
      refine GE (weakening IH (λ x h, _)), 
      rcases h with ⟨h, neq⟩, rcases h with ⟨p', h', rfl⟩,
      refine ⟨p', ⟨h', λ c, _⟩, rfl⟩, simp at c,
      rw c at neq, exact neq rfl },
    exact impl_trans lmm₁ lmm₂ },
  { have : T \ {q} ⊢ (q ⟶ p₁ ⟶ p₂) ⟶ (q ⟶ p₁) ⟶ (q ⟶ p₂), simp, 
    have : T \ {q} ⊢ (q ⟶ p₁) ⟶ q ⟶ p₂, from this.MP (IH₁ _),
    exact this.MP (IH₂ _) },
  { by_cases eqn : p = q,
    { simp[eqn] },
    { have : T \ {q} ⊢ p, from AX ⟨hyp_p, eqn⟩,
      simp[this] } }
end

instance : axiomatic_classical_logic (formula L) :=
{ deduction' := λ T p q h, by { have : (T+{p}) \ {p} ⊢ p ⟶ q, from delete_imply h p,
    refine weakening this (λ x h, _), rcases h with ⟨h, neq⟩,
    cases h; simp* at* },
  weakening := @weakening' L }

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
    have : ∃ s, U s ⊢ p ⟶ q, from IH₁ hyp ss, rcases this with ⟨s₁, lmm₁⟩,
    have : ∃ s, U s ⊢ p, from IH₂ hyp ss, rcases this with ⟨s₂, lmm₂⟩,
    refine ⟨max s₁ s₂, _⟩,
    have lmm₁ : U (max s₁ s₂) ⊢ p ⟶ q, from provable.weakening lmm₁ (ss_le hyp (by simp)),
    have lmm₂ : U (max s₁ s₂) ⊢ p, from provable.weakening lmm₂ (ss_le hyp (by simp)),
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


lemma conjunction'_mem {n : ℕ} {P : finitary (formula L) n} :
  ∀ {p}, p ∈ P → T ⊢ conjunction' n P ⟶ p :=
begin
  induction n with n IH; simp[conjunction'];
  simp[has_mem.mem, finitary.mem],
  intros p mem,
  exact and_inply_of_imply_right (IH mem)
end

lemma conjunction_mem {P : list (formula L)} : ∀ {p}, p ∈ P → T ⊢ conjunction P ⟶ p :=
begin 
  induction P with p P IH; simp[conjunction],
  have : ∀ q, q ∈ P → T ⊢ p ⊓ conjunction P ⟶ q, from λ q hq, and_inply_of_imply_right (IH hq),
  refine this,
end

lemma conjunction_weakening {P Q : list (formula L)} : 
  Q ⊆ P → T ⊢ conjunction P ⟶ conjunction Q :=
begin
  induction Q with q Q IH; simp[conjunction],
  intros hyp_q hyp_Q,
  have lmm₁ : T+{conjunction P} ⊢ q, from deduction.mpr (conjunction_mem hyp_q),  
  have lmm₂ : T+{conjunction P} ⊢ conjunction Q, from deduction.mpr (IH hyp_Q),
  refine deduction.mp _, simp[axiomatic_classical_logic'.iff_and, *]
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
  T ⊢ p → ∃ P : list (formula L), (∀ p, p ∈ P → T p) ∧ ∅ ⊢ conjunction P ⟶ p := λ h,
begin
  induction h,
  case fopl.provable.GE : T p hyp IH
  { rcases IH with ⟨P₀, hyp_P₀, prov⟩,
    have : ∃ P, (conjunction P)^1 = conjunction P₀ ∧ ∀ p, p ∈ P → T p, from conjunction_sf _ hyp_P₀,
    rcases this with ⟨P, eqn, hyp_P⟩,
    have : ∅ ⊢ conjunction P ⟶ ∏ p,
    { refine deduction.mp (GE _),
      rw [←sf_dsb, eqn], refine deduction.mpr (weakening prov (λ x hx, _)), cases hx },
    refine ⟨P, hyp_P, this⟩ },
  case fopl.provable.MP : T p q hyp_pq hyp_p IH₁ IH₂
  { rcases IH₁ with ⟨P₁, IH₁, prov₁⟩, rcases IH₂ with ⟨P₂, IH₂, prov₂⟩,
    refine ⟨P₁ ++ P₂, _, _⟩,
    { simp, intros p h, cases h, refine IH₁ _ h, refine IH₂ _ h },
    { have : ∅+{conjunction (P₁ ++ P₂)} ⊢ conjunction P₂, from deduction.mpr (conjunction_weakening (by simp)),
      have lmm₁ : ∅+{conjunction (P₁ ++ P₂)} ⊢ p, from (show _ ⊢ conjunction P₂ ⟶ p, by simp[prov₂]).MP this,
      have : ∅+{conjunction (P₁ ++ P₂)} ⊢ conjunction P₁, from deduction.mpr (conjunction_weakening (by simp)),
      have lmm₂ : ∅+{conjunction (P₁ ++ P₂)} ⊢ p ⟶ q,
      from (show _ ⊢ conjunction P₁ ⟶ p ⟶ q, by simp[prov₁]).MP this,
      refine deduction.mp (lmm₂.MP lmm₁) } },
  case fopl.provable.AX : T p hyp_p
  { refine ⟨[p], _⟩, simp[conjunction],
    have : ∅ ⊢ p ⊓ ⊤ ⟶ p,
    { apply deduction.mp, have : ∅+{p ⊓ ⊤} ⊢ p ⊓ ⊤, { simp }, simp[*, axiomatic_classical_logic'.iff_and] at* },
    refine hyp_p },
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

lemma fal_subst {p} (h : T ⊢ ∏ p) (t) : T ⊢ p.rew ι[0 ⇝ t] :=
(show T ⊢ ∏ p ⟶ p.rew ι[0 ⇝ t], by simp).MP h

local infixl ` ⊚ `:60 := fal_subst

lemma add_sf (p) : ⇑(T +{∏ p}) ⊢ p :=
by { have : ⇑(T +{∏ p}) ⊢ (∏ p)^1, rw ← sf_dsb, simp, 
     have := fal_subst this #0, simp[formula.nested_rew] at this,
     have eqn : (λ x, (((λ x, #(x + 1) : ℕ → term _)^1) x).rew ι[0 ⇝ #0]) = @ι L,
     { funext n, cases n; refl }, exact this }

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
  { simp },
  { simp },
  { simp },
  { intros, simp[formula.rew, formula.subst_sf_rew] },
  { simp },
  case q3 : T p { intros,
    simp,
    have : (p^1).rew (s^1) = (p.rew s)^1,
    { simp[formula.pow_eq, formula.rew, formula.nested_rew], refl },
    simp[this] },
  { simp },
  { simp },
  { simp },
  { simp [formula.sentence_rew eq_axiom4_sentence] },
  { simp [formula.sentence_rew eq_axiom5_sentence] },
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
  { simp },
  { simp },
  { simp },
  { intros, simp[formula.subst_sf_rew] },
  { simp },
  case q3 : T p { intros,
    simp,
    simp[←formula.pow_rew_distrib] },
  { simp },
  { simp },
  { simp },
  { simp [formula.sentence_rew eq_axiom4_sentence] },
  { simp [formula.sentence_rew eq_axiom5_sentence] },
end

lemma ppc_prove_rew (n) [pp : proper n T] :
  ∀ {p : formula L}, T ⊢ p → ∀ s, T ⊢ p.rew (s^n) := @pp_prove_rew _ _ n pp.proper

lemma ppc0_prove_rew [pp : proper 0 T] :
  ∀ {p : formula L}, T ⊢ p → ∀ s, T ⊢ p.rew s := @pp_prove_rew _ _ 0 pp.proper

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

protected lemma conjunction' {n} {P : finitary (formula L) n} (h : ∀ i, T ⊢ P i) : T ⊢ conjunction' n P :=
by { induction n with n IH; simp, refine ⟨h _, IH (λ i, _)⟩, refine h _ }

lemma sf_sf {p : formula L} : ⇑T ⊢ p^1 ↔ T ⊢ p :=
⟨λ h, by { have := fal_subst (GE h) #0, simp* at* },
 λ h, by { have : ∃ P, (∀ p, p ∈ P → p ∈ T) ∧ ∅ ⊢ conjunction P ⟶ p,
  from proof_conjunction h, rcases this with ⟨P, hyp_P, prov⟩,
  have lmm₁ : ⇑T ⊢ conjunction (P.map (λ p, p^1)),
  { refine conjunction_provable (λ p hyp, AX _), simp at hyp, rcases hyp with ⟨p', p'_mem, rfl⟩,
    refine ⟨p', hyp_P p' p'_mem, rfl⟩ },
  have lmm₂ : ⇑T ⊢ conjunction (P.map (λ p, p^1)) ⟶ p^1,
  { have : ∅ ⊢ (conjunction P)^1 ⟶ p^1, from cl_prove_rew prov _,
    simp[formula.pow_eq, conjunction_rew_eq] at this,
    refine weakening this (λ p h, _), exfalso, exact h },
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
  have : T^i ⊢ ∏ (nfal p (i+1) ^ (i+1)), from GE ((sf_itr_sf_itr (i + 1) _).mpr (GE_itr h)),
  have := fal_subst this t,
  have := (ppc_prove_rew i this u),
  simp[formula.nfal_pow, formula.nested_rew, -nfal] at this,
  have := nfal_subst' this s, simp[formula.nested_rew, term.nested_rew, ι] at this,
  simp[subst_pow, rewriting_sf_itr.pow_add] at this,
  have eqn : (λ x, (ite (x < i + 1) #x #(x + (i + 1))).rew (λ x, (ι[(i + 1) ⇝ t ^ (i + 1)] x).rew
    (λ x, (u^(i + (i + 1)) $ x).rew (λ x, ite (x < i+1) (s x) #(x - (i+1))) ))) = f,
  { funext x₀, by_cases C : x₀ < i + 1; simp[C],
    { simp[f, rewriting_sf_itr.pow_eq'],
      have : x₀ < i + (i + 1), exact nat.lt_add_left _ _ _ C,
      simp[this, C] },
    { have : i + 1 < x₀ + (i + 1), { omega },
      simp[f, this, rewriting_sf_itr.pow_eq', term.pow_eq], 
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

lemma use {p : formula L} (t) (h : T ⊢ p.rew ι[0 ⇝ t]) : T ⊢ ∐ p :=
begin
  simp[has_exists_quantifier.ex, formula.ex],
  refine raa (p.rew ι[0 ⇝ t]) (by simp[h]) (deduction.mpr _),
  have : ⁻p.rew ι[0 ⇝ t] = (⁻p).rew ι[0 ⇝ t] := rfl,
  rw[this], refine provable.q1,
end

@[simp] lemma eq_refl : ∀ {t : term L}, T ⊢ t ≃ t := (@provable.e1 _ T).fal_subst

lemma eq_symm : ∀ {t u : term L}, (T ⊢ t ≃ u) → (T ⊢ u ≃ t) :=
begin
  intros t u h,
  have : T ⊢ t ≃ u ⟶ u ≃ t, { have := fal_subst (fal_subst (@provable.e2 _ T) u) t, simp at*, refine this },
  refine this.MP h
end

lemma eq_trans {t₁ t₂ t₃ : term L} : (T ⊢ t₁ ≃ t₂) → (T ⊢ t₂ ≃ t₃) → (T ⊢ t₁ ≃ t₃) := λ h₁ h₂,
by { have : T ⊢ t₁ ≃ t₂ ⟶ t₂ ≃ t₃ ⟶ t₁ ≃ t₃,
     { have := (@provable.e3 _ T) ⊚ t₃ ⊚ t₂ ⊚ t₁, simp[←term.pow_rew_distrib] at*,
       exact this },
     exact (this.MP h₁).MP h₂ }

lemma e4' {n} (f : L.fn n) (v₁ v₂ : finitary (term L) n) :
  T ⊢ conjunction' n (λ i, v₁ i ≃ v₂ i) ⟶ term.app f v₁ ≃ term.app f v₂ :=
begin
  let s : ℕ → term L :=
    (λ x, if h₁ : x < n then v₁ ⟨x, h₁⟩ else
          if h₂ : x < 2*n then v₂ ⟨x - n, by { simp[two_mul] at*, exact (nat.sub_lt_left_iff_lt_add h₁).mpr h₂}⟩ else #x),
  have eq_conj :
    (λ i, ite (↑i < 2 * n) (s ↑i) #(↑i - 2*n) ≃ ite (n + ↑i < 2*n) (s (n + ↑i)) #(n + ↑i - 2*n) : fin n → formula L) =
    (λ i, v₁ i ≃ v₂ i),
  { funext i, simp[s, two_mul, show ↑i < n, from i.property],
    intros h, exfalso, refine not_le_of_gt i.property (nat.le_of_add_le_left h) },      
  have eq_v₁ : (λ i, ite (↑i < 2 * n) (s ↑i) #(↑i - 2 * n)) = v₁,
  { funext i, simp[s, two_mul, show ↑i < n, from i.property],
    intros h, exfalso, refine not_le_of_gt i.property (nat.le_of_add_le_left h) },
  have eq_v₂ : (λ i, ite (n + ↑i < 2 * n) (s (n + ↑i)) #(n + ↑i - 2 * n)) = v₂,
  { funext i, simp[s, two_mul, show ↑i < n, from i.property] },
  have := nfal_subst' (@provable.e4 _ T _ f) s,
  simp[eq_conj, eq_v₁, eq_v₂] at this, exact this
end

lemma e5' {n} (r : L.pr n) (v₁ v₂ : finitary (term L) n) :
  T ⊢ conjunction' n (λ i, v₁ i ≃ v₂ i) ⟶ formula.app r v₁ ⟶ formula.app r v₂ :=
begin
  let s : ℕ → term L :=
    (λ x, if h₁ : x < n then v₁ ⟨x, h₁⟩ else
          if h₂ : x < 2*n then v₂ ⟨x - n, by { simp[two_mul] at*, exact (nat.sub_lt_left_iff_lt_add h₁).mpr h₂}⟩ else #x),
  have eq_conj :
    (λ i, ite (↑i < 2 * n) (s ↑i) #(↑i - 2*n) ≃ ite (n + ↑i < 2*n) (s (n + ↑i)) #(n + ↑i - 2*n) : fin n → formula L) =
    (λ i, v₁ i ≃ v₂ i),
  { funext i, simp[s, two_mul, show ↑i < n, from i.property],
    intros h, exfalso, refine not_le_of_gt i.property (nat.le_of_add_le_left h) },      
  have eq_v₁ : (λ i, ite (↑i < 2 * n) (s ↑i) #(↑i - 2 * n)) = v₁,
  { funext i, simp[s, two_mul, show ↑i < n, from i.property],
    intros h, exfalso, refine not_le_of_gt i.property (nat.le_of_add_le_left h) },
  have eq_v₂ : (λ i, ite (n + ↑i < 2 * n) (s (n + ↑i)) #(n + ↑i - 2 * n)) = v₂,
  { funext i, simp[s, two_mul, show ↑i < n, from i.property] },
  have := nfal_subst' (@provable.e5 _ T _ r) s,
  simp[eq_conj, eq_v₁, eq_v₂] at this, exact this
end

lemma equal_rew_equal (s₁ s₂ : ℕ → term L) (e : ∀ n, T ⊢ s₁ n ≃ s₂ n) : ∀ (t : term L) ,
  T ⊢ t.rew s₁ ≃ t.rew s₂
| (#n)                := by simp; exact e _
| (@term.app _ n f v) :=
  by { simp,
       have : T ⊢ conjunction' n (λ i, (v i).rew s₁ ≃ (v i).rew s₂),
       { apply provable.conjunction', intros i, refine equal_rew_equal (v i) },
       refine (@e4' _ T _ f (λ i, (v i).rew s₁) (λ i, (v i).rew s₂)).MP this }

lemma equal_fal_subst_equal (t : term L) {t₁ t₂} (h : T ⊢ t₁ ≃ t₂) :
  T ⊢ t.rew (t₁ ⌢ ι) ≃ t.rew (t₂ ⌢ ι) :=
by { refine equal_rew_equal _ _ (λ n, _) t, { cases n; simp[concat, h] } }

lemma equal_rew_iff {s₁ s₂ : ℕ → term L} (eqn : ∀ n, T ⊢ s₁ n ≃ s₂ n) (p : formula L) :
  T ⊢ p.rew s₁ ⟷ p.rew s₂ :=
begin
  induction p generalizing T s₁ s₂,
  case app : n p v { intros, simp,
    suffices : ∀ (s₁ s₂ : ℕ → term L) (h : ∀ (n : ℕ), T ⊢ s₁ n ≃ s₂ n), T ⊢ formula.app p (λ i, (v i).rew s₁) ⟶ formula.app p (λ i, (v i).rew s₂),
    { refine ⟨this _ _ eqn, this s₂ s₁ (λ x, eq_symm (eqn x))⟩ },
    intros s₁ s₂ eqs,
    have : T ⊢ conjunction' n (λ i, (v i).rew s₁ ≃ (v i).rew s₂),
    { apply provable.conjunction', intros i,refine equal_rew_equal _ _ eqs _ },
    refine (e5' p _ _).MP this },
  case equal : t₁ t₂ { intros, simp,
    refine ⟨deduction.mp _, deduction.mp _⟩,
    { have lmm₁ : T+{t₁.rew s₁ ≃ t₂.rew s₁} ⊢ t₁.rew s₂ ≃ t₁.rew s₁,
      { refine equal_rew_equal s₂ s₁ (λ n, eq_symm _) t₁, simp[eqn n] },
      have lmm₂ : T+{t₁.rew s₁ ≃ t₂.rew s₁} ⊢ t₁.rew s₁ ≃ t₂.rew s₁, { simp },
      have lmm₃ : T+{t₁.rew s₁ ≃ t₂.rew s₁} ⊢ t₂.rew s₁ ≃ t₂.rew s₂,
      { refine equal_rew_equal s₁ s₂ (λ n, _) t₂, simp[eqn n]  },
      refine eq_trans lmm₁ (eq_trans lmm₂ lmm₃) },
    { have lmm₁ : T+{t₁.rew s₂ ≃ t₂.rew s₂} ⊢ t₁.rew s₁ ≃ t₁.rew s₂,
      { refine equal_rew_equal s₁ s₂ (λ n, _) t₁, simp[eqn n] },
      have lmm₂ : T+{t₁.rew s₂ ≃ t₂.rew s₂} ⊢ t₁.rew s₂ ≃ t₂.rew s₂, { simp },
      have lmm₃ : T+{t₁.rew s₂ ≃ t₂.rew s₂} ⊢ t₂.rew s₂ ≃ t₂.rew s₁,
      { refine equal_rew_equal s₂ s₁ (λ n, eq_symm _) t₂, simp[eqn n]  },
      refine eq_trans lmm₁ (eq_trans lmm₂ lmm₃) } },
  case imply : p q IH₁ IH₂
  { intros, 
    simp at*, split,
    { refine deduction.mp (deduction.mp _), 
      have : T+{p.rew s₁ ⟶ q.rew s₁}+{p.rew s₂} ⊢ p.rew s₂, simp,
      have : T+{p.rew s₁ ⟶ q.rew s₁}+{p.rew s₂} ⊢ p.rew s₁, from (by simp[IH₁ eqn]) ⨀ this,
      have : T+{p.rew s₁ ⟶ q.rew s₁}+{p.rew s₂} ⊢ q.rew s₁,
        from MP (show _ ⊢ p.rew s₁ ⟶ q.rew s₁, by simp) this,
      from (by simp[IH₂ eqn]) ⨀ this },
    { refine deduction.mp (deduction.mp _),
      have : T+{p.rew s₂ ⟶ q.rew s₂}+{p.rew s₁} ⊢ p.rew s₁, simp,
      have : T+{p.rew s₂ ⟶ q.rew s₂}+{p.rew s₁} ⊢ p.rew s₂, from (by simp[IH₁ eqn]) ⨀ this,
      have : T+{p.rew s₂ ⟶ q.rew s₂}+{p.rew s₁} ⊢ q.rew s₂,
        from MP (show _ ⊢ p.rew s₂ ⟶ q.rew s₂, by simp) this,
      from (by simp[IH₂ eqn]) ⨀ this } },
  case neg : p IH
  { intros, simp at*,
    refine ⟨contrapose.mpr _, contrapose.mpr _⟩; simp[IH eqn] },
  case fal : p IH
  { intros, simp,
    have := @IH (T^1) (s₁^1) (s₂^1)
      (λ n, by { cases n; simp, exact sf_sf.mpr (eqn n) }),
    simp at this, 
    refine ⟨provable.q2.MP (GE this.1), provable.q2.MP (GE this.2)⟩ }
end

lemma dummy_fal_quantifir (p) : T ⊢ p ⟷ ∏ p^1 :=
by { have : T ⊢ ∏ (p^1) ⟶ (p^1).rew ι[0 ⇝ #0], from provable.q1, simp* at * }

lemma dummy_fal_quantifir_iff {p : formula L} : T ⊢ ∏ (p^1) ↔ T ⊢ p :=
by { have :=  (@dummy_fal_quantifir _ T p), simp at this,  split,
     { refine λ h, this ⨀ h },
     { refine λ h, (by simp) ⨀ h } }

lemma dummy_ex_quantifir (p) : T ⊢ p ⟷ ∐ p^1 :=
by { simp[has_exists_quantifier.ex, formula.ex],
     have : T ⊢ ⁻p ⟷ ∏ (⁻p) ^ 1, from dummy_fal_quantifir ⁻p, simp at this, 
      split,
     { refine contrapose.mp _, simp[this] },
     { refine contrapose.mp _, simp[this] } }

@[simp] lemma T_hyp_eliminate {p} : T ⊢ ⊤ ⟶ p ↔ T ⊢ p :=
⟨λ h, by { have : T ⊢ ⊤, simp, exact h.MP this }, λ h, by simp[h]⟩

end provable

lemma weakening_le {T U : theory L} : T ⊆ U → T ≤ U := λ hyp p h, weakening hyp h

end fopl