import fopl theory provability

universes u v

namespace fopl
open formula 
variables {L : language.{u}}

def eq_axiom4 {n} (f : L.fn n) : formula L :=
  ∏[2*n] (inf_conjunction n (λ i, #i ≃ #(n + i)) ⟶ (term.app f (λ i, #i) ≃ term.app f (λ i, #(n + i))))

def eq_axiom5 {n} (r : L.pr n) : formula L :=
  ∏[2*n] (inf_conjunction n (λ i, #i ≃ #(n + i)) ⟶ formula.app r (λ i, #i) ⟶ formula.app r (λ i, #(n + i)))

@[simp] lemma eq_axiom4_is_sentence {n} {f : L.fn n} :
  is_sentence (eq_axiom4 f) :=
begin
  simp[is_sentence, eq_axiom4],
  cases n, { simp },
  have lmm₁ : ∀ m n, (⨆ᶠ (i : fin (n + 1)), m + ↑i + 1) = m + n + 1,
  { intros m n,
    suffices : (⨆ᶠ (i : fin (n + 1)), m + ↑i + 1) ≤ m + n + 1 ∧ m + n + 1 ≤ (⨆ᶠ (i : fin (n + 1)), m + ↑i + 1), from le_antisymm_iff.mpr this,
    split,
    { refine fintype_sup_le _, rintros ⟨i, hi⟩, simp[show i ≤ n, from nat.lt_succ_iff.mp hi] },
    { refine le_fintype_sup' ⟨n, by simp⟩ (by refl) }  },
  have lmm₂ : (⨆ᶠ (i : fin (n + 1)), ↑i + 1) = n + 1,
  { have := lmm₁ 0 n, simp at this, exact this },
  simp only [lmm₁ n.succ n, lmm₂, ← nat.add_one],
  simp[max_add_add_left (n + 1) 0 (n + 1), two_mul, add_assoc]
end

@[simp] lemma eq_axiom5_is_sentence {n} {r : L.pr n} :
  is_sentence (eq_axiom5 r) :=
by { simp[is_sentence, eq_axiom5],
     cases n, { simp },  have lmm₁ : ∀ m n, (⨆ᶠ (i : fin (n + 1)), m + ↑i + 1) = m + n + 1,
  { intros m n,
    suffices : (⨆ᶠ (i : fin (n + 1)), m + ↑i + 1) ≤ m + n + 1 ∧ m + n + 1 ≤ (⨆ᶠ (i : fin (n + 1)), m + ↑i + 1), from le_antisymm_iff.mpr this,
    split,
    { refine fintype_sup_le _, rintros ⟨i, hi⟩, simp[show i ≤ n, from nat.lt_succ_iff.mp hi] },
    { refine le_fintype_sup' ⟨n, by simp⟩ (by refl) }  },
  have lmm₂ : (⨆ᶠ (i : fin (n + 1)), ↑i + 1) = n + 1,
  { have := lmm₁ 0 n, simp at this, exact this },
     simp only [lmm₁ n.succ n, lmm₂, ← nat.add_one],
     simp[max_add_add_left (n + 1) 0 (n + 1), two_mul, add_assoc] }

inductive proof : theory L → formula L → Type u
| generalize : ∀ {T p}, proof ⤊T p → proof T (∏ p)
| mdp : ∀ {T p q}, proof T (p ⟶ q) → proof T p → proof T q
| by_axiom : ∀ {T p}, p ∈ T → proof T p
| verum : ∀ {T}, proof T ⊤
| imply₁ : ∀ {T p q}, proof T (p ⟶ q ⟶ p)
| imply₂ : ∀ {T p q r}, proof T ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r)
| contraposition : ∀ {T p q}, proof T ((⁻p ⟶ ⁻q) ⟶ q ⟶ p)
| specialize : ∀ {T p t}, proof T (∏ p ⟶ p.rew ı[0 ⇝ t])
| univ_K : ∀ {T p q}, proof T (∏ (p ⟶ q) ⟶ ∏ p ⟶ ∏ q)
| dummy_univ : ∀ {T p}, proof T (p ⟶ ∏ (p^1))
| eq_reflexivity : ∀ {T}, proof T ∏ (#0 ≃ #0)
| eq_symmetry : ∀ {T}, proof T ∏ ∏ ((#0 ≃ #1) ⟶ (#1 ≃ #0))
| eq_transitivity : ∀ {T}, proof T ∏ ∏ ∏ ((#0 ≃ #1) ⟶ (#1 ≃ #2) ⟶ (#0 ≃ #2))
| function_ext : ∀ {T n} {f : L.fn n}, proof T (eq_axiom4 f)
| predicate_ext : ∀ {T n} {r : L.pr n}, proof T (eq_axiom5 r)

infix ` ⟹ `:45 := proof

def provable (T : theory L) (p : formula L) : Prop := nonempty (T ⟹ p)


instance : axiomatic_classical_logic' (formula L) :=
{ turnstile := provable,
  classical := λ T,
  { modus_ponens := λ p q ⟨bpq⟩ ⟨bp⟩, ⟨bpq.mdp bp⟩,
    imply₁ := λ p q, ⟨proof.imply₁⟩, 
    imply₂ := λ p q r, ⟨proof.imply₂⟩,
    contraposition := λ p q, ⟨proof.contraposition⟩,
    provable_top := ⟨proof.verum⟩,
    bot_eq := by { unfold has_bot.bot },
    and_def := λ p q, rfl,
    or_def := λ p q, rfl },
  by_axiom := λ T p mem, ⟨proof.by_axiom mem⟩ }

noncomputable def provable.proof {T : theory L} {p : formula L} (b : T ⊢ p) : T ⟹ p := nonempty.some b

def provable_theory (T Γ : theory L) : Prop := ∀ p ∈ Γ, T ⊢ p

infix ` ⊢ₜₕ `:45 := provable_theory

open axiomatic_classical_logic' axiomatic_classical_logic

infixl ` ⨀ `:90 := axiomatic_classical_logic'.modus_ponens

@[simp] lemma mem_iff_prov (p : formula L) (T : set (formula L)) :
  (@has_mem.mem (formula L) (set (formula L)) _) p (provable T) ↔ T ⊢ p := by refl

def theory.consistent (T : theory L) : Prop := ¬∃p : formula L, (T ⊢ p) ∧ (T ⊢ ⁻p) 

lemma theory.consistent_def (T : theory L) : T.consistent ↔ ¬∃p : formula L, (T ⊢ p) ∧ (T ⊢ ⁻p) := by refl

lemma theory.consistent_iff_bot (T : theory L) : T.consistent ↔ ¬T ⊢ ⊥ :=
⟨by { simp[theory.consistent], intros h, exact h ⊤ (by simp) },
  by { intros h, simp[theory.consistent], intros p hp hnp,
  have : T ⊢ ⊥, from explosion hp hnp,
  exact h this }⟩

lemma theory.not_consistent_iff_bot {T : theory L} : ¬T.consistent ↔ T ⊢ ⊥ :=
by simp[theory.consistent_iff_bot T]

lemma theory.not_consistent_iff (T : theory L) : ¬T.consistent ↔ ∃p : formula L, (T ⊢ p) ∧ (T ⊢ ⁻p) :=
by simp[theory.consistent_def]

def theory.le (T U : theory L) : Prop := ∀ ⦃p : formula L⦄, T ⊢ p → U ⊢ p

instance : has_le (theory L) := ⟨theory.le⟩

@[simp] lemma theory.le_refl (T : theory L) : T ≤ T := λ p h, h

@[trans] lemma theory.le.trans {T₁ T₂ T₃ : theory L} : T₁ ≤ T₂ → T₂ ≤ T₃ → T₁ ≤ T₃ := λ le₁₂ le₂₃ p b, le₂₃ (le₁₂ b)

class extend (T₀ T : theory L) := (le : T₀ ≤ T)

instance extend_refl (T : theory L) : extend T T := ⟨λ p h, h⟩

@[trans] def extend.trans (T₁ T₂ T₃ : theory L) [extend T₁ T₂]  [extend T₂ T₃] : extend T₁ T₃ := ⟨λ p b, extend.le (extend.le b : T₂ ⊢ p)⟩

def theory.th (T : theory L) : theory L := {p | T ⊢ p}

lemma ss_le {U : ℕ → theory L} (hyp : ∀ s, U s ⊆ U (s+1)) : ∀ {s₁ s₂}, s₁ ≤ s₂ → U s₁ ⊆ U s₂ :=
by { intros s₁, suffices : ∀ t, U s₁ ⊆ U (s₁ + t),
      { intros s₂ eqn, have := this (s₂ - s₁),
        rw (show s₁ + (s₂ - s₁) = s₂, from nat.add_sub_of_le eqn) at this, exact this },
      intros t, induction t with t IH, simp, rw[nat.add_succ],  refine λ x hx, hyp _ (IH hx) }

def formula.equiv (T : theory L) : formula L → formula L → Prop := equiv T

def term.equiv (T : theory L) (t₁ t₂ : term L) : Prop := T ⊢ t₁ ≃ t₂

namespace proof
variables {T : theory L}

def weakening {p} (h : T ⟹ p) : ∀ {U}, T ⊆ U → U ⟹ p :=
begin
  induction h with T p hyp_p IH T p q hyp_pq hyp_p IH₁ IH₂ T p hyp_p; try { simp },
  { intros U hyp, refine generalize (IH (λ x h, _)), rcases h with ⟨p, hp, rfl⟩,
    refine ⟨p, hyp hp, rfl⟩ },
  { intros U hyp, exact (IH₁ hyp).mdp (IH₂ hyp) },
  { intros U hyp, exact by_axiom (hyp hyp_p) },
  { intros U ss, exact verum },
  { intros U ss, exact imply₁ },
  { intros U ss, exact imply₂ },
  { intros U ss, exact contraposition },
  { intros U ss, exact specialize },
  { intros U ss, exact univ_K },
  { intros U ss, exact dummy_univ },
  { intros U ss, exact eq_reflexivity },
  { intros U ss, exact eq_symmetry },
  { intros U ss, exact eq_transitivity },
  { intros U ss, exact function_ext },
  { intros U ss, exact predicate_ext }
end

-- TODO: rec'' で置き換える
@[elab_as_eliminator]
def rec'_on {T : theory L} (C : ℕ → formula L → Sort v) {i : ℕ} {p : formula L} (b : T^i ⟹ p)
  (GE : ∀ {i} {p : formula L} (b : T^(i + 1) ⟹ p), C (i + 1) p → C i (∏ p))
  (MP : ∀ {i} {p q : formula L} (b₁ : T^i ⟹ p ⟶ q) (b₂ : T^i ⟹ p), C i (p ⟶ q) → C i p → C i q)
  (by_axiom : ∀ {i} {p : formula L} (mem : p ∈ T^i), C i p)
  (p0 : ∀ {i}, C i ⊤)
  (p1 : ∀ {i} {p q : formula L}, C i (p ⟶ q ⟶ p))
  (p2 : ∀ {i} {p q r : formula L}, C i ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r))
  (p3 : ∀ {i} {p q : formula L}, C i ((⁻p ⟶ ⁻q) ⟶ q ⟶ p))
  (q1 : ∀ {i} {p : formula L} {t : term L}, C i (∏ p ⟶ p.rew ı[0 ⇝ t]))
  (q2 : ∀ {i} {p q : formula L}, C i (∏ (p ⟶ q) ⟶ ∏ p ⟶∏ q))
  (q3 : ∀ {i} {p : formula L}, C i (p ⟶ ∏ (p^1)))
  (e1 : ∀ {i}, C i (∏ (#0 ≃ #0)))
  (e2 : ∀ {i}, C i (∏ ∏ ((#0 ≃ #1) ⟶ (#1 ≃ #0))))
  (e3 : ∀ {i}, C i (∏ ∏ ∏ ((#0 ≃ #1) ⟶ (#1 ≃ #2) ⟶ (#0 ≃ #2))))
  (e4 : ∀ {i} {m} {f : L.fn m}, C i (eq_axiom4 f))
  (e5 : ∀ {i} {m} {r : L.pr m}, C i (eq_axiom5 r))
  : C i p :=
begin
  suffices :
    ∀ {p : formula L} {U : theory L} (b : U ⟹ p) {i : ℕ} (ss : U ⊆ T^i), C i p,
  { refine this b (by refl) },
  rintros p U b,
  induction b,
  case generalize : U p b IH
  { intros i ss,
    have ss' : ⤊U ⊆ T ^ (i + 1), { rintros _ ⟨q, mem, rfl⟩, simp[theory.sf_itr_succ], refine ⟨q, ss mem, rfl⟩ },
    have : C (i + 1) p, from @IH (i + 1) ss',
    refine GE (b.weakening ss') this },
  case mdp : U p q b₁ b₂ IH₁ IH₂
  { intros i ss, refine MP (weakening b₁ ss) (weakening b₂ ss) (IH₁ ss) (IH₂ ss) },
  case by_axiom : U p mem
  { intros i ss, refine by_axiom (ss mem) },
  { refine λ i ss, p0 },
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
def rec'' {T : theory L} (C : Π (i : ℕ) (p : formula L) (b : T^i ⟹ p), Sort v)
  (GE : ∀ {i} {p : formula L} (b : T^(i + 1) ⟹ p), C (i + 1) p b → C i (∏ p) b.generalize)
  (MP : ∀ {i} {p q : formula L} (b₁ : T^i ⟹ p ⟶ q) (b₂ : T^i ⟹ p), C i (p ⟶ q) b₁ → C i p b₂ → C i q (mdp b₁ b₂))
  (by_axiom : ∀ {i} {p : formula L} (mem : p ∈ T^i), C i p (by_axiom mem))
  (p0 : ∀ {i}, C i ⊤ verum)
  (p1 : ∀ {i} {p q : formula L}, C i (p ⟶ q ⟶ p) imply₁)
  (p2 : ∀ {i} {p q r : formula L}, C i ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r) imply₂)
  (p3 : ∀ {i} {p q : formula L}, C i ((⁻p ⟶ ⁻q) ⟶ q ⟶ p) contraposition)
  (q1 : ∀ {i} {p : formula L} {t : term L}, C i (∏ p ⟶ p.rew ı[0 ⇝ t]) specialize)
  (q2 : ∀ {i} {p q : formula L}, C i (∏ (p ⟶ q) ⟶ ∏ p ⟶∏ q) univ_K)
  (q3 : ∀ {i} {p : formula L}, C i (p ⟶ ∏ (p^1)) dummy_univ)
  (e1 : ∀ {i}, C i (∏ (#0 ≃ #0)) eq_reflexivity)
  (e2 : ∀ {i}, C i (∏ ∏ ((#0 ≃ #1) ⟶ (#1 ≃ #0))) eq_symmetry)
  (e3 : ∀ {i}, C i (∏ ∏ ∏ ((#0 ≃ #1) ⟶ (#1 ≃ #2) ⟶ (#0 ≃ #2))) eq_transitivity)
  (e4 : ∀ {i} {m} {f : L.fn m}, C i (eq_axiom4 f) function_ext)
  (e5 : ∀ {i} {m} {r : L.pr m}, C i (eq_axiom5 r) predicate_ext)
  (i : ℕ) (p : formula L) (b : T^i ⟹ p)
  : C i p b :=
begin
  suffices :
    ∀ {p : formula L} {U : theory L} (b : U ⟹ p) {i : ℕ} (e : U = T^i), C i p (by rcases e with rfl; exact b),
  { have := this b (by refl), exact this },
  rintros p U b,
  induction b,
  case generalize : U p b IH
  { rintros i rfl,
    exact GE _ (@IH (i + 1) rfl) },
  case mdp : U p q b₁ b₂ IH₁ IH₂
  { rintros i rfl, refine MP _ _ (@IH₁ i rfl) (@IH₂ i rfl) },
  case by_axiom : U p mem
  { rintros i rfl, refine by_axiom mem },
  { rintros i rfl, exact p0 },
  { rintros i rfl, exact p1 },
  { rintros i rfl, exact p2 },
  { rintros i rfl, exact p3 },
  { rintros i rfl, exact q1 },
  { rintros i rfl, exact q2 },
  { rintros i rfl, exact q3 },
  { rintros i rfl, exact e1 },
  { rintros i rfl, exact e2 },
  { rintros i rfl, exact e3 },
  { rintros i rfl, exact e4 },
  { rintros i rfl, exact e5 }
end

@[elab_as_eliminator]
def rec''_on {T : theory L} (C : Π (i : ℕ) (p : formula L) (b : T^i ⟹ p), Sort v)
  (i : ℕ) (p : formula L) (b : T^i ⟹ p)
  (GE : ∀ {i} {p : formula L} (b : T^(i + 1) ⟹ p), C (i + 1) p b → C i (∏ p) b.generalize)
  (MP : ∀ {i} {p q : formula L} (b₁ : T^i ⟹ p ⟶ q) (b₂ : T^i ⟹ p), C i (p ⟶ q) b₁ → C i p b₂ → C i q (mdp b₁ b₂))
  (by_axiom : ∀ {i} {p : formula L} (mem : p ∈ T^i), C i p (by_axiom mem))
  (p0 : ∀ {i}, C i ⊤ verum)
  (p1 : ∀ {i} {p q : formula L}, C i (p ⟶ q ⟶ p) imply₁)
  (p2 : ∀ {i} {p q r : formula L}, C i ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r) imply₂)
  (p3 : ∀ {i} {p q : formula L}, C i ((⁻p ⟶ ⁻q) ⟶ q ⟶ p) contraposition)
  (q1 : ∀ {i} {p : formula L} {t : term L}, C i (∏ p ⟶ p.rew ı[0 ⇝ t]) specialize)
  (q2 : ∀ {i} {p q : formula L}, C i (∏ (p ⟶ q) ⟶ ∏ p ⟶∏ q) univ_K)
  (q3 : ∀ {i} {p : formula L}, C i (p ⟶ ∏ (p^1)) dummy_univ)
  (e1 : ∀ {i}, C i (∏ (#0 ≃ #0)) eq_reflexivity)
  (e2 : ∀ {i}, C i (∏ ∏ ((#0 ≃ #1) ⟶ (#1 ≃ #0))) eq_symmetry)
  (e3 : ∀ {i}, C i (∏ ∏ ∏ ((#0 ≃ #1) ⟶ (#1 ≃ #2) ⟶ (#0 ≃ #2))) eq_transitivity)
  (e4 : ∀ {i} {m} {f : L.fn m}, C i (eq_axiom4 f) function_ext)
  (e5 : ∀ {i} {m} {r : L.pr m}, C i (eq_axiom5 r) predicate_ext)
  : C i p b :=
rec'' C @GE @MP @by_axiom @p0 @p1 @p2 @p3 @q1 @q2 @q3 @e1 @e2 @e3 @e4 @e5 i p b

end proof

namespace provable
variables {T : theory L}

lemma generalize {p : formula L} (h : ⤊T ⊢ p) : T ⊢ ∏ p := by rcases h; exact ⟨h.generalize⟩

@[simp] lemma specialize {p : formula L} (t) : T ⊢ ∏ p ⟶ p.rew ı[0 ⇝ t] := ⟨proof.specialize⟩

@[simp] lemma univ_K (p q : formula L) : T ⊢ ∏ (p ⟶ q) ⟶ ∏ p ⟶∏ q := ⟨proof.univ_K⟩

@[simp] lemma dummy_univ_quantifier (p : formula L) : T ⊢ p ⟶ ∏ (p^1) := ⟨proof.dummy_univ⟩

@[simp] lemma eq_reflexivity : T ⊢ ∏ (#0 ≃ #0) := ⟨proof.eq_reflexivity⟩

@[simp] lemma eq_symmetry : T ⊢ ∏ ∏ ((#0 ≃ #1) ⟶ (#1 ≃ #0)) := ⟨proof.eq_symmetry⟩

@[simp] lemma eq_transitivity : T ⊢ ∏ ∏ ∏ ((#0 ≃ #1) ⟶ (#1 ≃ #2) ⟶ (#0 ≃ #2)) := ⟨proof.eq_transitivity⟩

@[simp] lemma function_ext {n} (f : L.fn n) : T ⊢ eq_axiom4 f := ⟨proof.function_ext⟩

@[simp] lemma predicate_ext {n} (r : L.pr n) : T ⊢ eq_axiom5 r := ⟨proof.predicate_ext⟩

lemma generalize_of_closed [closed_theory T] {p} (h : T ⊢ p) : T ⊢ ∏ p :=
by { apply generalize, simp[closed_theory_sf_eq, h] }

lemma generalize_itr : ∀ {n p}, T^n ⊢ p → T ⊢ ∏[n] p
| 0     p h := by simp* at*
| (n+1) p h := by { simp at*, have := generalize_itr (generalize h), simp* at* }

lemma nfal_subst : ∀ (n) (p : formula L) (s : ℕ → term L),
  T ⊢ (∏[n] p) ⟶ p.rew (λ x, if x < n then s x else #(x-n))
| 0     p s := by simp
| (n+1) p s := by { simp,
    have lmm₁ : T ⊢ ∏ (∏[n] p) ⟶ nfal (p.rew $ ı[0 ⇝ s n]^n) n,
    { have := @specialize _ T (∏[n] p) (s n), simp[formula.nfal_rew] at this,
      exact this },
    have s' := s,
    have lmm₂ := nfal_subst n (p.rew $ ı[0 ⇝ s n]^n) s,
    simp[formula.nested_rew] at lmm₂,
    have : (λ x, (ı[0 ⇝ s n]^n $ x).rew (λ x, ite (x < n) (s x) #(x - n))) =
      (λ x, ite (x < n + 1) (s x) #(x - (n + 1))),
    { simp[subst_pow], ext x, have C : x < n ∨ x = n ∨ n < x, from trichotomous _ _,
      cases C,
      { simp[C, nat.lt.step C] }, cases C, { simp[C, term.pow_eq] },
      { have eqn₁ : ¬x - 1 < n, from not_lt.mpr (nat.le_pred_of_lt C),
        have eqn₂ : ¬x < n + 1, from not_lt.mpr (nat.succ_le_iff.mpr C),
        simp[C, eqn₁, eqn₂, nat.sub_sub, add_comm 1 n] } },
    simp[this] at lmm₂,
    exact imply_trans lmm₁ lmm₂ }

lemma nfal_subst' {n} {p : formula L} (h : T ⊢ ∏[n] p ) (s : ℕ → term L) :
  T ⊢ p.rew (λ x, if x < n then s x else #(x-n)) := (nfal_subst n p s) ⨀ h

lemma nfal_subst'_finitary {n} {p : formula L} (h : T ⊢ ∏[n] p ) (s : finitary (term L) n) :
  T ⊢ p.rew (of_fin s) :=
by { let s' : ℕ → term L := λ x, if h : x < n then s ⟨x, h⟩ else default,
     exact cast (by { congr, ext x, by_cases C : x < n; simp[C, s'],
       simp[show n ≤ x, from not_lt.mp C] }) (nfal_subst' h s')}

lemma fal_complete_rew (p : formula L) (s : ℕ → term L) :
  T ⊢ (∏* p) ⟶ p.rew s :=
begin
  have : T ⊢ (∏* p) ⟶ p.rew (λ x, if x < p.arity then s x else #(x - p.arity)),
    from nfal_subst p.arity p s,
  have eqn : (p.rew (λ x, if x < p.arity then s x else #(x - p.arity))) = p.rew s,
    from formula.rew_rew p (λ m h, by simp[h]),
  simp[eqn] at this, exact this
end

lemma weakening {p} (h : T ⊢ p) {U} (ss : T ⊆ U) : U ⊢ p :=
by rcases h; exact ⟨h.weakening ss⟩

lemma weakening' {U : theory L} {p : formula L} : T ⊆ U → T ⊢ p → U ⊢ p := λ hi hp,
weakening hp hi

private lemma delete_imply {p} (h : T ⊢ p) : ∀ q, T \ {q} ⊢ q ⟶ p :=
begin
  rcases h,
  induction h with T p hyp_p IH T p₁ p₂ hyp_p₁₂ hyp_p₁ IH₁ IH₂ T p hyp_p;
    try { intros q, simp }; intros q,
  { have IH : ⤊T \ {q^1} ⊢ q^1 ⟶ p := IH (q^1),
    have lmm₁ : T \ {q} ⊢ q ⟶ ∏ (q^1), { simp },
    have lmm₂ : T \ {q} ⊢ ∏ (q^1) ⟶ ∏ p,
    { suffices : T \ {q} ⊢ ∏ (q^1 ⟶ p),
      { have lmm : T \ {q} ⊢ ∏ (q^1 ⟶ p) ⟶ ∏ (q^1) ⟶ ∏ p, simp,
        exact lmm ⨀ this },
      refine generalize (weakening IH (λ x h, _)), 
      rcases h with ⟨h, neq⟩, rcases h with ⟨p', h', rfl⟩,
      refine ⟨p', ⟨h', λ c, _⟩, rfl⟩, simp at c,
      rw c at neq, exact neq rfl },
    exact imply_trans lmm₁ lmm₂ },
  { have : T \ {q} ⊢ (q ⟶ p₁ ⟶ p₂) ⟶ (q ⟶ p₁) ⟶ (q ⟶ p₂), simp, 
    have : T \ {q} ⊢ (q ⟶ p₁) ⟶ q ⟶ p₂, from this ⨀ (IH₁ _),
    exact this ⨀ (IH₂ _) },
  { by_cases eqn : p = q,
    { simp[eqn] },
    { have : T \ {q} ⊢ p, from by_axiom ⟨hyp_p, eqn⟩,
      simp[this] } }
end

instance : axiomatic_classical_logic (formula L) :=
{ deduction' := λ T p q h, by { have : (T+{p}) \ {p} ⊢ p ⟶ q, from delete_imply h p,
    refine weakening this (λ x h, _), rcases h with ⟨h, neq⟩,
    cases h; simp* at* },
  weakening := @weakening' L }

@[elab_as_eliminator]
theorem rec'_on {T : theory L} {C : ℕ → formula L → Prop} {i : ℕ} {p : formula L} (b : T^i ⊢ p)
  (GE : ∀ {i} {p : formula L} (b : T^(i + 1) ⊢ p), C (i + 1) p → C i (∏ p))
  (MP : ∀ {i} {p q : formula L} (b₁ : T^i ⊢ p ⟶ q) (b₂ : T^i ⊢ p), C i (p ⟶ q) → C i p → C i q)
  (by_axiom : ∀ {i} {p : formula L} (mem : p ∈ T^i), C i p)
  (p0 : ∀ {i}, C i ⊤)
  (p1 : ∀ {i} {p q : formula L}, C i (p ⟶ q ⟶ p))
  (p2 : ∀ {i} {p q r : formula L}, C i ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r))
  (p3 : ∀ {i} {p q : formula L}, C i ((⁻p ⟶ ⁻q) ⟶ q ⟶ p))
  (q1 : ∀ {i} {p : formula L} {t : term L}, C i (∏ p ⟶ p.rew ı[0 ⇝ t]))
  (q2 : ∀ {i} {p q : formula L}, C i (∏ (p ⟶ q) ⟶ ∏ p ⟶∏ q))
  (q3 : ∀ {i} {p : formula L}, C i (p ⟶ ∏ (p^1)))
  (e1 : ∀ {i}, C i (∏ (#0 ≃ #0)))
  (e2 : ∀ {i}, C i (∏ ∏ ((#0 ≃ #1) ⟶ (#1 ≃ #0))))
  (e3 : ∀ {i}, C i (∏ ∏ ∏ ((#0 ≃ #1) ⟶ (#1 ≃ #2) ⟶ (#0 ≃ #2))))
  (e4 : ∀ {i} {m} {f : L.fn m}, C i (eq_axiom4 f))
  (e5 : ∀ {i} {m} {r : L.pr m}, C i (eq_axiom5 r)) :
 C i p :=
begin
  suffices :
    ∀ {p : formula L} {U : theory L} (b : U ⊢ p) {i : ℕ} (ss : U ⊆ T^i),  C i p,
  { refine this b (by refl) },
  rintros p U ⟨b⟩,
  induction b,
  case generalize : U p b IH
  { intros i ss,
    have ss' : ⤊U ⊆ T ^ (i + 1), { rintros _ ⟨q, mem, rfl⟩, simp[theory.sf_itr_succ], refine ⟨q, ss mem, rfl⟩ },
    have : C (i + 1) p, from @IH (i + 1) ss',
    refine GE (weakening ⟨b⟩ ss') this },
  case mdp : U p q b₁ b₂ IH₁ IH₂
  { intros i ss, refine MP (weakening ⟨b₁⟩ ss) (weakening ⟨b₂⟩ ss) (IH₁ ss) (IH₂ ss) },
  case by_axiom : U p mem
  { intros i ss, refine by_axiom (ss mem) },
  { refine λ i ss, p0 },
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

theorem proof_compact : ∀ {T : ℕ → theory L}, (∀ s, T s ⊆ T (s+1)) →
  ∀ {p}, (⋃ s, T s) ⊢ p → ∃ s, T s ⊢ p :=
begin
  suffices : ∀ {p} {U : theory L}, U ⊢ p → ∀ {T : ℕ → theory L},
    (∀ s, T s ⊆ T (s+1)) → U ⊆ (⋃ s, T s) → ∃ s, T s ⊢ p,
  { refine λ T hyp p h, this h hyp (λ x hx, hx) },
  rintros p U ⟨b⟩,
  induction b,
  case generalize : T p h IH
  { intros U hyp ss,
    let U' := λ s, ⤊(U s),
    have hyp' : ∀ s, U' s ⊆ U' (s + 1),
    { simp[U'], intros s p hyp_p, exact hyp s hyp_p },
    have ss' : ⤊T ⊆ ⋃ s, U' s,
    { intros q hyp_q, rcases hyp_q with ⟨q', hyp_q', rfl⟩, rcases (ss hyp_q') with ⟨_, ⟨s, rfl⟩, hyp_s⟩,
      simp, refine ⟨s, _, hyp_s, rfl⟩ },
    have : ∃ s, U' s ⊢ p, from IH hyp' ss', rcases this with ⟨s, h⟩,
    refine ⟨s, generalize h⟩ },
  case mdp : T p q hyp_pq hyp_p IH₁ IH₂
  { intros U hyp ss,
    have : ∃ s, U s ⊢ p ⟶ q, from IH₁ hyp ss, rcases this with ⟨s₁, lmm₁⟩,
    have : ∃ s, U s ⊢ p, from IH₂ hyp ss, rcases this with ⟨s₂, lmm₂⟩,
    refine ⟨max s₁ s₂, _⟩,
    have lmm₁ : U (max s₁ s₂) ⊢ p ⟶ q, from provable.weakening lmm₁ (ss_le hyp (by simp)),
    have lmm₂ : U (max s₁ s₂) ⊢ p, from provable.weakening lmm₂ (ss_le hyp (by simp)),
    exact lmm₁ ⨀ lmm₂ },
  case by_axiom : T p hyp_p
  { intros U hyp ss, rcases (ss hyp_p) with ⟨_, ⟨s, rfl⟩, hyp_s⟩,
    refine ⟨s, by_axiom hyp_s⟩ },
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
  { refine λ _ _ _, ⟨0, by simp⟩ },
  { refine λ _ _ _, ⟨0, by simp⟩ }
end

lemma inf_conjunction_mem {n : ℕ} {P : finitary (formula L) n} :
  ∀ {p}, p ∈ P → T ⊢ inf_conjunction n P ⟶ p :=
begin
  induction n with n IH; simp[inf_conjunction];
  simp[has_mem.mem, finitary.mem],
  intros p mem,
  exact and_imply_of_imply_right (IH mem)
end

lemma conjunction_mem {P : list (formula L)} : ∀ {p}, p ∈ P → T ⊢ conjunction P ⟶ p :=
begin 
  induction P with p P IH; simp[conjunction],
  have : ∀ q, q ∈ P → T ⊢ p ⊓ conjunction P ⟶ q, from λ q hq, and_imply_of_imply_right (IH hq),
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

private lemma conjunction_sf (P₀ : list (formula L)) : (∀ p, p ∈ P₀ → ⤊T p) →
  ∃ P, (conjunction P)^1 = conjunction P₀ ∧ (∀ p, p ∈ P → T p) :=
begin
  induction P₀ with p₀ P₀ IHl, { refine λ _, ⟨[], _⟩, simp[conjunction] },
  { intros hyp,
    have : ∀ p, p ∈ P₀ → ⤊T p,
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

theorem proof_conjunction {T : theory L} {p} :
  T ⊢ p → ∃ P : list (formula L), (∀ p, p ∈ P → T p) ∧ ∅ ⊢ conjunction P ⟶ p := λ h,
begin
  rcases h,
  induction h,
  case generalize : T p hyp IH
  { rcases IH with ⟨P₀, hyp_P₀, prov⟩,
    have : ∃ P, (conjunction P)^1 = conjunction P₀ ∧ ∀ p, p ∈ P → T p, from conjunction_sf _ hyp_P₀,
    rcases this with ⟨P, eqn, hyp_P⟩,
    have : ∅ ⊢ conjunction P ⟶ ∏ p,
    { refine deduction.mp (generalize _),
      rw [←sf_dsb, eqn], refine deduction.mpr (weakening prov (λ x hx, _)), cases hx },
    refine ⟨P, hyp_P, this⟩ },
  case mdp : T p q hyp_pq hyp_p IH₁ IH₂
  { rcases IH₁ with ⟨P₁, IH₁, prov₁⟩, rcases IH₂ with ⟨P₂, IH₂, prov₂⟩,
    refine ⟨P₁ ++ P₂, _, _⟩,
    { simp, intros p h, cases h, refine IH₁ _ h, refine IH₂ _ h },
    { have : ∅+{conjunction (P₁ ++ P₂)} ⊢ conjunction P₂, from deduction.mpr (conjunction_weakening (by simp)),
      have lmm₁ : ∅+{conjunction (P₁ ++ P₂)} ⊢ p, from (show _ ⊢ conjunction P₂ ⟶ p, by simp[prov₂]) ⨀ this,
      have : ∅+{conjunction (P₁ ++ P₂)} ⊢ conjunction P₁, from deduction.mpr (conjunction_weakening (by simp)),
      have lmm₂ : ∅+{conjunction (P₁ ++ P₂)} ⊢ p ⟶ q,
      from (show _ ⊢ conjunction P₁ ⟶ p ⟶ q, by simp[prov₁]) ⨀ this,
      refine deduction.mp (lmm₂ ⨀ lmm₁) } },
  case by_axiom : T p hyp_p
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
  { refine ⟨[], _⟩, simp },
  { refine ⟨[], _⟩, simp }
end

theorem proof_conjunction_union {T U : theory L} {p} :
  T ∪ U ⊢ p → ∃ P Q : list (formula L), (∀ p, p ∈ P → T p) ∧ (∀ p, p ∈ Q → U p) ∧
  ∅ ⊢ conjunction P ⟶ conjunction Q ⟶ p := λ h,
begin
  rcases proof_conjunction h with ⟨R, hR, b⟩,
  let P := R.filter (λ p, p ∈ T),
  let Q := R.filter (λ p, p ∈ U),
  refine ⟨P, Q, by { simp, intros p _ h, exact h }, by { simp, intros p _ h, exact h }, _⟩,
  refine (deduction.mp $ deduction.mp _),
  have : ∅ +{ conjunction P } +{ conjunction Q } ⊢ conjunction R,
  refine conjunction_provable _,
  { intros p memR, rcases hR p memR with (memT | memU),
    { have : p ∈ P, by simp[memR, memT], refine conjunction_mem this ⨀ (by simp) },
    { have : p ∈ Q, by simp[memR, memU], refine conjunction_mem this ⨀ (by simp) } },
  exact (weakening b (by simp)) ⨀ this
end

lemma fal_subst {p} (h : T ⊢ ∏ p) (t) : T ⊢ p.rew ı[0 ⇝ t] :=
(show T ⊢ ∏ p ⟶ p.rew ı[0 ⇝ t], by simp) ⨀ h

infixl ` ⊚ `:60 := fal_subst

lemma add_sf (p) : ⤊(T +{ ∏ p }) ⊢ p :=
by { have : ⤊(T +{∏ p}) ⊢ (∏ p)^1, rw ← sf_dsb, simp, 
     have := fal_subst this #0, simp[formula.nested_rew] at this,
     exact this }

lemma cl_prove_rew [cl : closed_theory T] : ∀ {p : formula L}, T ⊢ p → ∀ s, T ⊢ p.rew s :=
begin
  suffices : ∀ {p : formula L} {T}, T ⊢ p → closed_theory T → ∀ s, T ⊢ p.rew s,
  { refine λ p h s, this h cl _ },
  rintros p T ⟨b⟩,
  induction b,
  case generalize : T p hyp IH
  { intros cl s, rw[@closed_theory_sf_eq _ _ cl] at IH,
    refine generalize _, simp[@closed_theory_sf_eq _ _ cl], exact IH cl _ },
  case mdp : T p q hyp_pq hyp_p IH₁ IH₂
  { intros cl s, simp[formula.rew, @closed_theory_sf_eq _ _ cl] at*, refine (IH₁ cl _) ⨀ (IH₂ cl _) },
  case by_axiom : T p hyp
  { intros cl s, simp[show is_sentence p, by exactI closed_theory.cl hyp], exact by_axiom hyp },
  { simp },
  { simp },
  { simp },
  { simp },
  { intros, simp[formula.rew, formula.subst_sf_rew] },
  { simp },
  case dummy_univ : T p { intros,
    simp,
    have : (p^1).rew (s^1) = (p.rew s)^1,
    { simp[formula.pow_eq, formula.rew, formula.nested_rew], refl },
    simp[this] },
  { simp },
  { simp },
  { simp },
  { simp [formula.is_sentence_rew eq_axiom4_is_sentence] },
  { simp [formula.is_sentence_rew eq_axiom5_is_sentence] }
end

lemma pow_of_cl [closed_theory T] {p : formula L} (i : ℕ) : T ⊢ p → T^i ⊢ p :=
by simp[closed_theory_pow_eq]

lemma iff_fal_complete [closed_theory T] {p : formula L} : T ⊢ p ↔ T ⊢ ∏* p :=
⟨λ h, generalize_itr (pow_of_cl p.arity h), λ h, by simpa using fal_complete_rew p ı ⨀ h⟩

lemma pp_prove_rew {n} (pp : proper_at n T) :
  ∀ {p : formula L}, T ⊢ p → ∀ s, T ⊢ p.rew (s^n) :=
begin
  suffices : ∀ {p : formula L} {T},
    T ⊢ p → ∀ {n}, proper_at n T → ∀ s, T ⊢ p.rew (s^n),
  { refine λ p h s, this h @pp _ },
  rintros p T ⟨b⟩,
  induction b,
  case generalize : T p hyp IH
  { intros n pp s,
    refine generalize _, refine @IH (n+1) (@proper_theory_sf_itr _ _ _ @pp 1) s },
  case mdp : T p q hyp_pq hyp_p IH₁ IH₂
  { intros n pp s, refine (IH₁ @pp _) ⨀ (IH₂ @pp _) },
  case by_axiom : T p hyp
  { intros n pp s, refine by_axiom (pp _ _ hyp) },
  { simp },
  { simp },
  { simp },
  { simp },
  { intros, simp[formula.subst_sf_rew] },
  { simp },
  case dummy_univ : T p { intros,
    simp,
    simp[←formula.pow_rew_distrib] },
  { simp },
  { simp },
  { simp },
  { simp [formula.is_sentence_rew eq_axiom4_is_sentence] },
  { simp [formula.is_sentence_rew eq_axiom5_is_sentence] },
end

lemma proper_theory_pow_rew (n : ℕ) [proper_theory T] : ∀ {p : formula L},
  T^n ⊢ p → ∀ s, T^n ⊢ p.rew (s^n) := @pp_prove_rew L (T^n) n (properc_theory_sf_itr)

lemma proper_theory_rew [proper_theory T] : ∀ {p : formula L},
  T ⊢ p → ∀ s, T ⊢ p.rew s := @pp_prove_rew _ _ 0 proper_theory.proper

protected lemma sup_disjunction {n} {P : finitary (formula L) n} (i) (h : T ⊢ P i) : T ⊢ sup_disjunction n P :=
by { induction n with n IH; simp, { exfalso, exact i.val.not_lt_zero i.property },
     { rcases i with ⟨i, hi⟩,
       have : i = n ∨ i < n, exact eq_or_lt_of_le (nat.lt_succ_iff.mp hi), rcases this with (rfl | lt),
       { refine imply_or_left _ _ ⨀ h }, { simpa using imply_or_right _ _ ⨀ (@IH (λ i, P i) ⟨i, lt⟩ (by simp; exact h)) } } }

lemma sf_sf {p : formula L} : ⤊T ⊢ p^1 ↔ T ⊢ p :=
⟨λ h, by { have := fal_subst (generalize h) #0, simp* at* },
 λ h, by { have : ∃ P, (∀ p, p ∈ P → p ∈ T) ∧ ∅ ⊢ conjunction P ⟶ p,
  from proof_conjunction h, rcases this with ⟨P, hyp_P, prov⟩,
  have lmm₁ : ⤊T ⊢ conjunction (P.map (λ p, p^1)),
  { refine conjunction_provable (λ p hyp, by_axiom _), simp at hyp, rcases hyp with ⟨p', p'_mem, rfl⟩,
    refine ⟨p', hyp_P p' p'_mem, rfl⟩ },
  have lmm₂ : ⤊T ⊢ conjunction (P.map (λ p, p^1)) ⟶ p^1,
  { have : ∅ ⊢ (conjunction P)^1 ⟶ p^1, by exactI cl_prove_rew prov _,
    simp[formula.pow_eq, conjunction_rew_eq] at this,
    refine weakening this (λ p h, _), exfalso, exact h },
  refine lmm₂ ⨀ lmm₁ }⟩

lemma sf_itr_sf_itr : ∀ {i : ℕ} {p : formula L},
  T^i ⊢ p^i ↔ T ⊢ p
| 0     p := by simp
| (i+1) p := by simp[theory.sf_itr_succ];
    rw [show p^(i + 1) = (p^i)^1, by simp[formula.pow_add], sf_sf, @sf_itr_sf_itr i]

lemma pow_rew' [proper_theory T] (i : ℕ) {p : formula L} (h : T^(i + 1) ⊢ p) (s u : ℕ → term L) :
  T^i ⊢ p.rew (λ x, if x < i + 1 then s x else (u (x - i - 1))^i) :=
begin
  have t := #0,
  let f : ℕ → term L := λ x, if x < i + 1 then s x else (u (x - i - 1))^i,
  have : T^i ⊢ ∏ (∏[i + 1] p) ^ (i+1),
    from generalize (show T^(i + 1) ⊢ (∏[i + 1] p) ^ (i+1), from sf_itr_sf_itr.mpr (generalize_itr h)),
  have := fal_subst this t,
  have := (proper_theory_pow_rew i this u),
  simp[formula.nfal_pow, formula.nested_rew, -nfal] at this,
  have := nfal_subst' this s, simp[formula.nested_rew, term.nested_rew, ı] at this,
  simp[subst_pow, rewriting_sf_itr.pow_add] at this,
  have eqn : (λ x, (ite (x < i + 1) #x #(x + (i + 1))).rew (λ x, (ı[(i + 1) ⇝ t ^ (i + 1)] x).rew
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

lemma pow_subst' [proper_theory T] (i : ℕ) {p : formula L} (h : T^(i + 1) ⊢ p) (t : term L) :
  T^i ⊢ p.rew ı[i ⇝ t] :=
by { have := pow_rew' i h ı[i ⇝ t] ı,
     have eqn : (λ x, ite (x < i + 1) (ı[i ⇝ t] x) (ı (x - i - 1) ^ i)) = ı[i ⇝ t],
     { funext x, by_cases C₁ : x < i + 1; simp[C₁],
       have : i < x, exact nat.succ_le_iff.mp (not_lt.mp C₁),
       simp[this, ı], omega },
     rw eqn at this, exact this }

lemma use {p : formula L} (t) (h : T ⊢ p.rew ı[0 ⇝ t]) : T ⊢ ∐ p :=
begin
  simp[has_exists_quantifier.ex, formula.ex],
  refine raa (p.rew ı[0 ⇝ t]) (by simp[h]) (deduction.mpr _),
  have : ⁻p.rew ı[0 ⇝ t] = (⁻p).rew ı[0 ⇝ t] := rfl,
  rw[this], refine specialize t,
end

lemma use_0 {p : formula L} (h : ⤊T ⊢ p) : T ⊢ ∐ p :=
use #0 ((generalize h) ⊚ #0)

@[simp] lemma eq_refl : ∀ {t : term L}, T ⊢ t ≃ t := (@eq_reflexivity _ T).fal_subst

lemma eq_symm : ∀ {t u : term L}, (T ⊢ t ≃ u) → (T ⊢ u ≃ t) :=
begin
  intros t u h,
  have : T ⊢ (t ≃ u) ⟶ (u ≃ t), { have := fal_subst (fal_subst (@eq_symmetry _ T) u) t, simp at*, refine this },
  refine this ⨀ h
end

lemma eq_trans {t₁ t₂ t₃ : term L} : (T ⊢ t₁ ≃ t₂) → (T ⊢ t₂ ≃ t₃) → (T ⊢ t₁ ≃ t₃) := λ h₁ h₂,
by { have : T ⊢ (t₁ ≃ t₂) ⟶ (t₂ ≃ t₃) ⟶ (t₁ ≃ t₃),
     { have := (@eq_transitivity _ T) ⊚ t₃ ⊚ t₂ ⊚ t₁, simp[←term.pow_rew_distrib] at*,
       exact this },
     exact (this ⨀ h₁) ⨀ h₂ }

lemma ne_symm {t u : term L} (h : T ⊢ t ≄ u) : T ⊢ u ≄ t :=
neg_of_equiv h (show T ⊢ (t ≃ u) ⟷ (u ≃ t), by { 
    have : T ⊢ (t ≃ u) ⟶ (u ≃ t),
    { have := fal_subst (fal_subst (@eq_symmetry _ T) u) t, simp at*, refine this },
    have : T ⊢ (u ≃ t) ⟶ (t ≃ u),
    { have := fal_subst (fal_subst (@eq_symmetry _ T) t) u, simp at*, refine this },
    simp[iff_equiv, *] })

lemma function_ext' {n} (f : L.fn n) (v₁ v₂ : finitary (term L) n) :
  T ⊢ (⋀ i, v₁ i ≃ v₂ i) ⟶ (term.app f v₁ ≃ term.app f v₂) :=
begin
  let s : ℕ → term L :=
    (λ x, if h₁ : x < n then v₁ ⟨x, h₁⟩ else
          if h₂ : x < 2*n then v₂ ⟨x - n, by { simp[two_mul] at*, omega}⟩ else #x),
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
  have := nfal_subst' (@function_ext _ T _ f) s,
  simp[eq_conj, eq_v₁, eq_v₂] at this, exact this
end

lemma predicate_ext' {n} (r : L.pr n) (v₁ v₂ : finitary (term L) n) :
  T ⊢ (⋀ i, v₁ i ≃ v₂ i) ⟶ formula.app r v₁ ⟶ formula.app r v₂ :=
begin
  let s : ℕ → term L :=
    (λ x, if h₁ : x < n then v₁ ⟨x, h₁⟩ else
          if h₂ : x < 2*n then v₂ ⟨x - n, by { simp[two_mul] at*, omega}⟩ else #x),
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
  have := nfal_subst' (@predicate_ext _ T _ r) s,
  simp[eq_conj, eq_v₁, eq_v₂] at this, exact this
end

lemma predicate_ext'' {n} (r : L.pr n) (v₁ v₂ : finitary (term L) n) :
  T ⊢ (⋀ i, v₁ i ≃ v₂ i) ⟶ (formula.app r v₁ ⟷ formula.app r v₂) :=
by { refine deduction.mp _,
     simp[iff_equiv], split,
     { refine (predicate_ext' r v₁ v₂) ⨀ (by simp) },
     { refine (predicate_ext' r v₂ v₁) ⨀
       (conjunction_iff.mpr (λ i, eq_symm (deduction.mpr $ inf_conjunction_mem $ finitary.index_mem _ i))) } }

lemma equal_rew_equal (s₁ s₂ : ℕ → term L) (e : ∀ n, T ⊢ s₁ n ≃ s₂ n) : ∀ (t : term L) ,
  T ⊢ t.rew s₁ ≃ t.rew s₂
| (#n)                := by simp; exact e _
| (@term.app _ n f v) :=
  by { simp,
       have : T ⊢ inf_conjunction n (λ i, (v i).rew s₁ ≃ (v i).rew s₂),
       { simp, intros i, refine equal_rew_equal (v i) },
       refine (@function_ext' _ T _ f (λ i, (v i).rew s₁) (λ i, (v i).rew s₂)) ⨀ this }

lemma equal_fal_subst_equal (t : term L) {t₁ t₂} (h : T ⊢ t₁ ≃ t₂) :
  T ⊢ t.rew (t₁ ⌢ ı) ≃ t.rew (t₂ ⌢ ı) :=
by { refine equal_rew_equal _ _ (λ n, _) t, { cases n; simp[concat, h] } }

lemma equal_rew_iff {s₁ s₂ : ℕ → term L} (eqn : ∀ n, T ⊢ s₁ n ≃ s₂ n) (p : formula L) :
  T ⊢ p.rew s₁ ⟷ p.rew s₂ :=
begin
  induction p generalizing T s₁ s₂,
  case verum { simp[show (formula.verum : formula L) = ⊤, from rfl] },
  case app : n p v { intros, simp[axiomatic_classical_logic'.iff_equiv],
    suffices : ∀ (s₁ s₂ : ℕ → term L) (h : ∀ (n : ℕ), T ⊢ s₁ n ≃ s₂ n), T ⊢ formula.app p (λ i, (v i).rew s₁) ⟶ formula.app p (λ i, (v i).rew s₂),
    { refine ⟨this _ _ eqn, this s₂ s₁ (λ x, eq_symm (eqn x))⟩ },
    intros s₁ s₂ eqs,
    have : T ⊢ ⋀ i, (v i).rew s₁ ≃ (v i).rew s₂,
    { simp, intros i,refine equal_rew_equal _ _ eqs _ },
    refine (predicate_ext' p _ _) ⨀ this },
  case equal : t₁ t₂ { intros, simp[axiomatic_classical_logic'.iff_equiv],
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
    simp[axiomatic_classical_logic'.iff_equiv] at*, split,
    { refine deduction.mp (deduction.mp _), 
      have : T+{p.rew s₁ ⟶ q.rew s₁}+{p.rew s₂} ⊢ p.rew s₂, simp,
      have : T+{p.rew s₁ ⟶ q.rew s₁}+{p.rew s₂} ⊢ p.rew s₁, from (by simp[IH₁ eqn]) ⨀ this,
      have : T+{p.rew s₁ ⟶ q.rew s₁}+{p.rew s₂} ⊢ q.rew s₁,
        from (show _ ⊢ p.rew s₁ ⟶ q.rew s₁, by simp) ⨀ this,
      from (by simp[IH₂ eqn]) ⨀ this },
    { refine deduction.mp (deduction.mp _),
      have : T+{p.rew s₂ ⟶ q.rew s₂}+{p.rew s₁} ⊢ p.rew s₁, simp,
      have : T+{p.rew s₂ ⟶ q.rew s₂}+{p.rew s₁} ⊢ p.rew s₂, from (by simp[IH₁ eqn]) ⨀ this,
      have : T+{p.rew s₂ ⟶ q.rew s₂}+{p.rew s₁} ⊢ q.rew s₂,
        from (show _ ⊢ p.rew s₂ ⟶ q.rew s₂, by simp) ⨀ this,
      from (by simp[IH₂ eqn]) ⨀ this } },
  case neg : p IH
  { intros, simp[axiomatic_classical_logic'.iff_equiv] at*,
    refine ⟨contrapose.mpr _, contrapose.mpr _⟩; simp[IH eqn] },
  case fal : p IH
  { intros, simp[axiomatic_classical_logic'.iff_equiv],
    have := @IH (T^1) (s₁^1) (s₂^1)
      (λ n, by { cases n; simp, exact sf_sf.mpr (eqn n) }),
    simp[axiomatic_classical_logic'.iff_equiv] at this, 
    refine ⟨univ_K _ _ ⨀ (generalize this.1), univ_K _ _ ⨀ (generalize this.2)⟩ }
end

lemma iff_of_eqs {s₁ s₂ : ℕ → term L} (eqn : ∀ n, T ⊢ s₁ n ≃ s₂ n) (p : formula L) :
  T ⊢ p.rew s₁ ↔ T ⊢ p.rew s₂ :=
⟨λ h, of_equiv_p h (equal_rew_iff eqn p), λ h, of_equiv_p h (equal_rew_iff (λ n, eq_symm $ eqn n) p)⟩

lemma iff_rew_of_eq {t : term L} {n : ℕ} (eqn : T ⊢ #n ≃ t) (p : formula L) :
  T ⊢ p ⟷ p.rew (λ x, if x = n then t else #x) :=
begin
  suffices : T ⊢ p.rew ı ⟷ p.rew (λ x, if x = n then t else #x), { simp*at* },
  refine equal_rew_iff (λ x, _) _,
  { by_cases C : x = n,
    { rcases C with rfl, simp[ı, eqn] },
    { simp[C] } }
end

lemma rew_of_eq (t : term L) (n : ℕ)
  (eqn : T ⊢ #n ≃ t) {p : formula L} (h : T ⊢ p.rew (λ x, if x = n then t else #x)) :
  T ⊢ p :=
by have := iff_rew_of_eq eqn p; simp[iff_equiv] at this;
   exact this.2 ⨀ h

lemma specialize_iff {t : term L} (p : formula L) :
  T ⊢ p.rew ı[0 ⇝ t] ⟷ ∏ ((#0 ≃ t^1) ⟶ p) :=
begin
  simp[axiomatic_classical_logic'.iff_equiv], split,
  { refine deduction.mp (generalize (deduction.mp _)),
    simp[←sf_dsb],
    have : (p.rew ı[0 ⇝ t])^1 = p.rew (λ x, if x = 0 then t^1 else #x),
    { simp[formula.pow_rew_distrib, formula.pow_eq, formula.nested_rew],
      congr, funext x, cases x; simp, refl },
    rw this,
    refine rew_of_eq (t^1) 0 (by simp) (by simp) },
  { refine deduction.mp _,
    have : T +{ ∏ ((#0 ≃ t^1) ⟶ p) } ⊢ (t ≃ t) ⟶ formula.rew ı[0 ⇝ t] p,
    { have := (show T +{ ∏ ((#0 ≃ (t^1)) ⟶ p) } ⊢ ∏ ((#0 ≃ (t^1)) ⟶ p), by simp) ⊚ t,
      simp at this, exact this },
    exact this ⨀ (by simp) }
end

lemma dummy_fal_quantifir (p) : T ⊢ p ⟷ ∏ p^1 :=
by { have : T ⊢ ∏ (p^1) ⟶ (p^1).rew ı[0 ⇝ #0], from specialize #0, simp[*, axiomatic_classical_logic'.iff_equiv] at * }

lemma dummy_fal_quantifir_iff {p : formula L} : T ⊢ ∏ (p^1) ↔ T ⊢ p :=
by { have :=  (@dummy_fal_quantifir _ T p), simp[axiomatic_classical_logic'.iff_equiv] at this,  split,
     { refine λ h, this ⨀ h },
     { refine λ h, (by simp) ⨀ h } }

lemma dummy_ex_quantifir (p) : T ⊢ p ⟷ ∐ p^1 :=
by { simp[has_exists_quantifier.ex, formula.ex, axiomatic_classical_logic'.iff_equiv],
     have : T ⊢ ⁻p ⟷ ∏ (⁻p) ^ 1, from dummy_fal_quantifir (⁻p), simp[axiomatic_classical_logic'.iff_equiv] at this, 
      split,
     { refine contrapose.mp _, simp[this] },
     { refine contrapose.mp _, simp[this] } }

@[simp] lemma T_hyp_eliminate {p} : T ⊢ ⊤ ⟶ p ↔ T ⊢ p :=
⟨λ h, by { have : T ⊢ ⊤, simp, exact h ⨀ this }, λ h, by simp[h]⟩

lemma equiv_eq_of_equiv {t₁ u₁ t₂ u₂} (h₁ : T ⊢ t₁ ≃ u₁) (h₂ : T ⊢ t₂ ≃ u₂) : T ⊢ (t₁ ≃ t₂) ⟷ (u₁ ≃ u₂) :=
by { simp[axiomatic_classical_logic'.iff_equiv],
     refine ⟨deduction.mp _, deduction.mp  _⟩,
     have lmm₁ : T+{t₁ ≃ t₂} ⊢ u₁ ≃ t₁, simp [eq_symm h₁],
     have lmm₂ : T+{t₁ ≃ t₂} ⊢ t₁ ≃ t₂, simp,
     have lmm₃ : T+{t₁ ≃ t₂} ⊢ t₂ ≃ u₂, simp [h₂],
     refine eq_trans (eq_trans lmm₁ lmm₂) lmm₃,
     have lmm₁ : T+{u₁ ≃ u₂} ⊢ t₁ ≃ u₁, simp [h₁],
     have lmm₂ : T+{u₁ ≃ u₂} ⊢ u₁ ≃ u₂, simp,
     have lmm₃ : T+{u₁ ≃ u₂} ⊢ u₂ ≃ t₂, simp [eq_symm h₂],
     refine eq_trans (eq_trans lmm₁ lmm₂) lmm₃  }

lemma eq_of_equiv {t₁ u₁ t₂ u₂} (h : T ⊢ t₁ ≃ u₁) (hp : T ⊢ t₁ ≃ t₂) (hq : T ⊢ u₁ ≃ u₂) : T ⊢ t₂ ≃ u₂ :=
by { have := equiv_eq_of_equiv hp hq, simp[axiomatic_classical_logic'.iff_equiv] at this, exact this.1 ⨀ h, }

lemma equiv_function_of_equiv {n} (f : L.fn n) {v₁ v₂ : finitary (term L) n} (h : ∀ i, T ⊢ v₁ i ≃ v₂ i) :
  T ⊢ term.app f v₁ ≃ term.app f v₂ :=
function_ext' f v₁ v₂ ⨀ (by simp[h])

lemma equiv_predicate_of_equiv {n} (p : L.pr n) {v₁ v₂ : finitary (term L) n} (h : ∀ i, T ⊢ v₁ i ≃ v₂ i) :
  T ⊢ formula.app p v₁ ⟷ formula.app p v₂ :=
begin
  simp[axiomatic_classical_logic'.iff_equiv],
  refine ⟨(predicate_ext' p v₁ v₂) ⨀ (by simp[h]),
  (predicate_ext' p v₂ v₁) ⨀ (by simp[λ i, eq_symm (h i)])⟩
end

lemma predicate_of_equiv {n} (p : L.pr n) {v₁ v₂ : finitary (term L) n} (h : T ⊢ formula.app p v₁) 
  (hv : ∀ i, T ⊢ v₁ i ≃ v₂ i) : T ⊢ formula.app p v₂ :=
by { have := equiv_predicate_of_equiv p hv, simp[axiomatic_classical_logic'.iff_equiv] at this, exact this.1 ⨀ h }

lemma equiv_univ_of_equiv {p₁ p₂} (h : ⤊T ⊢ p₁ ⟷ p₂) : T ⊢ ∏ p₁ ⟷ ∏ p₂ :=
by { simp[axiomatic_classical_logic'.iff_equiv] at h ⊢, refine ⟨univ_K _ _ ⨀ (generalize h.1), univ_K _ _ ⨀ (generalize h.2)⟩ }

lemma univ_of_equiv {p₁ p₂} (h : T ⊢ ∏ p₁) (hp : ⤊T ⊢ p₁ ⟷ p₂) : T ⊢ ∏ p₂ :=
(iff_equiv.mp (equiv_univ_of_equiv hp)).1 ⨀ h

lemma equiv_univs_of_equiv {p₁ p₂} {n : ℕ} (h : T^n ⊢ p₁ ⟷ p₂) : T ⊢ (∏[n] p₁) ⟷ (∏[n] p₂) :=
by { induction n with n IH generalizing p₁ p₂; simp, { exact h }, { simpa using IH (equiv_univ_of_equiv h) } }

lemma equiv_ex_of_equiv {p₁ p₂} (h : ⤊T ⊢ p₁ ⟷ p₂) : T ⊢ ∐ p₁ ⟷ ∐ p₂ :=
equiv_neg_of_equiv (equiv_univ_of_equiv (equiv_neg_of_equiv h))

lemma ex_of_equiv {p₁ p₂} (h : T ⊢ ∐ p₁) (hp : ⤊T ⊢ p₁ ⟷ p₂) : T ⊢ ∐ p₂ :=
(iff_equiv.mp (equiv_ex_of_equiv hp)).1 ⨀ h

@[simp] protected lemma extend {T₀ T : theory L} [extend T₀ T] {p : formula L} (h : T₀ ⊢ p) : T ⊢ p :=
extend.le h

lemma nfal_K (p q : formula L) (n) : T ⊢ (∏[n] (p ⟶ q)) ⟶ (∏[n] p) ⟶ ∏[n] q :=
begin
  have eqn : ∀ p : formula L, (p.rew (λ x, ite (x < n) #x #(x + n))).rew (λ x, ite (x < n) #x #(x - n)) = p,
  { intros p, simp[formula.nested_rew], 
    have : (λ x, term.rew (λ (x : ℕ), ite (x < n) #x #(x - n)) (ite (x < n) #x #(x + n)) : ℕ → term L) = ı,
    { funext x, by_cases C : x < n; simp[C] }, simp[this] },  
  refine deduction.mp (deduction.mp (generalize_itr _)),
  simp[pow_dsb],
  have lmm₁ : (T^n) +{ (∏[n] p ⟶ q)^n } +{ (∏[n] p)^n } ⊢ p ⟶ q,
  { have :  (T^n) +{ (∏[n] p ⟶ q)^n } +{ (∏[n] p)^n } ⊢ ∏[n] p.rew (λ x, ite (x < n) #x #(x + n)) ⟶ q.rew (λ x, ite (x < n) #x #(x + n)),
    { simp[show (∏[n] p.rew (λ x, ite (x < n) #x #(x + n)) ⟶ q.rew (λ x, ite (x < n) #x #(x + n))) = (∏[n] p ⟶ q)^n, by simp[formula.nfal_pow]] }, 
    have := nfal_subst' this ı, simp[eqn] at this, exact this },
  have lmm₂ : (T^n) +{ (∏[n] p ⟶ q)^n } +{ (∏[n] p)^n } ⊢ p,
  { have : (T^n) +{ (∏[n] p ⟶ q)^n } +{ (∏[n] p)^n } ⊢ ∏[n] p.rew (λ x, ite (x < n) #x #(x + n)),
    { simp[show (∏[n] p.rew (λ x, ite (x < n) #x #(x + n))) = (∏[n] p)^n, by simp[formula.nfal_pow]] },
    have := nfal_subst' this ı, simp[eqn] at this, exact this },
  exact lmm₁ ⨀ lmm₂
end

lemma fal_complete_K (p q : formula L) : T ⊢ (∏* (p ⟶ q)) ⟶ (∏* p) ⟶ ∏* q :=
begin
  refine (deduction.mp $ deduction.mp $ generalize_itr _), simp[pow_dsb],
  have lmm₁ : (T ^ q.arity) +{ ∏* (p ⟶ q) } +{ ∏* p } ⊢ p ⟶ q,
  { have : (T ^ q.arity) +{ ∏* (p ⟶ q) } +{ ∏* p } ⊢ ∏* (p ⟶ q), by simp,
    simpa using fal_complete_rew (p ⟶ q) ı ⨀ this },
  have lmm₂ : (T ^ q.arity) +{ ∏* (p ⟶ q) } +{ ∏* p } ⊢ p,
  { have : (T ^ q.arity) +{ ∏* (p ⟶ q) } +{ ∏* p } ⊢ ∏* p, by simp,
    simpa using fal_complete_rew p ı ⨀ this },
  exact lmm₁ ⨀ lmm₂
end

lemma equiv_fal_complete_of_equiv {p₁ p₂ : formula L} (h : T^(max p₁.arity p₂.arity) ⊢ p₁ ⟷ p₂) :
  T ⊢ (∏* p₁) ⟷ (∏* p₂) :=
begin
  simp[iff_equiv] at h ⊢, split,
  { have : T ⊢ ∏* (p₁ ⟶ p₂), from generalize_itr (by simp[h]),
    exact fal_complete_K _ _ ⨀ this },
  { have : T ⊢ ∏* (p₂ ⟶ p₁), from generalize_itr (by simp[max_comm, h]),
    exact fal_complete_K _ _ ⨀ this }
end

lemma nfal_rew {n} {p : formula L} (s : ℕ → term L) :
  T ⊢ (∏[n] p) ⟶ ∏[n] p.rew (λ x, if x < n then s x else #x) :=
begin
  refine deduction.mp (generalize_itr _),
  have : T +{ ∏[n] p } ^ n ⊢ ∏[n] p.rew (λ x, ite (x < n) #x #(x + n)),
  { simp[pow_dsb, show (∏[n] p.rew (λ x, ite (x < n) #x #(x + n))) = (∏[n] p)^n, by simp[formula.nfal_pow]] },
  have lmm : T +{ ∏[n] p } ^ n ⊢ (p.rew (λ x, ite (x < n) #x #(x + n))).rew (λ x, ite (x < n) (s x) #(x - n)), from nfal_subst' this s,
  simp[formula.nested_rew] at lmm,
  have : (λ x, term.rew (λ x, ite (x < n) (s x) #(x - n)) (ite (x < n) #x #(x + n))) = (λ x, ite (x < n) (s x) #x),
  { funext x, by_cases C : x < n; simp[C] },
  simp[this] at lmm, exact lmm
end

@[simp] lemma fal_shift_equiv_self {p : formula L} : T ⊢ ∏ (p^1) ⟷ p :=
begin
  simp[axiomatic_classical_logic'.iff_equiv],
  have : T ⊢ ∏ p^1 ⟶ (p^1).rew ı[0 ⇝ #0], from specialize #0,
  simp at this, exact this
end

@[simp] lemma nfal_pow_equiv_self {p : formula L} {n : ℕ} : T ⊢ (∏[n] p^n) ⟷ p :=
begin
  induction n with n IH,
  { simp },
  { simp[←nat.add_one],
    have lmm : T ⊢ ∏(∏[n] p^n)^1 ⟷ p,
    { have : T ⊢ ∏(∏[n] p^n)^1 ⟷ ∏[n] p^n, { simp },
      exact equiv_trans this IH },
    have : (∏[n] p^n)^1 = (∏[n] p^(n + 1)), 
    { simp[formula.pow_eq, formula.nested_rew, show ∀ x, x + (n + 1) = x + 1 + n, by omega] },
    simp[this] at lmm, exact lmm }
end

variables (T)

@[simp] lemma provable_theory_refl : T ⊢ₜₕ T := λ p mem, by_axiom mem

variables {T}

lemma provable_theory_weakening {U : theory L} (h : T ⊆ U) : U ⊢ₜₕ T := λ p mem, by_axiom (h mem)

end provable

variables {T : theory L}

namespace theory
variables {T₀ T₁ U₀ U₁ : theory L}

lemma le_of_ss : T₀ ⊆ T₁ → T₀ ≤ T₁ := λ hyp p h, weakening hyp h

@[simp] lemma le_union_left : T₀ ≤ T₀ ∪ T₁ := le_of_ss (by simp)

@[simp] lemma le_union_right : T₁ ≤ T₀ ∪ T₁ := le_of_ss (by simp)

@[simp] lemma union_le_union (h₀ : T₀ ≤ U₀) (h₁ : T₁ ≤ U₁) : T₀ ∪ T₁ ≤ U₀ ∪ U₁ :=
λ p b,
begin
  rcases provable.proof_conjunction_union b with ⟨P, Q, hP, hQ, b⟩,
  have bP : U₀ ∪ U₁ ⊢ conjunction P, from provable.conjunction_provable (λ p hp, weakening (by simp[hp]) (h₀ (by_axiom (hP p hp)))),
  have bQ : U₀ ∪ U₁ ⊢ conjunction Q, from provable.conjunction_provable (λ p hp, weakening (by simp[hp]) (h₁ (by_axiom (hQ p hp)))),
  exact (weakening (by simp) b) ⨀ bP ⨀ bQ
end


def extend_of_inclusion {T₁ T₂ : theory L} (ss : T₁ ⊆ T₂) : extend T₁ T₂ := ⟨le_of_ss ss⟩

instance extend_ax₁ (p : formula L) : extend T (T +{ p }) := ⟨λ q h, by simp[h]⟩

instance extend_ax₂ (p q : formula L) : extend T (T +{ p }+{ q }) := ⟨λ _ h, by simp[h]⟩

instance extend_ax₃ (p q r : formula L) : extend T (T +{ p }+{ q }+{ r }) := ⟨λ _ h, by simp[h]⟩

instance extend_ax₄ (p q r s : formula L) : extend T (T +{ p }+{ q }+{ r }+{ s }) := ⟨λ _ h, by simp[h]⟩

instance extend_sf {T₁ T₂ : theory L} [extend T₁ T₂] : extend (⤊T₁) (⤊T₂) :=
⟨λ p h, by {
  have : T₁ ⊢ ∏ p, from h.generalize,
  have : T₂ ⊢ ∏ p, from this.extend,
  have : ⤊T₂ ⊢ (∏ p)^1, from provable.sf_sf.mpr this,
  simpa[formula.nested_rew] using this ⊚ #0 }⟩

instance extend_pow (T₁ T₂ : theory L) [ex : extend T₁ T₂] (k : ℕ) : extend (T₁^k) (T₂^k) :=
by { induction k with k IH ; simp[theory.sf_itr_succ], { exact ex }, { exactI fopl.theory.extend_sf } }

instance extend_union_left (T₁ T₂ : theory L) : extend T₁ (T₁ ∪ T₂) := theory.extend_of_inclusion (by simp)

instance extend_union_right (T₁ T₂ : theory L) : extend T₂ (T₁ ∪ T₂) := theory.extend_of_inclusion (by simp)

instance extend_empty : extend ∅ T := theory.extend_of_inclusion (by simp)

instance extend_pow_of_closed (T₁ T₂ : theory L) [closed_theory T₁] [extend T₁ T₂] (k : ℕ) : extend T₁ (T₂^k) :=
by simpa using theory.extend_pow T₁ T₂ k

instance union_extend_union [extend T₀ U₀] [extend T₁ U₁] : extend (T₀ ∪ T₁) (U₀ ∪ U₁) :=
⟨union_le_union extend.le extend.le⟩

end theory

lemma provable.extend_pow {T₀ T : theory L} [extend T₀ T] [closed_theory T₀] {p : formula L} (h : T₀ ⊢ p) (k : ℕ) :
  T^k ⊢ p := by { have : T₀^k ⊢ p, by simp[h], exact this.extend }

lemma proper_theory_union (T₁ T₂ : theory L) (h₁ : proper_theory T₁) (h₂ : proper_theory T₂) :
  proper_at 0 (T₁ ∪ T₂) :=
λ p s h, by { cases h,
  { refine or.inl (proper_theory.proper p s h) },
  { refine or.inr (proper_theory.proper p s h) } }

def proper_schema (F : formula L → formula L) : Prop := ∃ i : ℕ, ∀ p s, (F p).rew s = F (p.rew (s^i))

lemma proper_image_of_proper_schema (C : theory L) [proper_theory C]
  {F : formula L → formula L} (h : proper_schema F) : proper_at 0 (F '' C) :=
λ p s mem, begin
    rcases mem with ⟨p, mem, rfl⟩,
    rcases h with ⟨i, h⟩,
    simp[h], refine ⟨p.rew (s^i), by simp[mem], rfl⟩
end

@[reducible] def prf (L : language) := Σ (T : theory L) (p : formula L), T ⟹ p

@[reducible] def prf.to_formula (b : prf L) : formula L := b.snd.fst

@[reducible] def prf.to_proof (b : prf L) := b.snd.snd

@[reducible] def proof.to_prf {p} (b : T ⟹ p) : prf L := ⟨T, p, b⟩

namespace prf
variables {T} {p : formula L} {b : T ⟹ p} {B : prf L}

@[simp] lemma to_proof_to_prf : B.to_proof.to_prf = B := by { rcases B with ⟨T, p, b⟩, simp }

@[simp] lemma to_prf_to_formula : b.to_prf.to_formula = p := rfl

@[simp] lemma to_prf_to_proof : b.to_prf.to_proof = b := rfl

end prf

namespace proof
variables {T} {p : formula L}

inductive subproof : prf L → prf L → Prop
| mdp₁    : ∀ {T : theory L} {p q : formula L} {b₁ : T ⟹ (p ⟶ q)} {b₂ : T ⟹ p}, subproof ⟨T, p ⟶ q, b₁⟩ ⟨T, q, mdp b₁ b₂⟩ 
| mdp₂    : ∀ {T : theory L} {p q : formula L} {b₁ : T ⟹ (p ⟶ q)} {b₂ : T ⟹ p}, subproof ⟨T, p, b₂⟩ ⟨T, q, mdp b₁ b₂⟩
| generalize : ∀ {T : theory L} {p : formula L} {b : ⤊T ⟹ p}, subproof ⟨⤊T, p, b⟩ ⟨T, ∏p, b.generalize⟩ 

@[simp] def complexity : Π {T : theory L} {p : formula L} (b : T ⟹ p), ℕ
| T p (generalize b)            := b.complexity + 1
| T p (mdp b₁ b₂)               := max b₁.complexity b₂.complexity + 1
| T p (by_axiom h)              := 0
| T _ verum                     := 0
| T _ (@imply₁ _ _ p q)         := 0
| T _ (@imply₂ _ _ p q r)       := 0
| T _ (@contraposition _ _ p q) := 0
| T _ (@specialize _ _ p t)     := 0
| T _ (@univ_K _ _ p q)         := 0
| T _ (@dummy_univ _ _ p)       := 0
| T _ (@eq_reflexivity _ _)     := 0
| T _ eq_symmetry               := 0
| T _ eq_transitivity           := 0
| T _ (@function_ext _ _ _ f)   := 0
| T _ (@predicate_ext _ _ _ r)  := 0

instance : wf_lt (prf L) :=
{ prelt := subproof,
  wt := λ b, b.snd.snd.complexity,
  mono' := λ b₁ b₂ h, by { induction h; try { simp },
  case mdp₁ : T p q b₁ b₂ { exact nat.lt_succ_iff.mpr (le_max_left b₁.complexity b₂.complexity) },
  case mdp₂ : T p q b₁ b₂ { exact nat.lt_succ_iff.mpr (le_max_right b₁.complexity b₂.complexity) } } }

def le {T₁ T₂ : theory L} {p₁ p₂ : formula L} (b₁ : T₁ ⟹ p₁) (b₂ : T₂ ⟹ p₂) : Prop := b₁.to_prf ≤ b₂.to_prf

def lt {T₁ T₂ : theory L} {p₁ p₂ : formula L} (b₁ : T₁ ⟹ p₁) (b₂ : T₂ ⟹ p₂) : Prop := b₁.to_prf < b₂.to_prf

def fn_symbols {p} (b : T ⟹ p) : set (Σ n, L.fn n) :=
  let B : set (prf L) := {c | c < b.to_prf},
      B' : set (formula L) := prf.to_formula '' B in ⋃₀ (formula.fn_symbols '' B')

section
variables {T₁ T₂ : theory L} {p₁ p₂ : formula L}

@[simp] lemma lt_generalize_iff {b₁ : prf L} {b₂ : ⤊T₂ ⟹ p₂} : b₁ < b₂.generalize.to_prf ↔ b₁ ≤ b₂.to_prf :=
by { simp[lt, le, wf_lt.lt_iff], split,
     { rintros ⟨T, p, b, prelt, le⟩, rcases prelt, exact le },
     { intros le, refine ⟨⤊T₂, p₂, b₂, subproof.generalize, le⟩ } }

@[simp] lemma lt_mdp_iff {q₂ : formula L} {b₁ : prf L} {b₂₁ : T₂ ⟹ p₂ ⟶ q₂} {b₂₂ : T₂ ⟹ p₂} :
  b₁ < (mdp b₂₁ b₂₂).to_prf ↔ b₁ ≤ b₂₁.to_prf ∨ b₁ ≤ b₂₂.to_prf :=
by { simp[lt, le, wf_lt.lt_iff], split,
     { rintros ⟨T, p, b, prelt, le⟩, rcases prelt, { exact or.inl le }, { exact or.inr le } },
     { rintros (le | le), refine ⟨T₂, p₂ ⟶ q₂, b₂₁, subproof.mdp₁, le⟩, refine ⟨T₂, p₂, b₂₂, subproof.mdp₂, le⟩ } }

end

@[simp] lemma wt_eq_complexity (T) (p) (b) : wf_lt.wt (⟨T, p, b⟩ : prf L) = complexity b :=
by refl

lemma prelt_finite (b : prf L) : set.finite {c | subproof c b} :=
begin
  have of_eq_empty : ∀ s : set (prf L), s = ∅ → s.finite,
  { rintros _ rfl, simp }, 
  rcases b with ⟨T, p, b⟩,
  induction b;
  try { refine of_eq_empty _
    (by { ext c, simp, intros h, 
      have : wf_lt.wt c < wf_lt.wt _, from wf_lt.lt_mono (wf_lt.lt_of_prelt (show wf_lt.prelt c ⟨_, _, _⟩, from h)),
      simp at this, contradiction }) },
  case generalize : T p b
  { have : {c : prf L | subproof c ⟨T, ⟨∏ p, b.generalize⟩⟩} = {b.to_prf},
    { ext c, simp, split,
      { intros h, rcases h, refl }, { rintros rfl, exact subproof.generalize } },
    simp[this] },
  case mdp : T p q b₁ b₂
  { have : {c : prf L | subproof c ⟨T, ⟨q, b₁.mdp b₂⟩⟩} = {b₁.to_prf, b₂.to_prf},
    { ext c, simp, split,
      { intros h, rcases h, refine or.inl rfl, refine or.inr rfl },
      { rintros (rfl | rfl), refine subproof.mdp₁, refine subproof.mdp₂ } },
    simp[this] }
end

lemma le_finite (b : prf L) : set.finite {b' | b' ≤ b} :=
wf_lt.le_finite (show ∀ (a : prf L), {b : prf L | wf_lt.prelt b a}.finite, from prelt_finite) b

def formula_mem_proof (p : formula L) {T : theory.{u} L} {q : formula.{u} L} (b : T ⟹ q) : Prop := ∃ (b' ≤ b.to_prf),p ≤ b'.to_formula

infix ` ∈ᶠ `:50 := formula_mem_proof

@[simp] lemma formula_mem_self {T : theory L} {p : formula L} (b : T ⟹ p) : p ∈ᶠ b := ⟨b.to_prf, by simp⟩

def term_mem_proof (t : term L) {T : theory.{u} L} {p : formula.{u} L} (b : T ⟹ p) : Prop := ∃ (b' ≤ b.to_prf), t ∈ b'.to_formula

infix ` ∈ᵗ `:50 := term_mem_proof

section
variables {T} {p} {b : T ⟹ p} {T₁ T₂ : theory L} {p₁ p₂ : formula L} {b₁ : T₁ ⟹ p₁} {b₂ : T₂ ⟹ p₂} {B : prf L}

lemma term_mem_proof_def {t : term L} :
  t ∈ᵗ b ↔ ∃ b' ≤ b.to_prf, t ∈ b'.to_formula := by refl

lemma mem_trans {t : term L} {q : formula L}
  (ht : t ∈ q) (hq : q ∈ᶠ b) : t ∈ᵗ b :=
by { rcases hq with ⟨b', hb', hq⟩, refine ⟨b', hb', formula.mem_of_formula_le_mem ht hq⟩ }

@[simp] lemma mem_self (B : prf L) : B.to_formula ∈ᶠ B.to_proof := ⟨B, by simp, by simp⟩

lemma formula_mem_proof.mem_of_mem_of_le {p'} (mem : p' ∈ᶠ b) (le : b.to_prf ≤ B) : p' ∈ᶠ B.to_proof :=
by { rcases mem with ⟨b', le_b', ge_b'⟩,
     refine ⟨b', by { simp, exact le_trans le_b' le }, ge_b'⟩ }

lemma term_mem_proof.mem_of_mem_of_le {t'} (mem : t' ∈ᵗ b) (le : b.to_prf ≤ B) : t' ∈ᵗ B.to_proof :=
by { rcases mem with ⟨b', le_b', ge_b'⟩,
     refine ⟨b', by { simp, exact le_trans le_b' le }, ge_b'⟩ }

lemma formula_mem_proof.mem_of_le_of_mem {p' q} (le : q ≤ p') (mem : p' ∈ᶠ b) : q ∈ᶠ b :=
by { rcases mem with ⟨b', le_b', ge_b'⟩, refine ⟨b', le_b', le_trans le ge_b'⟩ }

lemma term_mem_proof.mem_of_le_of_mem {t u} (le : u ≤ t) (mem : t ∈ᵗ b) : u ∈ᵗ b :=
by { rcases mem with ⟨b', le_b', ge_b'⟩, refine ⟨b', le_b', formula.mem_of_term_le_mem ge_b' le⟩ }

@[simp] lemma term_mem_generalize_iff {b : ⤊T ⟹ p} {t : term L} : t ∈ᵗ b.generalize ↔ t ∈ᵗ b :=
⟨by { rintros ⟨b', le, mem⟩,
      have : b' < b.generalize.to_prf ∨ b' = b.generalize.to_prf, exact lt_or_eq_of_le le,
      rcases this with (lt | rfl),
      { simp at lt, 
        have : b'.to_formula ∈ᶠ b, from (mem_self b').mem_of_mem_of_le (show b'.to_proof.to_prf ≤ b.to_prf, by simp[lt]),
        refine mem_trans mem this },
      { simp at mem, refine mem_trans mem (by simp) } },
 λ h, h.mem_of_mem_of_le (show b.to_prf ≤ b.generalize.to_prf, from le_of_lt (by simp))⟩ 

@[simp] lemma term_mem_mdp_iff {p q} {b₁ : T ⟹ p ⟶ q} {b₂ : T ⟹ p} {t} : t ∈ᵗ (b₁.mdp b₂) ↔ t ∈ᵗ b₁ ∨ t ∈ᵗ b₂ :=
⟨by { rintros ⟨b', le, mem⟩,
      have : b' < (b₁.mdp b₂).to_prf ∨ b' = (b₁.mdp b₂).to_prf, exact lt_or_eq_of_le le,
      rcases this with (lt | rfl),
      { simp at lt, rcases lt, 
        { have : b'.to_formula ∈ᶠ b₁, from (mem_self b').mem_of_mem_of_le (show b'.to_proof.to_prf ≤ b₁.to_prf, by simp[lt]),
          refine or.inl (mem_trans mem this) },
        { have : b'.to_formula ∈ᶠ b₂, from (mem_self b').mem_of_mem_of_le (show b'.to_proof.to_prf ≤ b₂.to_prf, by simp[lt]),
          refine or.inr (mem_trans mem this) }, },
      { simp at mem, refine or.inl (mem_trans mem
          (formula_mem_proof.mem_of_le_of_mem (show q ≤ p ⟶ q, from le_of_lt (by simp)) (by simp))) } },
 λ h, by { rcases h with (h | h),
           { exact h.mem_of_mem_of_le (show b₁.to_prf ≤ (b₁.mdp b₂).to_prf, from le_of_lt (by simp)) },
           { exact h.mem_of_mem_of_le (show b₂.to_prf ≤ (b₁.mdp b₂).to_prf, from le_of_lt (by simp)) } }⟩ 

private lemma not_mem_of (b : T ⟹ p) (h : b.complexity = 0) (t : term L) : t ∈ᵗ b ↔ t ∈ p :=
⟨by { rintros ⟨b', le, mem⟩, have : b' < b.to_prf ∨ b' = b.to_prf, exact lt_or_eq_of_le le,
      rcases this with (lt | rfl),
      { have : wf_lt.wt b' < wf_lt.wt b.to_prf, from wf_lt.lt_mono lt,
        simp[h] at this, contradiction },
      { simp at mem, exact mem } },
 by { intros mem, refine ⟨b.to_prf, by simp, by simp[mem]⟩ }⟩


@[simp] lemma term_mem_by_axiom_iff {h : p ∈ T} {t} : t ∈ᵗ by_axiom h ↔ t ∈ p := not_mem_of _ (by simp) _

@[simp] lemma term_mem_verum_iff {t} : ¬t ∈ᵗ (verum : T ⟹ ⊤) := by { have := not_mem_of (verum : T ⟹ ⊤) (by simp) t, simp at this, exact this }

@[simp] lemma term_mem_imply₁_iff {p q : formula L} {t} : t ∈ᵗ (@imply₁ _ T p q) ↔ t ∈ p ∨ t ∈ q :=
by { have := not_mem_of (@imply₁ _ T p q) (by simp) t, simp at this, simp[this], tauto }

@[simp] lemma term_mem_imply₂_iff {p q r : formula L} {t} : t ∈ᵗ (@imply₂ _ T p q r) ↔ t ∈ p ∨ t ∈ q ∨ t ∈ r :=
by { have := not_mem_of (@imply₂ _ T p q r) (by simp) t, simp at this, simp[this], tauto }

@[simp] lemma term_mem_contraposition_iff {p q : formula L} {t} :
  t ∈ᵗ (@contraposition _ T p q) ↔ t ∈ p ∨ t ∈ q :=
by { have := not_mem_of (@contraposition _ T p q) (by simp) t, simp at this, simp[this], tauto }

@[simp] lemma term_mem_specialize_iff {p : formula L} {t₀ t} :
  t ∈ᵗ (@specialize _ T p t₀) ↔ t ∈ p ∨ t ∈ formula.rew ı[0 ⇝ t₀] p :=
by { have := not_mem_of (@specialize _ T p t₀) (by simp) t, simp at this, simp[this] }

@[simp] lemma term_mem_univ_K_iff {p q : formula L} {t} :
  t ∈ᵗ (@univ_K _ T p q) ↔ t ∈ p ∨ t ∈ q :=
by { have := not_mem_of (@univ_K _ T p q) (by simp) t, simp at this, simp[this] }

@[simp] lemma term_mem_dummy_univ_iff {p : formula L} {t} :
  t ∈ᵗ (@dummy_univ _ T p) ↔ t ∈ p ∨ t ∈ p^1 :=
by { have := not_mem_of (@dummy_univ _ T p) (by simp) t, simp at this, simp[this] }

variables (b)

lemma term_mem_finite {T : theory L} {p : formula L} (b : T ⟹ p) : set.finite {t | t ∈ᵗ b} :=
begin
  let s := ⋃ b' ∈ {b' | b' ≤ b.to_prf}, {t | t ∈ b'.to_formula},
  have : {t | t ∈ᵗ b} = s,
  { ext t, simp[s, term_mem_proof_def] },
  simp[this],
  refine set.finite.bUnion (le_finite b.to_prf) (λ b' _, b'.to_formula.mem_finite) 
end

end

end proof

namespace theory
open provable
variables {T} {U : theory L}

lemma le_iff_mem_provable :
  T ≤ U ↔ ∀ p ∈ T, U ⊢ p :=
⟨λ h p mem, h (by_axiom mem), by { 
  suffices : ∀ (T : theory L) (k : ℕ) (p : formula L) (b : T^k ⊢ p) (h : ∀ p ∈ T, U ⊢ p), U^k ⊢ p,
  { intros h p b, exact this T 0 p b h },
  intros T k p b,
  refine rec'_on b _ _ _ _ _ _ _ _ _ _ _ _ _ _ _; try { simp },
  { intros i p b IH h, exact generalize (IH h) },
  { intros i p q b₁ b₂ IH_b₁ IH_b₂ h, exact IH_b₁ h ⨀ IH_b₂ h },
  { intros i p mem h, simp[theory_sf_itr_eq] at mem, rcases mem with ⟨p, mem, rfl⟩,
    exact sf_itr_sf_itr.mpr (h p mem) } }⟩

end theory

end fopl