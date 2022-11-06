import PL.pl provability consistency

universe u

namespace pl
open_locale logic_symbol aclogic
open logic formula
variables {A : Type u}

inductive proof : Theory A → formula A → Type u
| mdp : ∀ {T p q}, proof T (p ⟶ q) → proof T p → proof T q
| by_axiom : ∀ {T p}, p ∈ T → proof T p
| verum : ∀ {T}, proof T ⊤
| imply₁ : ∀ {T p q}, proof T (p ⟶ q ⟶ p)
| imply₂ : ∀ {T p q r}, proof T ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r)
| contraposition : ∀ {T p q}, proof T ((∼p ⟶ ∼q) ⟶ q ⟶ p)

def provable (T : Theory A) (p : formula A) : Prop := nonempty (proof T p)

instance : axiomatic_classical_logic' (formula A) :=
{ turnstile := provable,
  classical := λ T,
  { modus_ponens := λ p q ⟨bpq⟩ ⟨bp⟩, ⟨bpq.mdp bp⟩,
    imply₁ := λ p q, ⟨proof.imply₁⟩, 
    imply₂ := λ p q r, ⟨proof.imply₂⟩,
    contraposition := λ p q, ⟨proof.contraposition⟩,
    provable_top := ⟨proof.verum⟩,
    bot_eq := by refl,
    and_def := λ p q, rfl,
    or_def := λ p q, rfl },
  by_axiom := λ T p mem, ⟨proof.by_axiom mem⟩ }

open axiomatic_classical_logic' axiomatic_classical_logic

@[elab_as_eliminator]
theorem rec'_on {T : Theory A} {C : formula A → Prop} {p : formula A} (b : T ⊢ p)
  (mdp : ∀ {p q : formula A} (b₁ : T ⊢ p ⟶ q) (b₂ : T ⊢ p), C (p ⟶ q) → C p → C q)
  (by_axiom : ∀ {p : formula A} (mem : p ∈ T), C p)
  (p0 : C ⊤)
  (p1 : ∀ {p q : formula A}, C (p ⟶ q ⟶ p))
  (p2 : ∀ {p q r : formula A}, C ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r))
  (p3 : ∀ {p q : formula A}, C ((∼p ⟶ ∼q) ⟶ q ⟶ p)) :
  C p :=
begin
  rcases b with ⟨b⟩,
  induction b,
  case mdp : T p q bpq bp IHpq IHp { exact mdp ⟨bpq⟩ ⟨bp⟩ (IHpq @mdp @by_axiom) (IHp @mdp @by_axiom) },
  case by_axiom : T p hp { exact by_axiom hp },
  case verum : { exact p0 },
  case imply₁ : { exact p1 },
  case imply₂ : { exact p2 },
  case contraposition { exact p3 }
end

namespace proof
variables {T : Theory A}

def weakening {p} (h : proof T p) {U} (ss : T ⊆ U) : proof U p :=
begin
  induction h,
  case mdp : T p q bpq bp IHpq IHp { exact (IHpq ss).mdp (IHp ss) },
  case by_axiom : T p hp { exact proof.by_axiom (ss hp) },
  case verum : { exact proof.verum },
  case imply₁ : { exact proof.imply₁ },
  case imply₂ : { exact proof.imply₂ },
  case contraposition { exact proof.contraposition }
end

end proof

namespace provable
variables {T : Theory A}

lemma weakening {U} {p} (ss : T ⊆ U) (h : T ⊢ p): U ⊢ p :=
by rcases h; exact ⟨h.weakening ss⟩

def deduction' {p q} (h : insert q T ⊢ p) : T ⊢ q ⟶ p :=
begin
  apply rec'_on h,
  { intros p r _ _ h₁ h₂, exact modus_ponens_hyp h₁ h₂ },
  { rintros p (rfl | hp), { simp }, { exact hyp_right (by_axiom hp) q } },
  { simp },
  { simp },
  { simp },
  { simp }
end

instance : axiomatic_classical_logic (formula A) :=
{ deduction' := λ T p q, deduction',
  weakening := λ T U p, weakening }

theorem proof_conjunction {T : Theory A} {p} :
  T ⊢ p → ∃ P : list (formula A), (∀ p, p ∈ P → T p) ∧ ∅ ⊢ P.conjunction ⟶ p := λ h,
begin
  apply rec'_on h,
  { rintros p q b₁ b₂ ⟨P₁, IH₁, b0₁⟩ ⟨P₂, IH₂, b0₂⟩, refine ⟨P₁ ++ P₂, _, _⟩,
    { simp, rintros r (hr | hr), exact IH₁ r hr, exact IH₂ r hr },
    { have : ∅+{(P₁ ++ P₂).conjunction} ⊢ P₂.conjunction, from deduction.mpr (list_conjunction_weakening (by simp)),
      have lmm₁ : ∅+{(P₁ ++ P₂).conjunction} ⊢ p,
        from (show _ ⊢ P₂.conjunction ⟶ p, from weakening_insert b0₂ _) ⨀ this,
      have : ∅+{(P₁ ++ P₂).conjunction} ⊢ P₁.conjunction, from deduction.mpr (list_conjunction_weakening (by simp)),
      have lmm₂ : ∅+{(P₁ ++ P₂).conjunction} ⊢ p ⟶ q,
      from (show _ ⊢ P₁.conjunction ⟶ p ⟶ q, from weakening_insert b0₁ _) ⨀ this,
      refine deduction.mp (lmm₂ ⨀ lmm₁) } },
  { rintros p hp, refine ⟨[p], by simpa using hp, by simp⟩ },
  { refine ⟨[], by simp, by simp⟩ },
  { intros, refine ⟨[], by simp, by simp⟩ },
  { intros, refine ⟨[], by simp, by simp⟩ },
  { intros, refine ⟨[], by simp, by simp⟩ }
end

instance : Theory.has_finite_character (formula A) :=
Theory.finite_character_of_finite_provable (formula A) (λ T p, proof_conjunction)

end provable

end pl