import QL.FOL.fol provability consistency

universes u v

namespace fol
open_locale logic_symbol
open subterm subformula logic logic.Theory
variables {L : language.{u}} {m : ℕ}

localized "prefix (name := mlift) `𝗟`:max := subformula.mlift" in aclogic
localized "prefix (name := preTheory.mlift) `𝗟'`:max := preTheory.mlift" in aclogic
localized "prefix (name := push) `𝗠`:max := subformula.push" in aclogic
localized "prefix (name := pull) `𝗡`:max := subformula.pull" in aclogic
localized "prefix (name := dummy) `𝗗`:max := subformula.dummy" in aclogic

def eq_axiom4 {m k} (f : L.fn k) : subformula L m 0 :=
∀'*((⋀ i, #(fin.cast_add k i) =' #(fin.nat_add k i)) ⟶
  (function f (var ∘ fin.cast_add k) =' function f (var ∘ fin.nat_add k)) : subformula L m (k + k))

def eq_axiom5 {m k} (r : L.pr k) : subformula L m 0 :=
∀'*((⋀ i : fin k, #(fin.cast_add k i) =' #(fin.nat_add k i)) ⟶
  (relation r (var ∘ fin.cast_add k) ⟷ relation r (var ∘ fin.nat_add k)))

inductive proof : Π {m}, preTheory L m → subformula L m 0 → Type u
| generalize   {m} {T : preTheory L m} : ∀ {p}, proof T.mlift p → proof T (∀'𝗡p)
| mdp          {m} {T : preTheory L m} : ∀ {p q}, proof T (p ⟶ q) → proof T p → proof T q
| by_axiom     {m} {T : preTheory L m} : ∀ {p}, p ∈ T → proof T p
| verum        {m} {T : preTheory L m} : proof T ⊤
| imply₁       {m} {T : preTheory L m} : ∀ {p q}, proof T (p ⟶ q ⟶ p)
| imply₂       {m} {T : preTheory L m} : ∀ {p q r}, proof T ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r)
| contra       {m} {T : preTheory L m} : ∀ {p q}, proof T ((∼p ⟶ ∼q) ⟶ q ⟶ p)
| specialize   {m} {T : preTheory L m} : ∀ {p} {t}, proof T (∀'p ⟶ subst t p)
| dummy_univ   {m} {T : preTheory L m} : ∀ {p q}, proof T (∀'(dummy p ⟶ q) ⟶ p ⟶ ∀'q)
| non_empty    {m} {T : preTheory L m} : proof T (∃'⊤)
| eq_refl      {m} {T : preTheory L m} : proof T ∀'(#0 =' #0)
| eq_symm      {m} {T : preTheory L m} : proof T ∀' ∀'((#0 =' #1) ⟶ (#1 =' #0))
| eq_trans     {m} {T : preTheory L m} : proof T ∀' ∀' ∀'((#0 =' #1) ⟶ (#1 =' #2) ⟶ (#0 =' #2))
| function_ext {m} {T : preTheory L m} : ∀ {n} {f : L.fn n}, proof T (eq_axiom4 f)
| relation_ext {m} {T : preTheory L m} : ∀ {n} {r : L.pr n}, proof T (eq_axiom5 r)

instance (m : ℕ) : has_Longarrow (formula L m) := ⟨proof⟩

def provable (m) (T : preTheory L m) (p : formula L m) : Prop := nonempty (T ⟹ p)

instance (m) : axiomatic_classical_logic' (formula L m) :=
{ turnstile := provable m,
  classical := λ T,
  { modus_ponens := λ p q ⟨bpq⟩ ⟨bp⟩, ⟨bpq.mdp bp⟩,
    imply₁ := λ p q, ⟨proof.imply₁⟩, 
    imply₂ := λ p q r, ⟨proof.imply₂⟩,
    contraposition := λ p q, ⟨proof.contra⟩,
    provable_top := ⟨proof.verum⟩,
    bot_eq := by refl,
    and_def := λ p q, rfl,
    or_def := λ p q, rfl },
  by_axiom := λ T p mem, ⟨proof.by_axiom mem⟩ }

open_locale aclogic

namespace proof
variables {T : preTheory L m}

def weakening' {p} (h : T ⟹ p) : ∀ {U}, T ⊆ U → U ⟹ p :=
begin
  induction h,
  case generalize : m T p hyp_p IH
  { intros U hyp, refine generalize (IH $ set.image_subset _ hyp) },
  case mdp : m T p q hyp_pq hyp_p IH₁ IH₂
  { intros U hyp, exact (IH₁ hyp).mdp (IH₂ hyp) },
  case by_axiom : m T p hyp_p
  { intros U hyp, exact by_axiom (hyp hyp_p) },
  { intros U ss, exact verum },
  { intros U ss, exact imply₁ },
  { intros U ss, exact imply₂ },
  { intros U ss, exact contra },
  { intros U ss, exact specialize },
  { intros U ss, exact dummy_univ },
  { intros U ss, exact non_empty },
  { intros U ss, exact eq_refl },
  { intros U ss, exact eq_symm },
  { intros U ss, exact eq_trans },
  { intros U ss, exact function_ext },
  { intros U ss, exact relation_ext }
end

end proof

namespace provable
open axiomatic_classical_logic' axiomatic_classical_logic
variables {T U : preTheory L m}

lemma generalize {p} (h : T.mlift ⊢ p) : T ⊢ ∀'p.pull := by rcases h; exact ⟨h.generalize⟩

lemma generalize' {T : preTheory L (m + 1)} {p} (h : T ⊢ p) (hT : T = U.mlift) : U ⊢ ∀'p.pull :=
by rcases hT with rfl; exact generalize h

lemma gen {p : subformula L m 1} (h : T.mlift ⊢ p.push) : T ⊢ ∀'p :=
by rw[←subformula.pull_push p]; exact generalize h

lemma by_axiom {p} (h : p ∈ T) : T ⊢ p := ⟨proof.by_axiom h⟩

variables (T)

@[simp] lemma specialize (p) (t) : T ⊢ ∀'p ⟶ subst t p := ⟨proof.specialize⟩

variables {T}

lemma forall_subst {p} (h : T ⊢ ∀'p) (t) : T ⊢ subst t p :=
specialize T p t ⨀ h

infix ` ⊚ `:60 := forall_subst

variables (T)

@[simp] lemma dummy_univ (p q) : T ⊢ ∀'(dummy p ⟶ q) ⟶ p ⟶ ∀'q := ⟨proof.dummy_univ⟩

@[simp] lemma non_empty : T ⊢ ∃'⊤ := ⟨proof.non_empty⟩

@[simp] lemma eq_refl : T ⊢ ∀'(#0 =' #0) := ⟨proof.eq_refl⟩

@[simp] lemma eq_symm : T ⊢ ∀' ∀'((#0 =' #1) ⟶ (#1 =' #0)) := ⟨proof.eq_symm⟩

@[simp] lemma eq_trans : T ⊢ ∀' ∀' ∀'((#0 =' #1) ⟶ (#1 =' #2) ⟶ (#0 =' #2)) := ⟨proof.eq_trans⟩

@[simp] lemma function_ext {n} (f : L.fn n) : T ⊢ eq_axiom4 f := ⟨proof.function_ext⟩

@[simp] lemma relation_ext {n} (r : L.pr n) : T ⊢ eq_axiom5 r := ⟨proof.relation_ext⟩

variables {T U}

theorem rec_on {C : Π {m} (T : preTheory L m) (p : subformula L m 0), T ⊢ p → Prop}
  {m : ℕ} {T : preTheory L m} {p : formula L m} (b : T ⊢ p)
  (generalize : ∀ {m} {T : preTheory L m} {p} (b : T.mlift ⊢ p), C T.mlift p b → C T (∀'p.pull) (generalize b))
  (mdp : ∀ {m} {T : preTheory L m} {p q} (b₁ : T ⊢ p ⟶ q) (b₂ : T ⊢ p), C T (p ⟶ q) b₁ → C T p b₂ → C T q (b₁ ⨀ b₂))
  (by_axiom : ∀ {m} {T : preTheory L m} {p} (h : p ∈ T), C T p (by_axiom h))
  (verum : ∀ {m} {T : preTheory L m}, C T ⊤ axiomatic_classical_logic'.provable_top)
  (imply₁ : ∀ {m} {T : preTheory L m} {p q}, C T (p ⟶ q ⟶ p) (axiomatic_classical_logic'.imply₁ p q))
  (imply₂ : ∀ {m} {T : preTheory L m} {p q r}, C T ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r) (axiomatic_classical_logic'.imply₂ p q r))
  (contra : ∀ {m} {T : preTheory L m} {p q}, C T ((∼p ⟶ ∼q) ⟶ q ⟶ p) (axiomatic_classical_logic'.contraposition p q)) 
  (specialize : ∀ {m} {T : preTheory L m} {p} {t}, C T (∀'p ⟶ subst t p) (specialize T p t))
  (dummy_univ : ∀ {m} {T : preTheory L m} {p q}, C T (∀'(dummy p ⟶ q) ⟶ p ⟶ ∀'q) (dummy_univ T p q))
  (non_empty : ∀ {m} {T : preTheory L m}, C T (∃'⊤) (non_empty T))
  (eq_refl : ∀ {m} {T : preTheory L m}, C T (∀'(#0 =' #0)) (eq_refl T))
  (eq_symm : ∀ {m} {T : preTheory L m}, C T (∀' ∀'((#0 =' #1) ⟶ (#1 =' #0))) (eq_symm T))
  (eq_trans : ∀ {m} {T : preTheory L m}, C T (∀' ∀' ∀'((#0 =' #1) ⟶ (#1 =' #2) ⟶ (#0 =' #2))) (eq_trans T))
  (function_ext : ∀ {m} {T : preTheory L m} {p} {f : L.fn p}, C T (eq_axiom4 f) (function_ext T f))
  (relation_ext : ∀ {m} {T : preTheory L m} {p} {r : L.pr p}, C T (eq_axiom5 r) (relation_ext T r)) :
  C T p b :=
begin
  rcases b with ⟨b⟩,
  induction b,
  case generalize : m T p b IH { exact generalize ⟨b⟩ IH },
  case mdp : m T p q b₁ b₂ IH₁ IH₂ { exact mdp ⟨b₁⟩ ⟨b₂⟩ IH₁ IH₂ },
  case by_axiom : m T p hp { exact by_axiom hp },
  case verum : m T { exact verum },
  case imply₁ : m T p q { exact imply₁ },
  case imply₂ : m T p q r { exact imply₂ },
  case contra : m T p q { exact contra },
  case specialize : m T p t { exact specialize },
  case dummy_univ : m T p q { exact dummy_univ },
  case non_empty { exact non_empty },
  case eq_refl : { exact eq_refl },
  case eq_symm : { exact eq_symm },
  case eq_trans : { exact eq_trans },
  case function_ext : T p f { exact function_ext },
  case relation_ext : T p f { exact relation_ext }
end

noncomputable def provable.proof {T : preTheory L m} {p : formula L m} (b : T ⊢ p) : T ⟹ p := nonempty.some b

def weakening_aux {p} (h : T ⊢ p) : ∀ {U}, T ⊆ U → U ⊢ p :=
begin
  apply rec_on h,
  { intros m T p b IH U hyp, refine generalize (IH $ set.image_subset _ hyp) },
  { intros m T p q hyp_pq hyp_p IH₁ IH₂ U hyp, exact (IH₁ hyp) ⨀ (IH₂ hyp) },
  { intros m T p hyp_p U hyp, exact by_axiom (hyp hyp_p) },
  { intros, simp },
  { intros, simp },
  { intros, simp },
  { intros, simp },
  { intros, simp },
  { intros, simp },
  { intros, simp },
  { intros, simp },
  { intros, simp },
  { intros, simp },
  { intros, simp },
  { intros, simp }
end

lemma deduction_aux {q} (h : T ⊢ q) : ∀ (U) (p) (hT : T = insert p U), U ⊢ p ⟶ q :=
begin
  apply rec_on h,
  { rintros m T q b IH U p rfl,
    have : U.mlift ⊢ p.mlift ⟶ q, from IH U.mlift p.mlift (by simp[preTheory.mlift_insert]),
    have IH : U ⊢ ∀'(p.dummy ⟶ q.pull), from generalize this,
    have : U ⊢ ∀'(p.dummy ⟶ q.pull) ⟶ p ⟶ ∀'q.pull, by simp,
    show U ⊢ p ⟶ ∀'q.pull, from this ⨀ IH },
  { rintros m T p₁ p₂ b₁ b₂ IH₁ IH₂ U p rfl,
    show U ⊢ p ⟶ p₂, from (IH₁ U p rfl) ⨀₁ (IH₂ U p rfl) },
  { rintros m T p hp U r rfl, rcases hp with (rfl | hp),
    { simp }, { have : U ⊢ p, from by_axiom hp, exact hyp_right this r } },
  { rintros m T U p rfl, simp },
  { rintros m T p q U r rfl, simp },
  { rintros m T p q r U s rfl, simp },
  { rintros m T p q U r rfl, simp },
  { rintros m T p t U q rfl, refine hyp_right (specialize _ p t) _ },
  { rintros m T p q U r rfl, refine hyp_right (dummy_univ _ p q) _ },
  { intros, simp },
  { intros, simp },
  { intros, simp },
  { intros, simp },
  { rintros m T _ f U p rfl, refine hyp_right (function_ext _ f) _ },
  { rintros m T _ f U p rfl, refine hyp_right (relation_ext _ f) _ }
end

instance : axiomatic_classical_logic (formula L m) :=
{ deduction' := λ T p q h, deduction_aux h T p rfl,
  weakening := λ T U p ss b, weakening_aux b ss }

lemma empty_axiom_generalize {p : formula L (m + 1)} (hp : ⬝⊢ p) : ⬝⊢ ∀'p.pull :=
by { have : preTheory.mlift ∅ ⊢ p, by simpa[preTheory.mlift] using hp, exact generalize this }

private lemma mlift_list_conjunction (P₀ : list (formula L $ m + 1)) : (∀ p, p ∈ P₀ → p ∈ T.mlift) →
  ∃ P : list (formula L m), P.conjunction.mlift = P₀.conjunction ∧ (∀ p, p ∈ P → p ∈ T) :=
begin
  induction P₀ with p₀ P₀ IH,
  { intros _, refine ⟨[], by simp⟩ },
  { intros h,
    have : ∃ P : list (formula L m), P.conjunction.mlift = P₀.conjunction ∧ (∀ p, p ∈ P → p ∈ T),
    from IH (λ p hp, h p (by simp[hp])),
    rcases this with ⟨P, eq, hP⟩,
    have : p₀ ∈ T.mlift, from h p₀ (by simp), rcases this with ⟨p, hp, rfl⟩,
    refine ⟨p :: P, by simpa using eq, by { rintros q (rfl | hq), { exact hp }, { exact hP q hq } }⟩ }
end

theorem finite_character_aux {m} {T : preTheory L m} {p} :
  T ⊢ p → ∃ P : list (formula L m), (∀ p, p ∈ P → p ∈ T) ∧ ⬝⊢ P.conjunction ⟶ p := λ h,
begin
  apply rec_on h,
  { rintros m T p b ⟨P₀, IH, IHb⟩,
    have : ∃ P : list (formula L m), P.conjunction.mlift = P₀.conjunction ∧ ∀ p, p ∈ P → p ∈ T,
    from mlift_list_conjunction P₀ IH,
    rcases this with ⟨P, eqP, hP⟩,
    refine ⟨P, hP, _⟩,
    have : ⬝⊢ ∀'(P.conjunction.dummy ⟶ p.pull),
    { have := empty_axiom_generalize IHb, rw[←eqP] at this; exact this },
    exact dummy_univ _ P.conjunction p.pull ⨀ this },
  { rintros m T p q b₁ b₂ ⟨P₁, IH₁, IHb₁⟩ ⟨P₂, IH₂, IHb₂⟩,
    refine ⟨P₁ ++ P₂, _, _⟩,
    { simp, rintros p (hp | hp), { exact IH₁ p hp }, { exact IH₂ p hp } },
    { have    : ⬝⊢ (P₁ ++ P₂).conjunction ⟶ P₁.conjunction, from list_conjunction_weakening (by simp),
      have h₁ : ⬝⊢ (P₁ ++ P₂).conjunction ⟶ p ⟶ q, from imply_trans this IHb₁,
      have    : ⬝⊢ (P₁ ++ P₂).conjunction ⟶ P₂.conjunction, from list_conjunction_weakening (by simp),
      have h₂ : ⬝⊢ (P₁ ++ P₂).conjunction ⟶ p, from imply_trans this IHb₂,
      exact h₁ ⨀₁ h₂ } },
  { rintros m T p hp, refine ⟨[p], by simp[hp], _⟩, simp, refine deduction.mp (by simp) },
  { rintros m T, refine ⟨[], by simp, by simp[empty_axiom]⟩ },
  { rintros m T p q, refine ⟨[], by simp, by simp[empty_axiom]⟩ },
  { rintros m T p q r, refine ⟨[], by simp, by simp[empty_axiom]⟩ },
  { rintros m T p q, refine ⟨[], by simp, by simp[empty_axiom]⟩ },
  { rintros m T p t, refine ⟨[], by simp, by simp[empty_axiom]⟩ },
  { rintros m T p q, refine ⟨[], by simp, by simp[empty_axiom]⟩ },
  { rintros m T, refine ⟨[], by simp, by simp[empty_axiom]⟩ },
  { rintros m T, refine ⟨[], by simp, by simp[empty_axiom]⟩ },
  { rintros m T, refine ⟨[], by simp, by simp[empty_axiom]⟩ },
  { rintros m T, refine ⟨[], by simp, by simp[empty_axiom]⟩ },
  { rintros m T p f, refine ⟨[], by simp, by simp[empty_axiom]⟩ },
  { rintros m T p r, refine ⟨[], by simp, by simp[empty_axiom]⟩ },
end

instance : has_finite_character (formula L m) :=
finite_character_of_finite_provable (formula L m) (λ T p, finite_character_aux)

lemma exists_of_subst (p : subformula L m 1) (t) : T ⊢ subst t p ⟶ ∃'p :=
contrapose.mp (imply_of_equiv
  (show T ⊢ p.neg.fal ⟶ ∼subst t p, by simpa using specialize T (∼p) t)
  (iff_dn_refl_right $ ∀'∼p) (equiv_refl _))

lemma specialize' {T} (p : subformula L m 1) : T ⊢ ∀' 𝗟 p ⟶ 𝗠 p :=
by { have : T ⊢ ∀' 𝗟 p ⟶ subst &0 p.mlift, from specialize T p.mlift &0, simpa using this }

lemma use {p : subformula L m 1} (t) (h : T ⊢ subst t p) : T ⊢ ∃'p :=
exists_of_subst p t ⨀ h

@[simp] lemma forall_top : T ⊢ ∀'⊤ :=
gen (by simp)

lemma forallK (p q) : T ⊢ ∀'(p ⟶ q) ⟶ ∀'p ⟶ ∀'q :=
begin
  have lmm₁ : T ⊢ ∀'(p ⟶ q) ⟶ ∀'(𝗗 (∀' p) ⟶ q),
  { have : 𝗟'T +{ ∀'(𝗟 p ⟶ 𝗟 q) } ⊢ 𝗠 p ⟶ 𝗠 q, from deduction.mpr (by simpa using specialize' (p ⟶ q)),
    have : 𝗟'T +{ ∀'(𝗟 p ⟶ 𝗟 q) } ⊢ ∀'𝗟 p ⟶ 𝗠 q, from imply_trans (specialize' _) this, 
    refine deduction.mp (gen _), simp[preTheory.mlift_insert], exact this },
  have lmm₂ : T ⊢ ∀'(𝗗 (∀'p) ⟶ q) ⟶ ∀'p ⟶ ∀'q, from dummy_univ T (∀'p) q,
  exact imply_trans lmm₁ lmm₂
end

lemma forall_of_equiv {p₁ p₂} (h : T ⊢ ∀' p₁) (hp : 𝗟'T ⊢ 𝗠 p₁ ⟷ 𝗠 p₂) : T ⊢ ∀' p₂ :=
by { have : T ⊢ ∀'(p₁ ⟶ p₂), by simpa using generalize (iff_equiv.mp hp).1,
     exact (forallK _ _) ⨀ this ⨀ h }

lemma equiv_forall_of_equiv {p₁ p₂} (hp : 𝗟'T ⊢ 𝗠 p₁ ⟷ 𝗠 p₂) : T ⊢ ∀'p₁ ⟷ ∀'p₂ :=
by { simp[iff_equiv], split,
  { have : T ⊢ ∀'(p₁ ⟶ p₂), by simpa using generalize (iff_equiv.mp hp).1,
    exact forallK _ _ ⨀ this },
  { have : T ⊢ ∀'(p₂ ⟶ p₁), by simpa using generalize (iff_equiv.mp hp).2,
    exact forallK _ _ ⨀ this } }

lemma equiv_forall_of_equiv' {p₁ p₂} (hp : 𝗟'T ⊢ p₁ ⟷ p₂) : T ⊢ ∀' 𝗡 p₁ ⟷ ∀' 𝗡 p₂ :=
@equiv_forall_of_equiv _ _ T (𝗡 p₁) (𝗡 p₂) (by simpa using hp)

lemma equiv_exists_of_equiv {p₁ p₂} (hp : 𝗟'T ⊢ 𝗠 p₁ ⟷ 𝗠 p₂) : T ⊢ ∃'p₁ ⟷ ∃'p₂ :=
by simp[ex_def]; refine equiv_neg_of_equiv (equiv_forall_of_equiv (by simpa using equiv_neg_of_equiv hp))

lemma equiv_exists_of_equiv' {p₁ p₂} (hp : 𝗟'T ⊢ p₁ ⟷ p₂) : T ⊢ ∃' 𝗡 p₁ ⟷ ∃' 𝗡 p₂ :=
@equiv_exists_of_equiv _ _ T (𝗡 p₁) (𝗡 p₂) (by simpa using hp)

lemma univ_imply_dummy (p : subformula L m 1) (q : subformula L m 0) :
  T ⊢ ∀'(p ⟶ 𝗗 q) ⟶ ∃'p ⟶ q :=
begin
  have : T ⊢ ∀'(∼𝗗 q ⟶ ∼p) ⟶ ∼q ⟶ ∀'∼p, by simpa using dummy_univ T (∼q) (∼p),
  refine imply_of_equiv this (equiv_forall_of_equiv (by simp)) (by simp[ex_def])
end

lemma exists_intro (p : subformula L m 1) (q : subformula L m 0)
  (h : 𝗟'T ⊢ 𝗠 p ⟶ 𝗟 q) : T ⊢ ∃'p ⟶ q :=
by { have : T ⊢ ∀'(p ⟶ 𝗗 q), by simpa using generalize h,
     exact univ_imply_dummy p q ⨀ this }

@[simp] lemma forall_bot : T ⊢ ∀'⊥ ⟷ ⊥ :=
by { simp[iff_equiv],
     have : T ⊢ ∼∀'∼⊤, by simp[←ex_def],
     refine of_equiv (neg_of_equiv this (equiv_forall_of_equiv (by simp)))
     (neg_iff (∀'⊥)) }

@[simp] lemma forall_dummy (p : formula L m) : T ⊢ ∀'𝗗 p ⟷ p :=
begin
  simp[iff_equiv], split,
  { have : T ⊢ ∀'(⊤ ⟶ 𝗗 p) ⟶ ∃'⊤ ⟶ p, from univ_imply_dummy ⊤ p,
    refine imply_of_equiv this (equiv_forall_of_equiv $ by simp) (by simp) },
  { refine deduction.mp (gen $ by simp) }
end

section prenex_normal_form

lemma neg_forall_pnf (p) : T ⊢ ∼∀'p ⟷ ∃'∼p :=
equiv_neg_of_equiv (equiv_forall_of_equiv (by simp[neg_eq]))

lemma neg_univ_closure_pnf {n} (p : subformula L m n) : T ⊢ ∼∀'*p ⟷ ∃'*∼p :=
begin
  induction n with n IH generalizing m, { simp },
  { simp[forall_comm, subformula.exists_comm],
    have lmm₁ : T ⊢ ∼∀'𝗡 (∀'* 𝗠 p) ⟷ ∃'∼𝗡 (∀'* 𝗠 p), from neg_forall_pnf _,
    have : 𝗟'T ⊢ ∼∀'* (𝗠 p) ⟷ ∃'* (∼𝗠 p), from IH (𝗠 p),
    have lmm₂ : T ⊢ ∃'∼𝗡 (∀'* 𝗠 p) ⟷ ∃'𝗡 (∃'* ∼𝗠 p), by simpa using equiv_exists_of_equiv' this,
    exact equiv_trans lmm₁ lmm₂ }
end

lemma neg_exists_pnf (p) : T ⊢ ∼∃'p ⟷ ∀'∼p := by simp[ex_def]

lemma neg_exists_closure_pnf {n} (p : subformula L m n) : T ⊢ ∼∃'*p ⟷ ∀'*∼p :=
begin
  induction n with n IH generalizing m, { simp },
  { simp[forall_comm, subformula.exists_comm],
    have lmm₁ : T ⊢ ∼∃'𝗡 (∃'* 𝗠 p) ⟷ ∀'∼𝗡 (∃'* 𝗠 p), from neg_exists_pnf _,
    have : 𝗟'T ⊢ ∼∃'* (𝗠 p) ⟷ ∀'* (∼𝗠 p), from IH (𝗠 p),
    have lmm₂ : T ⊢ ∀'∼𝗡 (∃'* 𝗠 p) ⟷ ∀'𝗡 (∀'* ∼𝗠 p), by simpa using equiv_forall_of_equiv' this,
    exact equiv_trans lmm₁ lmm₂ }
end

@[simp] lemma or_forall_pnf (p q) : T ⊢ (∀'p) ⊔ q ⟷ ∀'(p ⊔ 𝗗 q) :=
begin
  have lmm₁ : T ⊢ (∀'p) ⊔ q ⟶ ∀'(p ⊔ 𝗗 q),
  { have : 𝗟'T ⊢ (∀'𝗟 p) ⊔ 𝗟 q ⟶ 𝗠 p ⊔ 𝗟 q,
    { have : 𝗟'T ⊢ ∀'𝗟 p ⟶ 𝗠 p, from specialize' p,
      exact or_imply (∀'𝗟 p) (𝗟 q) (𝗠 p ⊔ 𝗟 q) ⨀ (imply_trans this (by simp)) ⨀ (by simp) },
    have : 𝗟'(T +{ (∀'p) ⊔ q }) ⊢ 𝗠 p ⊔ 𝗟 q, simpa using deduction.mpr this,
    have : T +{ (∀'p) ⊔ q } ⊢ ∀'(p ⊔ 𝗗 q), by simpa using generalize this,
    exact deduction.mp this },
  have lmm₂ : T ⊢ ∀'(p ⊔ 𝗗 q) ⟶ (∀'p) ⊔ q,
  { simp[has_sup.sup, subformula.or, imply_eq, neg_eq],
    have : T ⊢ ∀'(∼p ⟶ 𝗗 q) ⟶ ∃'∼p ⟶ q, from univ_imply_dummy (∼p) q,
    refine imply_of_equiv this (by simp) (equiv_imply_of_equiv (equiv_symm (neg_forall_pnf p)) (by simp)) },
  refine iff_equiv.mpr ⟨lmm₁, lmm₂⟩
end

@[simp] lemma and_exists_pnf (p q) : T ⊢ (∃'p) ⊓ q ⟷ ∃'(p ⊓ 𝗗 q) :=
begin
  have : T ⊢ (∀'∼p) ⊔ ∼q ⟷ ∀'∼p ⊔ 𝗗 (∼q), from or_forall_pnf (∼p) (∼q),
  refine equiv_of_equiv (equiv_neg_of_equiv this) _ _,
  { show T ⊢ ∼((∀'∼p) ⊔ ∼q) ⟷ (∃'p) ⊓ q,
    refine equiv_of_equiv (neg_or_equiv_and_neg (∀'∼p) (∼q))
      (equiv_refl _) (equiv_and_of_equiv (equiv_refl _) (iff_dn_refl_left q)) },
  { show T ⊢ ∼∀'(∼p ⊔ 𝗗 (∼q)) ⟷ ∃'(p ⊓ 𝗗 q),
    refine equiv_neg_of_equiv (equiv_forall_of_equiv $ equiv_symm (by simp[neg_eq])) }
end

@[simp] lemma and_forall_pnf (p q) : T ⊢ (∀'p) ⊓ q ⟷ ∀'(p ⊓ 𝗗 q) :=
begin
  have lmm₁ : T ⊢ (∀'p) ⊓ q ⟶ ∀'(p ⊓ 𝗗 q),
  { have : 𝗟'T ⊢ (∀'𝗟 p) ⊓ 𝗟 q ⟶ 𝗠 p ⊓ 𝗟 q,
    { have : 𝗟'T ⊢ ∀'𝗟 p ⟶ 𝗠 p, from specialize' p,
      exact imply_and ((∀'𝗟 p) ⊓ 𝗟 q) (𝗠 p) (𝗟 q) ⨀ (imply_trans (by simp) this) ⨀ (by simp) },
    have : 𝗟'(T +{ (∀'p) ⊓ q }) ⊢ 𝗠 p ⊓ 𝗟 q, simpa using deduction.mpr this,
    have : T +{ (∀'p) ⊓ q } ⊢ ∀'(p ⊓ 𝗗 q), by simpa using generalize this,
    exact deduction.mp this },
  have lmm₂ : T ⊢ ∀'(p ⊓ 𝗗 q) ⟶ (∀'p) ⊓ q,
  { have lmm₃ : T ⊢ ∀'(p ⊓ 𝗗 q) ⟶ ∀'p, from forallK (p ⊓ 𝗗 q) p ⨀ (gen $ by simp),
    have lmm₄ : T ⊢ ∀'(p ⊓ 𝗗 q) ⟶ q,
    { have : T ⊢ ∀'(p ⊓ 𝗗 q) ⟶ ∀'𝗗 q, from forallK (p ⊓ 𝗗 q) (𝗗 q) ⨀ (gen $ by simp),
      refine imply_trans this (equiv_mp (forall_dummy _)) },
    refine imply_and (∀'(p ⊓ 𝗗 q)) (∀'p) q ⨀ lmm₃ ⨀ lmm₄ },
  refine iff_equiv.mpr ⟨lmm₁, lmm₂⟩
end

@[simp] lemma or_exists_pnf (p q) : T ⊢ (∃'p) ⊔ q ⟷ ∃'(p ⊔ 𝗗 q) :=
begin
  have : T ⊢ (∀'∼p) ⊓ ∼q ⟷ ∀'∼p ⊓ 𝗗 (∼q), from and_forall_pnf (∼p) (∼q),
  have := equiv_neg_of_equiv this,
  refine equiv_of_equiv this _ _,
  { show T ⊢ ∼((∀'∼p) ⊓ ∼q) ⟷ (∃'p) ⊔ q,
    refine equiv_of_equiv (neg_and_equiv_or_neg (∀'∼p) (∼q))
      (equiv_refl _) (equiv_or_of_equiv (equiv_refl _) (iff_dn_refl_left q)) },
  { show T ⊢ ∼∀'(∼p ⊓ 𝗗 (∼q)) ⟷ ∃'(p ⊔ 𝗗 q),
    refine equiv_neg_of_equiv (equiv_forall_of_equiv $ equiv_symm (by simp[neg_eq])) }
end

lemma imply_forall_pnf (p q) : T ⊢ (p ⟶ ∀'q) ⟷ ∀'(𝗗 p ⟶ q) :=
by { have : T ⊢ ((∀'q) ⊔ ∼p) ⟷ ∀'(q ⊔ ∼𝗗 p), by simpa using or_forall_pnf q ∼p,
     exact equiv_of_equiv this (equiv_symm (by simp))
       (equiv_forall_of_equiv (equiv_symm (by simp))) }

lemma imply_exists_pnf (p q) : T ⊢ (p ⟶ ∃'q) ⟷ ∃'(𝗗 p ⟶ q) :=
by{ have : T ⊢ ((∃'q) ⊔ ∼p) ⟷ ∃'(q ⊔ ∼𝗗 p), by simpa using or_exists_pnf q ∼p,
    refine equiv_of_equiv this (equiv_symm impl_iff_or')
      (equiv_exists_of_equiv $ equiv_symm $ by simp)}

lemma exists_imply_pnf (p q) : T ⊢ (∃'p ⟶ q) ⟷ ∀'(p ⟶ 𝗗 q) :=
by{ have : T ⊢ ((∀'∼p) ⊔ q) ⟷ ∀'(∼p ⊔ 𝗗 q), by simp,
    refine equiv_of_equiv this _ _,
    { have : T ⊢ (∼∼∀'∼p) ⊔ q ⟷ ∃'p ⟶ q, from equiv_symm (by simp[ex_def]),
      refine equiv_trans (equiv_or_of_equiv _ _) this; simp },
    { refine equiv_forall_of_equiv (equiv_symm $ by simp) } }

lemma forall_imply_pnf (p q) : T ⊢ (∀'p ⟶ q) ⟷ ∃'(p ⟶ 𝗗 q) :=
by{ have : T ⊢ ((∃'∼p) ⊔ q) ⟷ ∃'(∼p ⊔ 𝗗 q), by simp,
    refine equiv_of_equiv this _ _,
    { have : T ⊢ (∃'∼p) ⊔ q ⟷ ∀'∼∼p ⟶ q, from equiv_symm (by simp[ex_def]),
      refine equiv_trans this (equiv_imply_of_equiv (equiv_forall_of_equiv _) _); simp },
    { refine equiv_exists_of_equiv (equiv_symm $ by simp) } }

lemma forall_imply_forall_pnf (p q) : T ⊢ (∀'p ⟶ ∀'q) ⟷ ∃' ∀'(𝗡 𝗗 𝗠 p ⟶ 𝗗 q) :=
begin
  have : 𝗟'T ⊢ (𝗠 p ⟶ ∀'𝗟 q) ⟷ ∀'(𝗗 𝗠 p ⟶ 𝗟 q), from imply_forall_pnf (𝗠 p) (𝗟 q),
  have lmm₁ : T ⊢ ∃'(p ⟶ ∀' 𝗗 q) ⟷ ∃' ∀'(𝗡 𝗗 𝗠 p ⟶ 𝗗 q),
    from equiv_exists_of_equiv (by simpa using this),
  have lmm₂ : T ⊢ (∀'p ⟶ ∀'q) ⟷ ∃'(p ⟶ ∀' 𝗗 q), by simpa using forall_imply_pnf p (∀'q),
  exact equiv_trans lmm₂ lmm₁
end

lemma forall_imply_exists_pnf (p q) : T ⊢ (∀'p ⟶ ∃'q) ⟷ ∃' ∃'(𝗡 𝗗 𝗠 p ⟶ 𝗗 q) :=
begin
  have : 𝗟'T ⊢ (𝗠 p ⟶ ∃'𝗟 q) ⟷ ∃'(𝗗 𝗠 p ⟶ 𝗟 q), from imply_exists_pnf (𝗠 p) (𝗟 q),
  have lmm₁ : T ⊢ ∃'(p ⟶ ∃' 𝗗 q) ⟷ ∃' ∃'(𝗡 𝗗 𝗠 p ⟶ 𝗗 q),
    from equiv_exists_of_equiv (by simpa using this),
  have lmm₂ : T ⊢ (∀'p ⟶ ∃'q) ⟷ ∃'(p ⟶ ∃' 𝗗 q), by simpa using forall_imply_pnf p (∃'q),
  exact equiv_trans lmm₂ lmm₁
end

lemma exists_imply_forall_pnf (p q) : T ⊢ (∃'p ⟶ ∀'q) ⟷ ∀' ∀'(𝗡 𝗗 𝗠 p ⟶ 𝗗 q) :=
begin
  have : 𝗟'T ⊢ (𝗠 p ⟶ ∀'𝗟 q) ⟷ ∀'(𝗗 𝗠 p ⟶ 𝗟 q), from imply_forall_pnf (𝗠 p) (𝗟 q),
  have lmm₁ : T ⊢ ∀'(p ⟶ ∀' 𝗗 q) ⟷ ∀' ∀'(𝗡 𝗗 𝗠 p ⟶ 𝗗 q),
    from equiv_forall_of_equiv (by simpa using this),
  have lmm₂ : T ⊢ (∃'p ⟶ ∀'q) ⟷ ∀'(p ⟶ ∀' 𝗗 q), by simpa using exists_imply_pnf p (∀'q),
  exact equiv_trans lmm₂ lmm₁
end

lemma exists_imply_exists_pnf (p q) : T ⊢ (∃'p ⟶ ∃'q) ⟷ ∀' ∃'(𝗡 𝗗 𝗠 p ⟶ 𝗗 q) :=
begin
  have : 𝗟'T ⊢ (𝗠 p ⟶ ∃'𝗟 q) ⟷ ∃'(𝗗 𝗠 p ⟶ 𝗟 q), from imply_exists_pnf (𝗠 p) (𝗟 q),
  have lmm₁ : T ⊢ ∀'(p ⟶ ∃' 𝗗 q) ⟷ ∀' ∃'(𝗡 𝗗 𝗠 p ⟶ 𝗗 q),
    from equiv_forall_of_equiv (by simpa using this),
  have lmm₂ : T ⊢ (∃'p ⟶ ∃'q) ⟷ ∀'(p ⟶ ∃' 𝗗 q), by simpa using exists_imply_pnf p (∃'q),
  exact equiv_trans lmm₂ lmm₁
end

end prenex_normal_form

section equal
variables {m} {n : ℕ}

lemma specialize_foralls (p : subformula L m n) (w : fin n → subterm L m 0) : T ⊢ ∀'*p ⟶ substs w p :=
begin
  induction n with n IH generalizing m,
  { simp },
  { have : 𝗟'T ⊢ ∀'* 𝗠 p ⟶ substs (mlift ∘ w ∘ fin.cast_succ) (𝗠 p),
    from IH (𝗠 p) (subterm.mlift ∘ w ∘ fin.cast_succ),
    have : T ⊢ ∀'(𝗡 (∀'*𝗠 p) ⟶ 𝗡 (substs (mlift ∘ w ∘ fin.cast_succ) (𝗠 p))),
    by simpa using generalize this,
    have lmm₁ : T ⊢ ∀'*p ⟶ ∀'𝗡 (substs (mlift ∘ w ∘ fin.cast_succ) (𝗠 p)),
    by simpa[forall_comm] using forallK _ _ ⨀ this,
    have lmm₂ : T ⊢ ∀'𝗡 (substs (mlift ∘ w ∘ fin.cast_succ) (𝗠 p)) ⟶ substs w p,
    from specialize T (𝗡 (substs (mlift ∘ w ∘ fin.cast_succ) (𝗠 p))) (w $ fin.last n),
    exact imply_trans lmm₁ lmm₂ }
end

lemma exists_dn (p : subformula L m n) : T ⊢ ∃'*∼∼p ⟷ ∃'*p :=
begin
  induction n with n IH generalizing m; simp[subformula.exists_comm],
  refine equiv_exists_of_equiv (by simpa using IH (𝗠 p))
end

lemma exists_of_substs (p : subformula L m n) (w : fin n → subterm L m 0) : T ⊢ ∀'*p ⟶ substs w p :=
begin
  induction n with n IH generalizing m,
  { simp },
  { have : 𝗟'T ⊢ ∀'* 𝗠 p ⟶ substs (mlift ∘ w ∘ fin.cast_succ) (𝗠 p),
    from IH (𝗠 p) (subterm.mlift ∘ w ∘ fin.cast_succ),
    have : T ⊢ ∀'(𝗡 (∀'*𝗠 p) ⟶ 𝗡 (substs (mlift ∘ w ∘ fin.cast_succ) (𝗠 p))),
    by simpa using generalize this,
    have lmm₁ : T ⊢ ∀'*p ⟶ ∀'𝗡 (substs (mlift ∘ w ∘ fin.cast_succ) (𝗠 p)),
    by simpa[forall_comm] using forallK _ _ ⨀ this,
    have lmm₂ : T ⊢ ∀'𝗡 (substs (mlift ∘ w ∘ fin.cast_succ) (𝗠 p)) ⟶ substs w p,
    from specialize T (𝗡 (substs (mlift ∘ w ∘ fin.cast_succ) (𝗠 p))) (w $ fin.last n),
    exact imply_trans lmm₁ lmm₂ }
end

lemma foralls_substs {p : subformula L m n} (h : T ⊢ ∀'*p) (w) : T ⊢ substs w p :=
specialize_foralls p w ⨀ h

@[refl, simp] lemma eq_refl' (t : subterm L m 0) : T ⊢ t =' t :=
by simpa using eq_refl T ⊚ t

@[simp] lemma eq_symm' (t u : subterm L m 0) : T ⊢ (t =' u) ⟶ (u =' t) :=
begin
  have : T ⊢ ∀'(_ ⟶ _), by simpa using eq_symm T ⊚ u,
  have : T ⊢ _ ⟶ _, by simpa using this ⊚ t, simp at this,
  simp only [show (0 : fin (0 + 1 + 1)) = (fin.last 0).cast_succ, by refl,
             show (1 : fin (0 + 1 + 1)) = fin.last 1, by refl,
             subst_var_cast_succ,
             subst_var_last,
             subst_mlift,
             subst_zero,
             subst_lift_lift] at this,
  assumption
end

@[symm] lemma equal_symm {t u : subterm L m 0} : T ⊢ t =' u → T ⊢ u =' t :=
λ h, eq_symm' t u ⨀ h

@[simp] lemma eq_trans' (t₁ t₂ t₃: subterm L m 0) : T ⊢ (t₁ =' t₂) ⟶ (t₂ =' t₃) ⟶ (t₁ =' t₃) :=
begin
  have : T ⊢ ∀' ∀'(_ ⟶ _ ⟶ _), by simpa using eq_trans T ⊚ t₃,
  have : T ⊢ ∀'(_ ⟶ _ ⟶ _), by simpa using this ⊚ t₂,
  have : T ⊢ _ ⟶ _ ⟶ _, by simpa using this ⊚ t₁, simp at this,
  simp only [show (0 : fin (0 + 1 + 1 + 1)) = (fin.last 0).cast_succ.cast_succ, by refl,
             show (2 : fin (0 + 1 + 1 + 1)) = fin.last _, by refl] at this,
  simp only [show (1 : fin (0 + 1 + 1 + 1)) = (fin.last 1).cast_succ, by refl,
             subst_var_cast_succ,
             subst_var_last,
             subst_mlift,
             subst_zero,
             subst_lift_lift] at this,
  exact this
end

@[trans] lemma equal_trans (t₁ t₂ t₃: subterm L m 0) : T ⊢ t₁ =' t₂ → T ⊢ t₂ =' t₃ → T ⊢ t₁ =' t₃ :=
λ h₁ h₂, eq_trans' t₁ t₂ t₃ ⨀ h₁ ⨀ h₂

@[simp] lemma function_ext' {k} (f : L.fn k) (v w : fin k → subterm L m 0) :
  T ⊢ (⋀ i, v i =' w i) ⟶ (function f v =' function f w) :=
begin
  let x : fin (k + k) → subterm L m 0 := @fin.add_cases k k (λ _, subterm L m 0) v w,
  have : T ⊢ ∀'*((⋀ i, #(fin.cast_add k i) =' #(fin.nat_add k i)) ⟶
    (function f (var ∘ fin.cast_add k) =' function f (var ∘ fin.nat_add k))), from function_ext T f,
  simpa[x, (∘)] using foralls_substs this x
end

lemma eq_function_of_equal {k} (f : L.fn k) {v w : fin k → subterm L m 0}
  (h : ∀ i, T ⊢ v i =' w i) : T ⊢ function f v =' function f w :=
function_ext' f v w ⨀ by simpa using h

@[simp] lemma relation_ext' {k} (r : L.pr k) (v w : fin k → subterm L m 0) :
  T ⊢ (⋀ i, v i =' w i) ⟶ (relation r v ⟷ relation r w) :=
begin
  let x : fin (k + k) → subterm L m 0 := @fin.add_cases k k (λ _, subterm L m 0) v w,
  have : T ⊢ ∀'*((⋀ i, #(fin.cast_add k i) =' #(fin.nat_add k i)) ⟶
    (relation r (var ∘ fin.cast_add k) ⟷ relation r (var ∘ fin.nat_add k))), from relation_ext T r,
  simpa[x, (∘)] using foralls_substs this x
end

lemma equiv_relation_of_equal {k} (r : L.pr k) {v w : fin k → subterm L m 0}
  (h : ∀ i, T ⊢ v i =' w i) : T ⊢ relation r v ⟷ relation r w :=
relation_ext' r v w ⨀ by simpa using h

end equal

end provable

end fol