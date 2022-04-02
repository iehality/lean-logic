import language_extension consistency lindenbaum
open encodable

universes u

namespace fopl

@[simp] lemma app_concat {α β : Type*} (a : α) (s : ℕ → α) (g : α → β) :
  (λ x, g ((a ⌢ s) x)) = g a ⌢ g ∘ s :=
by { funext x, cases x; simp  }

@[simp] lemma app_concat' {α β γ : Type*} (a : α) (s : ℕ → α) (g : α → β) (h : β → γ):
  (λ x, h (g ((a ⌢ s) x))) = h (g a) ⌢ h ∘ g ∘ s :=
by { funext x, cases x; simp  }

open term formula
variables (L : language.{u}) (T : theory L)

namespace henkin
open language language.extension language.consts_pelimination theory language.language_translation

@[reducible] def extend : language.{u} := L + consts (formula L)

variables {L}

def henkin_axiom (p : formula L) : formula (extend L) := (∐ ↑p) ⟶ rew ı[0 ⇝ p] ↑p

@[reducible] def theory_extend : theory (extend L) := ↑T ∪ set.range henkin_axiom

variables {T}

section
open axiomatic_classical_logic axiomatic_classical_logic' provable

variables {S : theory (extend L)} (Γ : list (formula L))

lemma consistent_of_disjoint (S_consis : S.consistent) (disj : ∀ p ∈ S, disjoint Γ p) (p : formula (extend L)) :
  ¬S ⊢ (∏[Γ.length] ⁻((pelimination' Γ).p 0 p)) → theory.consistent (S +{ p }) := λ not_b,
begin
  simp [theory.consistent_iff_bot],
  intros b,
  have : S ⊢ ⁻p, from of_equiv_p (deduction.mp b) (equiv_symm $ neg_iff _),
  have : S ⊢ ∏[Γ.length] ⁻(pelimination' Γ).p 0 p,
  { have := provable_pelimination_of_disjoint Γ S (⁻p) disj this, simp at this, exact this },
  contradiction
end

lemma tauto (p : formula L) : S ⊢ ∐ ((∐ ↑p)^1 ⟶ ↑p) :=
begin
  have lmm₁ : S ⊢ (∐ ↑p) ⟶ ∐ ((∐ ↑p)^1 ⟶ ↑p),
  { simp[pnf_imply_ex_iff_fal_imply₁], refine generalize (deduction.mp _),
    refine use #0 _, simp[formula.nested_rew] },
  have lmm₂ : S ⊢ ⁻(∐ ↑p) ⟶ ∐ ((∐ ↑p)^1 ⟶ ↑p),
  { refine deduction.mp (use #0 (deduction.mp _)), simp,
    show S +{ ⁻∐ ↑p } +{ ∐ ↑p } ⊢ rew ı[0 ⇝ #0] ↑p,
    exact explosion (show S +{ ⁻∐ ↑p } +{ ∐ ↑p } ⊢ ∐ ↑p, by simp) (show S +{ ⁻∐ ↑p } +{ ∐ ↑p } ⊢ ⁻∐ ↑p, by simp) },
  exact cases_of _ _ lmm₁ lmm₂
end

@[simp] lemma pelimination'_henkin_axiom (p : formula L) : (pelimination' ([p])).p 0 (henkin_axiom p) = ((∐ ↑p)^1 ⟶ ↑p) :=
begin
  simp[henkin_axiom, pelimination'_subst, pelimination_coe_eq_pow_coe_aux],
  have : pelim_aux_t ([p]) 0 ↑↑p = (#0 : term (extend L)),
  { have : pelim_aux_t ([p]) 0 ↑p = (#(list.index_of p ([p]) + 0) : term (extend L)), from pelim_aux_t_consts_of_Γ ([p]) p (by simp) 0,
    simp at this, exact this },
  simp[this, formula.nested_rew, show (#0 ⌢ λ x, #(1 + x) : ℕ → term (extend L)) = ı, by { funext x, rcases x; simp[add_comm 1] }],
  simp[formula.pow_eq, add_comm 1]
end

lemma consts_of_henkin_axiom {p : formula L} {c} (mem : c ∈ consts_of_p (henkin_axiom p)) : c = p :=
begin
  simp[henkin_axiom, consts_of_p] at mem,
  rcases mem with ⟨t, (t_mem | t_mem), c_mem⟩,
  { rcases language_translation_coe.fun_p_inversion_of_mem t_mem with ⟨t, t_mem, rfl⟩, simp at c_mem, contradiction },
  { rcases formula.rew_inversion_or_le_of_mem_rew t_mem with (⟨t, t_mem', k, rfl⟩ | ⟨k, n, le⟩),
    { rcases language_translation_coe.fun_p_inversion_of_mem t_mem' with ⟨t, t_mem'', rfl⟩,
      simp[subst_pow] at c_mem,
      rcases mem_of_consts_of_t_subst _ _ _ c_mem with (c_mem | c_mem),
      { simp at c_mem, contradiction },
      {exact eq_of_consts_of_t_coe.mp c_mem } },
    { simp[subst_pow] at le, have : n < k ∨ n = k ∨ k < n , exact trichotomous n k, rcases this with (lt | rfl | lt),
      { simp[lt] at le, simp[le] at c_mem, contradiction },
      { simp[consts.coe_def, show (↑(consts.c p) : (extend L).fn 0) = sum.inr (consts.c p), from rfl, le_iff_lt_or_eq] at le,
        rcases le with (⟨⟨_, A⟩, _⟩ | rfl), { simp at A, contradiction }, { simp at c_mem, exact c_mem } },
      { simp[lt] at le, simp[le] at c_mem, contradiction } } }
end

lemma disjoint_of_ne (p q : formula L) (ne : p ≠ q) : disjoint ([p]) (henkin_axiom q) := λ p mem,
by { simp at mem, rcases mem with rfl, intros mem, have : p = q, from consts_of_henkin_axiom mem, contradiction }

end

theorem theory_extend_consistent (consis : T.consistent) : (theory_extend T).consistent :=
begin
  have : (↑T : theory (extend L)).consistent, from language.add_consts.consistent_iff.mpr consis,
  refine consistent.of_finite_induction this _,
  intros s s_ss φ φ_mem p_nmem s_fin consis',
  let U := ↑T ∪ s,
  rcases φ_mem with ⟨φ, rfl⟩,
  show theory.consistent (U +{ henkin_axiom φ }),
  have disj : ∀ p ∈ U, disjoint ([φ]) p,
  { intros p mem, simp[U] at mem, rcases mem,
    { rcases mem with ⟨p, mem, rfl⟩, show disjoint ([φ]) (↑p), intros h, simp },
    { have : p ∈ set.range henkin_axiom, from s_ss mem,
      rcases this with ⟨p, rfl⟩,
      have : φ ≠ p, { rintros rfl, contradiction },
      exact disjoint_of_ne _ _ this } },
  have : ¬U ⊢ ∏ ⁻((∐ ↑φ)^1 ⟶ ↑φ),
  { intros b,
    have : U ⊢ ⁻∏ ⁻((∐ ↑φ)^1 ⟶ ↑φ), from tauto φ,
    have : ¬U.consistent, { simp[theory.consistent], refine ⟨_, b, this⟩ },
    contradiction },
  exact consistent_of_disjoint ([φ]) consis' disj (henkin_axiom φ) (by simp; exact this)
end

variables (L) (T)

@[reducible] def Lang : ℕ → language
| 0     := L
| (n+1) := extend (Lang n)

local notation `L[` n `]` := Lang L n

@[reducible] def Consts : Type u := Σ n, formula (Lang L n)

def pConsts (m : ℕ) : Type u := Σ (n : {n | m ≤ n}), formula (Lang L n)

@[reducible] def limit : language := L + consts (Consts L)  

local notation `Lω` := limit L

local infix ` ≃∘ `:50 := ((≃) : term Lω → term Lω → formula Lω)

@[reducible] def Ln_to_Lω : Π n, L[n] ↝ᴸ Lω
| 0     := add_left
| (n+1) := let σ : consts (formula L[n]) ↝ᴸ consts (Consts L) := consts_of_fun (λ p, ⟨n, p⟩) in
    (Ln_to_Lω n).sum (add_right.comp σ)

def pConsts_to_add_pConsts (n : ℕ) : consts (pConsts L n) ↝ᴸ consts (formula L[n]) + consts (pConsts L (n + 1)) :=
{ fn := λ m f, by { rcases m,
    { rcases f with ⟨⟨i, hi⟩, p⟩, simp at hi p,
      by_cases e : i = n,
      { rcases e with rfl, refine sum.inl p },
      { have : n + 1 ≤ i, from nat.succ_le_iff.mpr ((ne.symm e).le_iff_lt.mp hi), refine sum.inr ⟨⟨i, this⟩, p⟩ } },
    { rcases f } },
  pr := λ m r, by { rcases r } }

@[reducible] def Lω_to_Ln_add_pConsts : Π n, Lω ↝ᴸ L[n] + consts (pConsts L n)
| 0       := (1 : L ↝ᴸ L).add (consts_of_fun (λ ⟨n, p⟩, ⟨⟨n, by simp⟩, p⟩))
| (n + 1) :=
  let τ : L[n] + consts (pConsts L n) ↝ᴸ L[n + 1] + consts (pConsts L (n + 1)) := (add_assoc'_inv _ _ _).comp ((1 : L[n] ↝ᴸ L[n]).add ( pConsts_to_add_pConsts L n)) in
    τ.comp (Lω_to_Ln_add_pConsts n)

lemma pConsts_to_add_pConsts_of_eq {n : ℕ} (p : formula L[n]) :
  (pConsts_to_add_pConsts L n).fn 0 (consts.c ⟨⟨n, by { show n ≤ n, by refl }⟩, p⟩) = sum.inl p :=
by simp[pConsts_to_add_pConsts, consts.c]

lemma pConsts_to_add_pConsts_of_lt {n m : ℕ} (p : formula L[m]) (lt : n < m) :
  (pConsts_to_add_pConsts L n).fn 0 (consts.c ⟨⟨m, le_of_lt lt⟩, p⟩) = sum.inr (consts.c ⟨⟨m, nat.succ_le_iff.mpr lt⟩, p⟩) :=
by simp[pConsts_to_add_pConsts, consts.c, show ¬m = n, from ne_of_gt lt]

lemma Lω_to_Ln_add_pConst_fn_of_le {n m : ℕ} (p : formula L[m]) (le : n ≤ m) :
  (Lω_to_Ln_add_pConsts L n).fn 0 (show (consts (Consts L)).fn 0, from ⟨m, p⟩) = sum.inr (consts.c ⟨⟨m, le⟩, p⟩) :=
begin
  simp,
  induction n with n IH generalizing p m; simp[Lω_to_Ln_add_pConsts, ← coe_fn₂],
  { refl },
  { simp[IH p (nat.le_of_succ_le le), ← coe_fn₂],
    have : n < m, from nat.succ_le_iff.mp le,
    simp[pConsts_to_add_pConsts_of_lt L p this, ←coe_fn₂] }
end

lemma commutative (n : ℕ) : (Lω_to_Ln_add_pConsts L n).comp (Ln_to_Lω L n) = add_left :=
begin
  induction n with n IH,
  { ext; simp[Ln_to_Lω, Lω_to_Ln_add_pConsts, add_left_fn_to_coe, add_left_pr_to_coe] },
  { ext m,
    { rcases f; simp[Ln_to_Lω, limit, ←coe_fn₁, ←coe_fn₂],
      { have : (Lω_to_Ln_add_pConsts L n).fn m ((Ln_to_Lω L n).fn m f) = ↑f,
        { have := (language_translation.eq_iff.mp IH).1 m f, simpa using this },
        simp[this, add_left_fn_to_coe] },
      { rcases m,
        { simp[add_right_fn_to_coe],
          have := Lω_to_Ln_add_pConst_fn_of_le L f (by refl), simp at this,
          simp[this, ←coe_fn₂, ←coe_fn₁, add_left_fn_to_coe, pConsts_to_add_pConsts_of_eq L f,
            show (pConsts_to_add_pConsts L n).fn 0 (consts.c ⟨⟨n, show n ≤ n, by refl⟩, f⟩) = _, from pConsts_to_add_pConsts_of_eq L f] },
        { rcases f } } },
    { intros m r, rcases r; simp[Ln_to_Lω, limit, ←coe_pr₁, ←coe_pr₂], 
      { have : (Lω_to_Ln_add_pConsts L n).pr m ((Ln_to_Lω L n).pr m r) = ↑r,
        { have := (language_translation.eq_iff.mp IH).2 m r, simpa using this },
        simp[this, add_left_pr_to_coe] },
      { rcases r } } }
end

lemma add_left_Ln_to_Lω_commutative (n : ℕ) : (Ln_to_Lω L (n + 1)).comp (add_left : L[n] ↝ᴸ L[n+1]) = Ln_to_Lω L n :=
by ext; simp[Ln_to_Lω, add_left_fn_to_coe, add_left_pr_to_coe]

variables {L}

def Lω_seq_limit : seq_limit (Lang L) Lω :=
{ seq := λ n, add_left,
  to_limit := Ln_to_Lω L,
  commutes := add_left_Ln_to_Lω_commutative L,
  rank_fn := λ n f, by { rcases f, { exact 0 }, { rcases n, { rcases f with ⟨m, f⟩, exact (m + 1) }, { rcases f } } },
  rank_pr := λ n r, by { rcases r, { exact 0 }, { rcases r } },
  fn := λ n f, by { rcases f, { exact f }, { rcases n, { rcases f with ⟨m, f⟩, exact sum.inr (consts.c f) }, { rcases f } } },
  pr := λ n r, by { rcases r, { exact r }, { rcases r } },
  fn_spec := λ n f, by { rcases f, { refl }, { cases n, { rcases f with ⟨m, f⟩, refl }, { rcases f } } },
  pr_spec := λ n r, by { rcases r, { refl }, { rcases r } } }

def retruct (p : formula Lω) : formula L[Lω_seq_limit.rank_p p] := Lω_seq_limit.retruct_p p

def henkin_constant (p : formula (limit L)) : Consts L := ⟨Lω_seq_limit.rank_p p, retruct L p⟩

@[simp] lemma retruct_s_c (p : formula Lω) : (Ln_to_Lω L _).fun_p (retruct L p) = p := Lω_seq_limit.retruct_p_spec p 

@[simp] lemma retruct_s (p : formula Lω) : (Ln_to_Lω L _).fun_p (retruct L p) = p := Lω_seq_limit.retruct_p_spec p 

lemma Ln_to_Lω_fun_p_coe (n : ℕ) (p : formula L[n]) :
  (Ln_to_Lω L (n + 1)).fun_p (by simp[Lang]; refine p) = (Ln_to_Lω L n).fun_p p :=
by simp[←add_left_Ln_to_Lω_commutative L n, comp_fun_p]; refl

@[simp] lemma Ln_to_Lω_fun_t_coe {n} (p : formula L[n]) :
  (Ln_to_Lω L (n + 1)).fun_t (↑(↑p : term (consts (formula L[n]))) : term (extend L[n])) = ↑(⟨n, p⟩ : Consts L) :=
begin
  unfold_coes, simp[Ln_to_Lω],
  suffices : ((Ln_to_Lω L n).sum (add_right.comp (consts_of_fun (sigma.mk n)))).fn 0 (↑(consts.c p)) = ↑(consts.c (⟨n, p⟩ : Consts L)),
  { exact this },
  simp, refl
end

variables (T) {L}

@[reducible] def Thy : Π n : ℕ, theory (Lang L n)
| 0       := T
| (n + 1) := theory_extend (Thy n)

def Thy' (n : ℕ) := (Ln_to_Lω L n).fun_theory (Thy T n)

local notation `T[` n `]` := Thy' T n

def theory_limit : theory Lω := ⋃ n, T[n]

local notation `Tω` := theory_limit L T

lemma Thy'_ss (n : ℕ) : T[n] ⊆ T[n + 1] :=
begin
  simp[fun_theory, Thy', Thy],
  intros p mem, simp[Lang], refine ⟨by simp[Lang]; refine p, _⟩,
  simpa[mem] using Ln_to_Lω_fun_p_coe _ n p,
end

lemma Tn_consistent (consis : T.consistent) (n : ℕ) : theory.consistent T[n] :=
begin
  have : theory.consistent (Thy T n),
  { induction n with n IH, { exact consis }, { exact theory_extend_consistent IH } },
  have consis' : theory.consistent (add_left.fun_theory (Thy T n) : theory (L[n] + consts (pConsts L n))), from add_consts.consistent_iff.mpr this,
  have : (add_left.fun_theory (Thy T n) : theory (L[n] + consts (pConsts L n))) = (Lω_to_Ln_add_pConsts L n).fun_theory T[n],
  { rw[fun_theory, ←commutative, comp_fun_p, set.image_comp], simp[fun_theory, Thy'] },
  rw this at consis',
  exact language.language_translation.consistency _ _ consis'
end

theorem Tω_consistent (consis : T.consistent) : theory.consistent Tω :=
(theory.consistent.Union_seq (Thy' T) (Thy'_ss T)).mpr (Tn_consistent T consis)


lemma T_ss_Tω : ↑T ⊆ Tω :=
by simpa [show ↑T = T[0], by refl, theory_limit] using set.subset_Union (Thy' T) 0

lemma henkin_mem_Tω (p : formula Lω) : (∐ p) ⟶ rew ı[0 ⇝ henkin_constant p] p ∈ Tω :=
begin
  simp[henkin_constant],
  let r := Lω_seq_limit.rank_p p,
  suffices : (∐ p) ⟶ rew ı[0 ⇝ henkin_constant p] p ∈ T[r + 1],
  { simp[theory_limit], refine ⟨_, this⟩ },
  have lmm₁ : (∐ p) ⟶ rew ı[0 ⇝ henkin_constant p] p = (Ln_to_Lω L (r + 1)).fun_p (henkin_axiom (retruct L p)),
  { have := Ln_to_Lω_fun_p_coe L r (retruct L p), simp at this, simp[this, henkin_axiom, henkin_constant] },
  have lmm₂ : (Ln_to_Lω L (r + 1)).fun_p (henkin_axiom (retruct L p)) ∈ T[r + 1],
  { simp[Thy'], refine ⟨henkin_axiom (retruct L p), by simp[Thy], rfl⟩ },
  rw lmm₁, exact lmm₂
end

local notation `Tω⁺` := consistent.maximal Tω

local notation `Lω` := limit _

open axiomatic_classical_logic axiomatic_classical_logic' provable

def Consts.of (t : term Lω) : Consts L := henkin_constant ((t^1) ≃∘ #0)
#check Consts.of

def Consts.fn {n} (f : (limit L).fn n) (v : finitary (Consts L) n) : Consts L := Consts.of (app f (λ i, (v i)))

def Consts.pr {n} (r : (limit L).pr n) (v : finitary (Consts L) n) : Prop := formula.app r (λ i, (v i)) ∈ Tω⁺

def Consts.equal (p q : Consts L) : Prop := (p ≃∘ q) ∈ Tω⁺

local notation p ` ~[`:50 T :50 `] `:0 q:50 := Consts.equal T p q

variables [cT : Consistent T] {L}
include cT

lemma Tω_consistent' : consistent (theory_limit L T) := Tω_consistent T cT.consis

lemma mem_Tω'_of_Tω_provable {p : formula Lω} (b : Tω ⊢ p): p ∈ Tω⁺ :=
begin
  have : Tω⁺ ⊢ p, from weakening' (Tω_consistent' T).ss_maximal b,
  exact (Tω_consistent' T).mem_maximal_iff.mpr this
end

@[simp, refl] lemma Consts.equal_refl (c : Consts L) : c ~[T] c := by simp[Consts.equal, (Tω_consistent' T).mem_maximal_iff]

theorem Consts.equal_equivalence : equivalence (Consts.equal T) :=
⟨λ p, by simp[Consts.equal, (Tω_consistent' T).mem_maximal_iff],
  λ p q, by { simp[Consts.equal, (Tω_consistent' T).mem_maximal_iff], exact provable.eq_symm },
  λ p q r, by { simp[Consts.equal, (Tω_consistent' T).mem_maximal_iff], exact provable.eq_trans }⟩

lemma Consts.of_eq (t : term Lω) :
 t ≃∘ Consts.of t ∈ Tω⁺ :=
begin
  have : ∐ (t^1 ≃∘ #0) ⟶ (t ≃∘ Consts.of t) ∈ Tω, by simpa[Consts.fn] using henkin_mem_Tω L T (t^1 ≃ #0),
  have lmm₁ : Tω ⊢ ∐ (t^1 ≃∘ #0) ⟶ (t ≃∘ Consts.of t), from by_axiom this,
  have lmm₂ : Tω ⊢ ∐ (t^1 ≃∘ #0), from provable.use t (by simp),
  have : Tω ⊢ t ≃∘ Consts.of t, from lmm₁ ⨀ lmm₂,
  exact mem_Tω'_of_Tω_provable T this
end

lemma Consts.fn_eq {n} (f : (limit L).fn n) (v : finitary (Consts L) n) :
 (app f (λ i, (v i)) ≃∘ Consts.fn f v) ∈ Tω⁺ :=
Consts.of_eq _ _

@[reducible, simp, instance]
def henkin : setoid (Consts L) := ⟨Consts.equal T, Consts.equal_equivalence T⟩

def Henkin : Type u := quotient (henkin T)

namespace Henkin
variables {T}

@[elab_as_eliminator]
protected lemma ind_on {C : Henkin T → Prop} (d : Henkin T)
  (h : ∀ p : Consts L, C ⟦p⟧) : C d :=
quotient.induction_on' d h

@[elab_as_eliminator, reducible]
def lift_on {φ} (d : Henkin T) (f : Consts L → φ)
  (h : ∀ p q : Consts L, p ~[T] q → f p = f q) : φ :=
quotient.lift_on' d f h

@[simp]
lemma lift_on_eq {φ} (p : Consts L) (f : Consts L → φ)
  (h : ∀ p q : Consts L, p ~[T] q → f p = f q) : lift_on ⟦p⟧ f h = f p := rfl

@[elab_as_eliminator, reducible, simp]
def lift_on₂ {φ} (d₁ d₂ : Henkin T) (f : Consts L → Consts L → φ)
  (h : ∀ p₁ p₂ q₁ q₂, p₁ ~[T] q₁ → p₂ ~[T] q₂ → f p₁ p₂ = f q₁ q₂) : φ :=
quotient.lift_on₂' d₁ d₂ f h

@[simp] lemma lift_on₂_eq {φ} (p q : Consts L) (f : Consts L → Consts L → φ)
  (h : ∀ p₁ p₂ q₁ q₂, p₁ ~[T] q₁ → p₂ ~[T] q₂ → f p₁ p₂ = f q₁ q₂) :
lift_on₂ ⟦p⟧ ⟦q⟧ f h = f p q := rfl

def lift_on_finitary {φ} {n : ℕ} (v : finitary (Henkin T) n) (f : finitary (Consts L) n → φ)
  (h : ∀ v₁ v₂ : finitary (Consts L) n, (∀ n, (v₁ n) ~[T] (v₂ n)) → f v₁ = f v₂) : φ :=
quotient.lift_on_finitary v f h 

@[simp] lemma lift_on_finitary_eq {φ} {n} (v : finitary (Consts L) n) (f : finitary (Consts L) n → φ)
  (h : ∀ v₁ v₂ : finitary (Consts L) n, (∀ n, (v₁ n) ~[T] (v₂ n)) → f v₁ = f v₂) :
  lift_on_finitary (λ x, ⟦v x⟧) f h = f v :=
quotient.lift_on_finitary_eq v f h

@[simp] lemma of_eq_of {p q : Consts L} : (⟦p⟧ : Henkin T) = ⟦q⟧ ↔ p ~[T] q := quotient.eq'

def fn {n} (f : (Lω).fn n) : finitary (Henkin T) n → Henkin T :=
λ v, lift_on_finitary v (λ v, (⟦Consts.fn f v⟧ : Henkin T)) $ λ v₁ v₂ eqs,
begin
  simp[of_eq_of, Consts.equal, (Tω_consistent' T).mem_maximal_iff],
  show      Tω⁺ ⊢ Consts.fn f v₁ ≃∘ Consts.fn f v₂,
  have b₁ : Tω⁺ ⊢ app f (λ i, (v₁ i)) ≃∘ Consts.fn f v₁, from (Tω_consistent' T).mem_maximal_iff.mp (Consts.fn_eq T f v₁),
  have b₂ : Tω⁺ ⊢ app f (λ i, (v₂ i)) ≃∘ Consts.fn f v₂, from (Tω_consistent' T).mem_maximal_iff.mp (Consts.fn_eq T f v₂),
  have b  : Tω⁺ ⊢ app f (λ i, (v₁ i)) ≃∘ app f (λ i, (v₂ i)),
  { have : ∀ i, Tω⁺ ⊢ v₁ i ≃∘ v₂ i, from λ i, (Tω_consistent' T).mem_maximal_iff.mp (eqs i),
    have : Tω⁺ ⊢ ⋀ i, v₁ i ≃∘ v₂ i, refine conjunction_iff.mpr this,
    exact function_ext' f (λ i, (v₁ i)) (λ i, (v₂ i)) ⨀ this },
  exact eq_trans (eq_trans b₁.eq_symm b) b₂
end

@[simp] lemma fn_app {n} (f : (Lω).fn n) (v : finitary (Consts L) n) :
  fn f (λ i, ⟦v i⟧) = ⟦Consts.fn f v⟧ :=
lift_on_finitary_eq _ _ _

def pr {n} (r : (Lω).pr n) : finitary (Henkin T) n → Prop :=
λ v, lift_on_finitary v (Consts.pr T r) $ λ v₁ v₂ eqs,
begin
  simp[of_eq_of, Consts.pr, (Tω_consistent' T).mem_maximal_iff],
  suffices : Tω⁺ ⊢ app r (λ i, (v₁ i)) ⟷ app r (λ i, (v₂ i)),
  { split; intros h, { exact (iff_equiv.mp this).1 ⨀ h }, { exact (iff_equiv.mp this).2 ⨀ h } },
  have : ∀ i, Tω⁺ ⊢ v₁ i ≃∘ v₂ i, from λ i, (Tω_consistent' T).mem_maximal_iff.mp (eqs i),
  have : Tω⁺ ⊢ ⋀ i, v₁ i ≃∘ v₂ i, refine conjunction_iff.mpr this,
  exact predicate_ext'' r (λ i, (v₁ i)) (λ i, (v₂ i)) ⨀ this
end

@[simp] lemma pr_app {n} (r : (Lω).pr n) (v : finitary (Consts L) n) :
  pr r (λ i, ⟦v i⟧) ↔ formula.app r (λ i, (v i)) ∈ Tω⁺ :=
by { have : pr r (λ i, ⟦v i⟧) = Consts.pr T r v, from lift_on_finitary_eq _ _ _, simp[this, Consts.pr] }

variables (T)

def henkin_model : model Lω := ⟨Henkin T, ⟨⟦henkin_constant ⊤⟧⟩, λ n f, fn f, λ n r, pr r⟩

local notation `ℌ` := henkin_model T


@[simp] lemma henkin_model_fn {n} (f : (Lω).fn n) (v) : (ℌ).fn f v = fn f v := rfl
@[simp] lemma henkin_model_pr {n} (r : (Lω).pr n) (v) : (ℌ).pr r v = pr r v := rfl

lemma eq_Consts_of_eq {t u} : Consts.of t ~[T] Consts.of u ↔ Tω⁺ ⊢ t ≃∘ u  :=
begin
  simp[Consts.equal, (Tω_consistent' T).mem_maximal_iff],
  have lmm₁ : Tω⁺ ⊢ t ≃∘ Consts.of t, from by_axiom (Consts.of_eq T _), 
  have lmm₂ : Tω⁺ ⊢ u ≃∘ Consts.of u, from by_axiom (Consts.of_eq T _), 
  refine ⟨λ h, eq_trans (eq_trans lmm₁ h) (eq_symm lmm₂), λ h, eq_trans (eq_trans (eq_symm lmm₁) h) lmm₂⟩
end

lemma term_val_eq_quotient (t : term Lω) (e : ℕ → Consts L) :
  @term.val _ ℌ (λ n, ⟦e n⟧ : ℕ → |ℌ|) t = ⟦Consts.of (t.rew (λ x, ↑(e x)))⟧ :=
begin
  induction t,
  case var : x { simp[Consts.equal], exact Consts.of_eq T _ },
  case app : n f v IH
  { simp,
    have : (λ i, @term.val _ ℌ (λ n, ⟦e n⟧) (v i)) = (λ i, ⟦Consts.of ((v i).rew (λ x, ↑(e x)))⟧),
    { funext i, exact IH i },
    simp[this, Consts.fn],
    have : Tω⁺ ⊢ app f (λ i, (Consts.of ((v i).rew (λ x, (e x))))) ≃∘ app f (λ i, (v i).rew (λ x, (e x))),
    { have : ∀ i, Tω⁺ ⊢ Consts.of ((v i).rew (λ x, (e x))) ≃∘ (v i).rew (λ x, (e x)),
        from λ i, eq_symm (by_axiom (Consts.of_eq T ((v i).rew (λ x, (e x))))),
      have : Tω⁺ ⊢ ⋀ i, Consts.of ((v i).rew (λ x, (e x))) ≃∘ (v i).rew (λ x, (e x)),
        from conjunction_iff.mpr this,
      exact function_ext' f _ _ ⨀ this },
    refine (eq_Consts_of_eq _).mpr this }
end

private lemma ℌ_models_Tω'_fal
  {p : formula Lω} 
  (IH : ∀ (s : ℕ → Consts L), p.rew (λ x, ↑(s x)) ∈ Tω⁺ ↔ @formula.val _ ℌ (λ x, ⟦s x⟧) p)
  (s : ℕ → Consts L) :
  (∏ p).rew (λ x, ↑(s x)) ∈ Tω⁺ ↔ ℌ ⊧[λ x, ⟦s x⟧] (∏ p) :=
begin
  simp, split,
    { intros h,  intros c,
      induction c using fopl.henkin.Henkin.ind_on,
      let s' : ℕ → Consts L := c ⌢ s,
      have : p.rew (λ x, (s' x)) ∈ Tω⁺,
      { simp[(Tω_consistent' T).mem_maximal_iff] at h ⊢,
        have : Tω⁺ ⊢ p.rew (c ⌢ λ x, (s x)),  simpa[formula.nested_rew] using h ⊚ c,
        simpa using this },
      simpa[s', app_concat c s] using (IH s').1 this },
    { intros h,
      have h : ∀ (c : Consts L), @formula.val _ ℌ (λ x, ⟦(c ⌢ s) x⟧) p, { intros c, simp, exact h ⟦c⟧ },
      by_contradiction A,
      let φ := ⁻p.rew ((λ x, (s x))^1),
      have lmm₁ : Tω⁺ ⊢  p.rew (henkin_constant φ ⌢ (λ x, (s x))),
        by simpa using by_axiom ((IH _).mpr (h $ henkin_constant φ)),         
      have : Tω⁺ ⊢ ⁻∏ p.rew ((λ x, (s x))^1), from by_axiom ((Tω_consistent' T).neg_mem_maximal_iff.mpr A),      
      have : Tω⁺ ⊢ ∐ φ, from (iff_of_equiv (provable.neg_fal_equiv_ex_neg _)).mp this,
      have lmm₂ : Tω⁺ ⊢ ⁻p.rew (henkin_constant φ ⌢ (λ x, (s x))),
        by simpa[φ, formula.nested_rew] using by_axiom ((Tω_consistent' T).ss_maximal (henkin_mem_Tω L T φ)) ⨀ this,
      exact (Tω_consistent' T).maximal_consistent ⟨_, lmm₁, lmm₂⟩ }
end

theorem ℌ_models_Tω' (p : formula Lω) (s : ℕ → Consts L) :
  p.rew (λ x, ↑(s x)) ∈ Tω⁺ ↔ ℌ ⊧[λ x, ⟦s x⟧] p :=
begin
  induction p generalizing s,
  case app : n r v
  { simp[term_val_eq_quotient, (Tω_consistent' T).mem_maximal_iff],
    suffices :  Tω⁺ ⊢ app r (λ i, (v i).rew (λ x, (s x))) ⟷ app r (λ i, Consts.of ((v i).rew (λ x, (s x)))), from iff_of_equiv this,
    have : ∀ i, Tω⁺ ⊢ (v i).rew (λ x, (s x)) ≃∘ Consts.of ((v i).rew (λ x, (s x))),
      from λ i, (by_axiom (Consts.of_eq T ((v i).rew (λ x, (s x))))),
    have :      Tω⁺ ⊢ ⋀ i, (v i).rew (λ x, (s x)) ≃∘ Consts.of ((v i).rew (λ x, (s x))),
      from conjunction_iff.mpr this,
    exact predicate_ext'' r _ _ ⨀ this },
  case equal : t u { simp[term_val_eq_quotient, (Tω_consistent' T).mem_maximal_iff], exact iff.symm (eq_Consts_of_eq _) },
  case imply : p q IH_p IH_q { simp[(Tω_consistent' T).imply_mem_maximal_iff] at*, simp[IH_p s, IH_q s] },
  case verum { simp[(Tω_consistent' T).mem_maximal_iff] },
  case neg : p IH { simp[(Tω_consistent' T).neg_mem_maximal_iff], exact iff.not (IH s) },
  case fal : p IH { exact ℌ_models_Tω'_fal T IH s }
end

theorem ℌ_models_Tω'_of_sentence {p : formula Lω} (hp : is_sentence p) :
  p ∈ Tω⁺ ↔ ℌ ⊧ p :=
by simpa[hp, eval_is_sentence_iff] using ℌ_models_Tω' T p default

variables [closed_theory T]

theorem ℌ_models_T : add_left.of_ltr ℌ ⊧ₜₕ T :=
begin
  simp[theory_models_iff], intros p mem,
  have : p ∈ Tω⁺, from (Tω_consistent' T).ss_maximal (T_ss_Tω T mem),  
  exact (ℌ_models_Tω'_of_sentence T (show is_sentence p, from closed_theory.cl mem)).mp this
end 

end Henkin

end henkin

variables [closed_theory T] {L} {T}

theorem consistent_iff_satisfiable : T.consistent ↔ ∃ M, M ⊧ₜₕ T :=
⟨λ consis,  ⟨_, @henkin.Henkin.ℌ_models_T _ T ⟨consis⟩ _⟩, by { rintros ⟨M, hM⟩, exact model_consistent hM}⟩

theorem completeness {p : formula L} (hp : is_sentence p) : 
  T ⊢ p ↔ (∀ M, M ⊧ₜₕ T → M ⊧ p) :=
⟨λ b M, soundness b,
 λ h, by { simp[theory.provable_iff_inconsistent], intros consis,
  have : closed_theory (T +{⁻p}), from ⟨by { simp[hp], exact λ _, closed_theory.cl }⟩,
  have : ∃ M, M ⊧ₜₕ (T +{⁻p}), exactI consistent_iff_satisfiable.mp consis,
  rcases this with ⟨M, hM⟩,
  have : M ⊧ p, from h M (λ p mem, hM p (by simp[mem])),
  have : ¬M ⊧ p, by simpa[models_neg_iff_of_is_sentence hp] using hM (⁻p) (by simp),
  contradiction }⟩

theorem completeness' {p : formula L} : 
  T ⊢ p ↔ (∀ M, M ⊧ₜₕ T → M ⊧ p) :=
⟨λ b M, soundness b,
 λ h, by { have : ∀ M, M ⊧ₜₕ T → M ⊧ ∏* p, { intros M hM, simp[fal_complete, nfal_models_iff, h M hM] },
  have : T ⊢ ∏* p, from (completeness (show is_sentence (∏* p), by simp)).mpr this,
  have lmm : T ⊢ p.rew (λ x, ite (x < p.arity) #x #(x - p.arity)), from provable.nfal_subst _ _ ı ⨀ this,
  have := @formula.rew_rew _ p (λ x, ite (x < p.arity) #x #(x - p.arity)) ı (λ m lt, by simp[lt]),
  simpa[this] using lmm }⟩

variables {L₁ L₂ : language.{u}} {T₁ : theory L₁} [closed_theory T₁]

theorem coe_consistent_iff :
  (↑T₁ : theory (L₁ + L₂)).consistent ↔ T₁.consistent :=
⟨language.language_translation.consistency _ T₁,
 λ h,
begin
  have : ∃ M₁, M₁ ⊧ₜₕ T₁, from consistent_iff_satisfiable.mp h,
  rcases this with ⟨M₁, hM₁⟩,
  let M₂ : model (L₁ + L₂) := M₁.extend default default,
  have : M₁.extend default default ⊧ₜₕ (↑T₁ : theory (L₁ + L₂)), from (M₁.extend_modelsth_coe_iff default default).mpr hM₁,
  exact consistent_iff_satisfiable.mpr ⟨_, this⟩
end⟩

theorem coe_provable_iff {p : formula L₁} (hp : is_sentence p) :
  (↑T₁ : theory (L₁ + L₂)) ⊢ ↑p ↔ T₁ ⊢ p :=
begin
  simp[theory.provable_iff_inconsistent],
  suffices : ¬theory.consistent (↑(T₁ +{ ⁻p } : theory L₁) : theory (L₁ + L₂)) ↔ ¬theory.consistent (T₁ +{ ⁻p }),
    by simpa[language.language_translation_coe.fun_theory_insert] using this, 
  have : closed_theory (T₁ +{ ⁻p }) := ⟨by { simp[hp], exact λ _, closed_theory.cl }⟩,
  have : theory.consistent (↑(T₁ +{ ⁻p } : theory L₁) : theory (L₁ + L₂)) ↔ theory.consistent (T₁ +{ ⁻p }),
    from @coe_consistent_iff _ _ ((T₁ +{ ⁻p } : theory L₁)) this,
  simp[this]
end

variables {L₁ L₂} (D : L₁.definitions L₂)

theorem extensions_by_definitions_consistent (consis : T₁.consistent)
  (b : ∀ {n} (f : L₂.fn n), T₁ ⊢ ∏[n] ∐ (D.df_fn f)) :
  theory.consistent (↑T₁ ∪ D.thy) :=
begin
  suffices : ∃ M, M ⊧ₜₕ (↑T₁ ∪ D.thy),
  { exactI consistent_iff_satisfiable.mpr this },  
  have : ∃ M, M ⊧ₜₕ T₁, from consistent_iff_satisfiable.mp consis,
  rcases this with ⟨M, hM⟩,
  have : ∀ (n) (f : L₂.fn n) (v : finitary (|M|) n), ∃ (d : (|M|)),
    (D.df_fn f).val M (d ⌢ (λ i, if h : i < n then v ⟨i, h⟩ else default)),
  { intros n f,
    have : M ⊧[default] ∏[n] ∐ (D.df_fn f), from (soundness (b f) hM) default,
    simpa[models_univs] using this },
  have : ∀ n : ℕ, ∃ F' : L₂.fn n → finitary (|M|) n → |M|,
    ∀ (f : L₂.fn n) (v : finitary (|M|) n), (D.df_fn f).val M (F' f v ⌢ (λ i, if h : i < n then v ⟨i, h⟩ else default)),
  { intros n, choose F' hF' using this n, exact ⟨F', hF'⟩ },
  choose F hF using this,
  let R : Π n, L₂.pr n → finitary (|M|) n → Prop := λ n r v, M ⊧[λ i, if h : i < n then v ⟨i, h⟩ else default] (D.df_pr r),
  let M₂ : model (L₁ + L₂) := M.extend F R,
  have lmm₁ : ∀ {n} (f : L₂.fn n), M₂ ⊧ def_fn f (D.df_fn f),
  { intros n f,
    rw [←eval_is_sentence_iff default (show is_sentence (def_fn f (D.df_fn f)), by simp[D.hdf_fn])],
    simp[def_fn, models_univs], intros v,
    exact (model.extend_val_coe_iff M _ _).mpr (hF n f v) },
  have lmm₂ : ∀ {n} (r : L₂.pr n), M₂ ⊧ def_pr r (D.df_pr r),
  { intros n r,
    rw [←eval_is_sentence_iff default (show is_sentence (def_pr r (D.df_pr r)), by simp[D.hdf_pr])],
    simp[def_pr, models_univs, R], intros v,
    exact iff.symm (model.extend_val_coe_iff M F R), exact ⟨λ _, default⟩ },
  have lmm₃ : M₂ ⊧ₜₕ ↑T₁, from (model.extend_modelsth_coe_iff M _ _).mpr hM, 
  refine ⟨M₂, by { simp[lmm₃, definitions_def], split; intros n; simp[modelsth, lmm₁, lmm₂] }⟩
end

variables (T₁)

theorem extensions_by_definitions_consistent_iff
  (b : ∀ {n} (f : L₂.fn n), T₁ ⊢ ∏[n] ∐ (D.df_fn f)) :
  theory.consistent (↑T₁ ∪ D.thy) ↔ T₁.consistent :=
⟨λ h, begin
  have : (↑T₁ : theory (L₁ + L₂)).consistent, from theory.consistent_of_consistent_ss h (by simp),
  exact coe_consistent_iff.mp this
end, λ h,  extensions_by_definitions_consistent D h @b⟩

theorem extensions_by_definitions_conservative
  (b : ∀ {n} (f : L₂.fn n), T₁ ⊢ ∏[n] ∐ (D.df_fn f))
  (p : formula L₁) (hp : p.is_sentence) :
  ↑T₁ ∪ D.thy ⊢ p ↔ T₁ ⊢ p :=
begin
  simp[theory.provable_iff_inconsistent],
  suffices : ¬theory.consistent (↑(T₁+{ ⁻p }) ∪ D.thy) ↔ ¬theory.consistent (T₁+{ ⁻p }),
  { have eq : ((↑T₁ ∪ D.thy) +{ ⁻↑p }) = (↑(T₁+{ ⁻p }) ∪ D.thy),
    { ext q, simp[language.language_translation_coe.fun_theory_insert, or_assoc] },
    simpa[eq] using this },
  have : closed_theory (T₁ +{ ⁻p }) := ⟨by { simp[hp], exact λ _, closed_theory.cl }⟩,
  exact iff.not (by exactI extensions_by_definitions_consistent_iff (T₁+{ ⁻p }) D (λ n f, by simp[b f]))
end

theorem extensions_by_definitions_conservative'
  (b : ∀ {n} (f : L₂.fn n), T₁ ⊢ ∏[n] ∐ (D.df_fn f))
  (p : formula L₁) :
  ↑T₁ ∪ D.thy ⊢ p ↔ T₁ ⊢ p :=
by { have := extensions_by_definitions_conservative T₁ D @b (∏* p) (by simp),
     simpa[←provable.iff_fal_complete] using this }

theorem extensions_by_definitions_consistent_iff_of_predicate [language.predicate L₂] :
  theory.consistent (↑T₁ ∪ D.thy) ↔ T₁.consistent :=
extensions_by_definitions_consistent_iff T₁ D (λ n f, by { exfalso, exact is_empty.false f })

end fopl