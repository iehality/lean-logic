import FOL.deduction

universes u v
open_locale logic_symbol

namespace fol
open logic formula

structure Structure (L : language.{u}) :=
(dom : Type u)
(inhabited : inhabited dom)
(fn : ∀ {n}, L.fn n → (fin n → dom) → dom)
(pr : ∀ {n}, L.pr n → (fin n → dom) → Prop)

local notation (name := dom) `|`M`|` := Structure.dom M

variables {L : language.{u}} {M : Structure L}

instance (M : Structure L) : inhabited M.dom := M.inhabited

variables (M)

@[simp] def term.val (e : ℕ → |M|) : term L → |M|
| (#x)           := e x
| (term.app f v) := M.fn f (λ i, (v i).val)

@[simp] def formula.val : ∀ (e : ℕ → |M|), formula L → Prop
| _ ⊤                 := true
| e (formula.app p v) := M.pr p (λ i, (v i).val M e)
| e (t =' u)          := t.val M e = u.val M e
| e (p ⟶ q)          := p.val e → q.val e
| e (∼p)              := ¬(p.val e)
| e (∀.p)            := ∀ d : M.dom, (p.val (d ⌢ e))

notation M` ⊧[`:80 e`] `p :50 := @formula.val _ M e p

def models (M : Structure L) (p : formula L) : Prop := ∀ (e : ℕ → |M|), M ⊧[e] p

instance : semantics (formula L) (Structure L) := ⟨models⟩

lemma models_def {M : Structure L} {p : formula L} : M ⊧ p ↔ (∀ (e : ℕ → |M|), M ⊧[e] p) := by refl

abbreviation satisfiable (p : formula L) : Prop := semantics.satisfiable (Structure L) p

abbreviation Satisfiable (T : Theory L) : Prop := semantics.Satisfiable (Structure L) T

instance : has_double_turnstile (Theory L) (formula L) := ⟨semantics.consequence (Structure L)⟩

lemma consequence_def {T : Theory L} {p : formula L} :
  T ⊧ p ↔ ∀ S : Structure L, S ⊧ T → S ⊧ p := by refl

variables {M}

lemma rew_val_eq (s : ℕ → term L) (e : ℕ → |M|) : ∀ (t : term L),
  (t.rew s).val M e = t.val M (λ n, (s n).val M e)
| (#x)                := by simp
| (@term.app _ n f v) := by simp[λ i : fin n, rew_val_eq (v i)]

@[simp] lemma pow_val_concat (e : ℕ → |M|) (d : |M|) (t : term L) : (t^1).val M (d ⌢ e) = t.val M e :=
by simp[term.pow_eq, rew_val_eq]

lemma rew_val_iff : ∀ (s : ℕ → term L) (p : formula L) (e : ℕ → |M|),
  (p.rew s).val M e ↔ p.val M (λ n, (s n).val M e)
| _ ⊤                 _ := by simp
| _ (formula.app p v) _ := by simp[formula.rew, rew_val_eq]
| _ (t =' u)          _ := by simp[formula.rew, term.val, rew_val_eq]
| _ (p ⟶ q)           _ := by simp[formula.rew, rew_val_iff _ p, rew_val_iff _ q]
| _ (∼p)              _ := by simp[formula.rew, rew_val_iff _ p]
| s (∀.p)            e :=
  by { simp[formula.rew, rew_val_iff _ p], refine forall_congr (λ d, _),
       have : (λ n, ((s ^ 1) n).val M (d ⌢ e) ) = (d ⌢ λ n, ((s n).val M e)),
       { funext n, cases n; simp[concat, term.val, term.val], exact pow_val_concat _ _ _ },
       simp[this] }

@[simp] lemma pow_val_concat_iff : ∀ (p : formula L) (e : ℕ → |M|) d, (p^1).val M (d ⌢ e) = p.val M e :=
by simp[formula.pow_eq, rew_val_iff]

@[simp] lemma Structure_zero_val [has_zero_symbol L] {e : ℕ → |M|} : (0 : term L).val M e = M.fn has_zero_symbol.zero finitary.nil :=
by simp[has_zero.zero]; congr

@[simp] lemma Structure_succ_val [has_succ_symbol L] (t : term L) {e : ℕ → |M|} :
  (Succ t).val M e = M.fn has_succ_symbol.succ ‹t.val M e› :=
by simp[has_succ.succ]; congr; ext; simp

private lemma modelsth_sf {T : Theory L} : M ⊧ T → M ⊧ ⤊T := λ h p hyp_p e,
by { rcases hyp_p with ⟨p, hyp_p', rfl⟩, simp[formula.pow_eq, rew_val_iff],
     refine h hyp_p' _ }

@[simp] lemma models_ex {p : formula L} {e : ℕ → |M|} : (∃.p).val M e ↔ ∃ d, p.val M (d ⌢ e) :=
by simp[has_exists_quantifier.ex, formula.ex, models, rew_val_iff]

lemma models_univs {p : formula L} {e : ℕ → |M|} {n} :
  (∀.[n] p).val M e ↔ ∀ d : finitary (|M|) n, p.val M (λ i, if h : i < n then d ⟨i, h⟩ else e (i - n)) :=
begin
  induction n with n IH generalizing e; simp,
  { refine ⟨λ h _, h, λ h, h ∅⟩ },
  { simp[IH], split,
    { intros h D, refine cast _ (h D.head_inv D.tail_inv), congr, funext i, simp[concat, slide],
      have C : i < n ∨ i = n ∨ n < i, exact trichotomous i n,
      cases C,
      { simp[C, nat.lt.step C, finitary.tail_inv] }, rcases C with (rfl | C),
      { simp[←nat.add_one], refl },
      { simp[show ¬i < n, from asymm C, show ¬i < n.succ, by omega, C, ←nat.add_one,
             show i - n - 1 = i - (n + 1), from tsub_tsub i n 1] } },
    { intros h d D, refine cast _ (h (D ᶠ:: d)), congr, funext i, simp[concat, slide],
      have C : i < n ∨ i = n ∨ n < i, exact trichotomous i n,
      cases C,
      { simp[C, nat.lt.step C, finitary.cons_inv] }, rcases C with (rfl | C), 
      { simp[←nat.add_one] },
      { simp[show ¬i < n, from asymm C, show ¬i < n.succ, by omega, C, ←nat.add_one,
             show i - n - 1 = i - (n + 1), from tsub_tsub i n 1] } } }
end

@[simp] lemma models_and {p q : formula L} {e : ℕ → |M|} : (p ⊓ q).val M e ↔ (p.val M e ∧ q.val M e) :=
by simp[has_inf.inf, formula.and]

@[simp] lemma models_or {p q : formula L} {e : ℕ → |M|} : (p ⊔ q).val M e ↔ (p.val M e ∨ q.val M e) :=
by {simp[has_sup.sup, formula.or], exact or_iff_not_imp_left.symm }

@[simp] lemma models_iff {p q : formula L} {e : ℕ → |M|} : (p ⟷ q).val M e ↔ (p.val M e ↔ q.val M e) :=
by simp[lrarrow_def]; exact iff_def.symm

@[simp] lemma models_conjunction' {n : ℕ} {P : finitary (formula L) n} {e : ℕ → |M|} :
  (finitary.conjunction n P).val M e ↔ ∀ i, (P i).val M e :=
by { induction n with n IH; simp,
     { simp [IH], split,
       { rintros ⟨h0, h1⟩, intros i,
         have : i.val < n ∨ i.val = n := nat.lt_succ_iff_lt_or_eq.mp i.property,
         cases this,
         { have := h1 ⟨↑i, this⟩, simp at this, refine this },
         { simp[←this] at*, refine h0 } },
       { intros h, refine ⟨h _, λ _, h _⟩ } } }

@[simp] lemma models_pow {p : formula L} {i : ℕ} {e : ℕ → |M| } : (p^i).val M e ↔ p.val M (λ n, e (n + i)) :=
by simp[formula.pow_eq, rew_val_iff]

lemma models_subst {p : formula L} {i : ℕ} {t : term L} {e : ℕ → |M| } :
  (p.rew ı[i ⇝ t]).val M e ↔ p.val M (λ n, if n < i then e n else if i < n then e (n - 1) else t.val M e) :=
by { simp[rew_val_iff],
     have : (λ (n : ℕ), term.val M e (ı[i ⇝ t] n)) = (λ n, if n < i then e n else if i < n then e (n - 1) else t.val M e),
     { funext n,
       have C : n < i ∨ n = i ∨ i < n, exact trichotomous n i,
       cases C, simp[C],
       cases C; simp[C], simp[asymm C] },
     simp[this] }

@[simp] lemma models_subst_0 {p : formula L} {t : term L} {e : ℕ → |M|} :
  (p.rew ı[0 ⇝ t]).val M e ↔ p.val M (t.val M e ⌢ e) :=
by { have := @models_subst _ _ p 0 t e, simp at this,
     have eqn : (λ n, ite (0 < n) (e (n - 1)) (t.val M e)) = t.val M e ⌢ e,
     { funext n, cases n; simp }, rw[←eqn], exact this }

@[simp] lemma models_subst_1 {p : formula L} {t : term L} {e : ℕ → |M| } :
  (p.rew ı[1 ⇝ t]).val M e ↔ p.val M (e 0 ⌢ t.val M e ⌢ (λ x, e (x + 1))) :=
by { have := @models_subst _ _ p 1 t e,
     have eqn : (λ n, ite (n < 1) (e n) (ite (1 < n) (e (n - 1)) (t.val M e))) =
       e 0 ⌢ t.val M e ⌢ (λ x, e (x + 1)),
     { funext n, cases n; simp[←nat.add_one], cases n; simp }, rw[←eqn], exact this }

lemma nfal_models_iff : ∀ {n} {p : formula L}, M ⊧ nfal p n ↔ M ⊧ p
| 0     _ := iff.rfl
| (n+1) p := by { simp[←@nfal_models_iff n p], refine ⟨λ h e, _, λ h e d, h _⟩,
  have : ((e 0) ⌢ λ x, e (x + 1) )= e, { ext x, cases x; simp[concat] },
  have := h (λ x, e (x + 1)) (e 0), simp* at* }

theorem soundness {T : Theory L} : ∀ {p}, T ⊢ p → T ⊧ p := λ p hyp,
begin
  rcases hyp,
  induction hyp,
  case generalize : T p hyp_p IH
  { intros M hyp_T e d, exact IH (modelsth_sf hyp_T) _ },
  case mdp : T p q hyp_pq hyp_p IH_pq IH_p
  { intros M hyp_T e, exact IH_pq hyp_T e (IH_p hyp_T e) },
  case by_axiom : T p hyp_p
  { intros M hyp_T e, exact hyp_T hyp_p _ },
  case verum : T
  { intros M hyp_T e, simp },
  case imply₁ : T p q
  { intros M hyp_T e h₁ h₂, exact h₁ },
  case imply₂ : T p q r
  { intros M hyp_T e h₁ h₂ h₃, exact (h₁ h₃) (h₂ h₃) },
  case contraposition : T p q
  { intros M hyp_T e h₁, simp[formula.val], contrapose, exact h₁ },
  case specialize : T p t
  { intros M hyp_T e h, simp[rew_val_iff] at h ⊢,
    have : (λ n, (ı[0 ⇝ t] n).val M e) = (t.val M e) ⌢ e,
    { funext n, cases n; simp[term.val, term.val, concat] },
    rw this, exact h _ },
  case univ_K : T p q
  { intros M hyp_T e h₁ h₂ d, exact (h₁ d) (h₂ d) },
  case dummy_univ : T p
  { intros M hyp_T e h d, simp, exact h },
  case eq_reflexivity : T
  { intros M hyp_T e t, simp[formula.val] },
  case eq_symmetry : T
  { intros M hyp_T e t₁ t₂, simp[formula.val], refine eq.symm },
  case eq_transitivity : T
  { intros M hyp_T e t₁ t₂ t₃, simp[formula.val], refine eq.trans },
  case function_ext : T n f
  { intros M hyp_T, simp[eq_axiom4, nfal_models_iff], intros e, simp,
    intros h, simp[h] },
  case predicate_ext : T n f
  { intros M hyp_T, simp[eq_axiom5, nfal_models_iff], intros e, simp,
    intros h, simp[h] }
end

theorem Structure_consistent {T : Theory L} : M ⊧ T → Theory.consistent T :=
by { contrapose, simp[Theory.consistent], intros p hp₁ hp₂ hyp,
     exact soundness hp₂ hyp (λ _, default) (soundness hp₁ hyp (λ _, default)) }

lemma eval_eq : ∀ {t : term L} {e₁ e₂ : ℕ → |M|},
  (∀ n, n < t.arity → e₁ n = e₂ n) → t.val M e₁ = t.val M e₂
| (#n)               _  _  eqs := by simp at *; refine eqs _ _; simp
| (@term.app _ n f v)  e₁ e₂ eqs := by { simp at *, congr, funext i, refine @eval_eq (v i) _ _ (λ n eqn, _),
  have : (v i).arity ≤ ⨆ᶠ i, (v i).arity, from le_fintype_sup (λ i, (v i).arity) i,
  refine eqs n (lt_of_lt_of_le eqn this) }
  
lemma eval_iff : ∀ {p : formula L} {e₁ e₂ : ℕ → |M|},
  (∀ n, n < p.arity → e₁ n = e₂ n) → (M ⊧[e₁] p ↔ M ⊧[e₂] p)
| ⊤                      _  _  _   := by simp
| (@formula.app _ n p v) e₁ e₂ eqs := by { simp at*,
    suffices : (λ i, term.val M e₁ (v i)) = (λ i, term.val M e₂ (v i)), { simp[this] },
    funext i, refine @eval_eq _ M (v i) _ _ (λ n eqn, eqs n _),
    have : (v i).arity ≤ ⨆ᶠ i, (v i).arity, from le_fintype_sup (λ i, (v i).arity) i,
    refine (lt_of_lt_of_le eqn this) }
| (t =' u)               e₁ e₂ eqs := by { simp[formula.arity] at*,
    simp[eval_eq (λ n h, eqs _ (or.inl h)), eval_eq (λ n h, eqs _ (or.inr h))] }
| (p ⟶ q)                e₁ e₂ eqs := by { simp[formula.arity] at*,
    simp[eval_iff (λ n h, eqs _ (or.inl h)), eval_iff (λ n h, eqs _ (or.inr h))] }
| (∼p)                   e₁ e₂ eqs := by { simp[formula.arity] at*,
    simp[eval_iff eqs] }
| (∀.p)                 e₁ e₂ eqs := by { simp[formula.arity] at*,
    have : ∀ (d : |M|), p.val M (d ⌢ e₁) ↔ p.val M (d ⌢ e₂),
    { intros d, refine eval_iff (λ n eqn, _),
      cases n; simp[concat], refine eqs _ (by omega) },
    exact forall_congr this }

lemma eval_is_sentence_iff {p : formula L} (e : ℕ → |M|) (a : is_sentence p) : M ⊧[e] p ↔ M ⊧ p :=
⟨λ h e, by { refine (eval_iff $ λ n h, _).1 h, exfalso,
 simp[is_sentence] at*, rw[a] at h, exact nat.not_lt_zero n h},
 λ h, h e⟩

lemma models_neg_iff_of_is_sentence {p : formula L} (hp : is_sentence p) : M ⊧ ∼p ↔ ¬M ⊧ p :=
by { have : M ⊧[default] ∼p ↔ ¬M ⊧[default] p, by simp,
     simp only [hp, show is_sentence (∼p), by simp[hp], eval_is_sentence_iff] at this, exact this }

end fol