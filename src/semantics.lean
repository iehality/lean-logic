import deduction

universes u v

namespace fopl
open dvector

structure model (L : language.{u}) :=
(dom : Type u)
(inhabited : inhabited dom)
(fn : ∀ {n}, L.fn n → (fin n → dom) → dom)
(pr : ∀ {n}, L.pr n → (fin n → dom) → Prop)

notation `|`M`|` := model.dom M

variables {L : language.{u}} {M : model L}

local infix ` ≃₁ `:80 := ((≃) : term L → term L → formula L)
local prefix `∏₁ `:64 := (has_univ_quantifier.univ : formula L → formula L)
local prefix `∐₁ `:64 := (has_exists_quantifier.ex : formula L → formula L)

instance (M : model L) : inhabited M.dom := M.inhabited

@[simp] def term.val (e : ℕ → |M|) : term L → |M|
| (#x)           := e x
| (term.app f v) := M.fn f (λ i, (v i).val)

@[simp] def formula.val : ∀ (e : ℕ → |M|), formula L → Prop
| e (formula.app p v) := M.pr p (λ i, (v i).val e)
| e (t ≃₁ u)          := t.val e = u.val e
| e (p ⟶ q)          := p.val e → q.val e
| e (⁻p)              := ¬(p.val e)
| e (∏₁ p)            := ∀ d : M.dom, (p.val (d ⌢ e))

notation M` ⊧[`:80 e`] `p :50 := @formula.val _ M e p

def models (M : model L) (p : formula L) : Prop := ∀ (e : ℕ → |M|), M ⊧[e] p
infix ` ⊧ `:50 := models

def modelsth (M : model L) (T : theory L) : Prop := ∀ p, p ∈ T → M ⊧ p
infix ` ⊧ₜₕ `:50 := modelsth

lemma rew_val_eq (s : ℕ → term L) (e : ℕ → |M|) : ∀ (t : term L),
  (t.rew s).val e = t.val (λ n, (s n).val e)
| (#x)                := by simp
| (@term.app _ n f v) := by simp[λ i : fin n, rew_val_eq (v i)]

@[simp] lemma pow_val_concat (e : ℕ → |M|) (d : |M|) (t : term L) : (t^1).val (d ⌢ e) = t.val e :=
by simp[term.pow_eq, rew_val_eq]

lemma rew_val_iff : ∀ (s : ℕ → term L) (p : formula L) (e : ℕ → |M|),
  (p.rew s).val e ↔ p.val (λ n, (s n).val e)
| _ (formula.app p v) _ := by simp[formula.rew, rew_val_eq]
| _ (t ≃₁ u)           _ := by simp[formula.rew, term.val, rew_val_eq]
| _ (p ⟶ q)          _ := by simp[formula.rew, rew_val_iff _ p, rew_val_iff _ q]
| _ (⁻p)              _ := by simp[formula.rew, rew_val_iff _ p]
| s (∏₁ p)              e :=
  by { simp[formula.rew, rew_val_iff _ p], refine forall_congr (λ d, _),
       have : (λ n, ((s ^ 1) n).val (d ⌢ e) ) = (d ⌢ λ n, ((s n).val e)),
       { funext n, cases n; simp[concat, term.val, term.val], exact pow_val_concat _ _ _ },
       simp[this] }

@[simp] lemma pow_val_concat_iff : ∀ (p : formula L) (e : ℕ → |M|) d, (p^1).val (d ⌢ e) = p.val e :=
by simp[formula.pow_eq, rew_val_iff]

@[simp] lemma model_zero_val [has_zero_symbol L] {e : ℕ → |M|} : (0 : term L).val e = M.fn has_zero_symbol.zero finitary.nil :=
by simp[has_zero.zero]; congr

@[simp] lemma model_succ_val [has_succ_symbol L] (t : term L) {e : ℕ → |M|} :
  (Succ t).val e = M.fn has_succ_symbol.succ ‹t.val e› :=
by simp[has_succ.succ]; congr; ext; simp

private lemma modelsth_sf {T} : M ⊧ₜₕ T → M ⊧ₜₕ ⤊T := λ h p hyp_p e,
by { rcases hyp_p with ⟨p, hyp_p', rfl⟩, simp[formula.pow_eq, rew_val_iff],
     refine h _ hyp_p' _ }

@[simp] lemma models_ex {p : formula L} {e : ℕ → |M|} : (∐₁ p).val e ↔ ∃ d, p.val (d ⌢ e) :=
by simp[has_exists_quantifier.ex, formula.ex, models, rew_val_iff]

lemma models_univs {p : formula L} {e : ℕ → |M|} {n} :
  (∏[n] p).val e ↔ ∀ d : finitary (|M|) n, p.val (λ i, if h : i < n then d ⟨i, h⟩ else e (i - n)) :=
begin
  induction n with n IH generalizing e; simp,
  { refine ⟨λ h _, h, λ h, h ∅⟩ },
  { simp[IH], split,
    { intros h D, refine cast _ (h D.head_inv D.tail_inv), congr, funext i, simp[concat, slide'],
      have C : i < n ∨ i = n ∨ n < i, exact trichotomous i n,
      cases C,
      { simp[C, nat.lt.step C, finitary.tail_inv] }, rcases C with (rfl | C),
      { simp[←nat.add_one], refl },
      { simp[show ¬i < n, from asymm C, show ¬i < n.succ, by omega, C, ←nat.add_one,
             show i - n - 1 = i - (n + 1), from tsub_tsub i n 1] } },
    { intros h d D, refine cast _ (h (D ᶠ:: d)), congr, funext i, simp[concat, slide'],
      have C : i < n ∨ i = n ∨ n < i, exact trichotomous i n,
      cases C,
      { simp[C, nat.lt.step C, finitary.cons_inv] }, rcases C with (rfl | C), 
      { simp[←nat.add_one] },
      { simp[show ¬i < n, from asymm C, show ¬i < n.succ, by omega, C, ←nat.add_one,
             show i - n - 1 = i - (n + 1), from tsub_tsub i n 1] } } }
end

@[simp] lemma models_and {p q : formula L} {e : ℕ → |M|} : (p ⊓ q).val e ↔ (p.val e ∧ q.val e) :=
by simp[has_inf.inf, formula.and]

@[simp] lemma models_or {p q : formula L} {e : ℕ → |M|} : (p ⊔ q).val e ↔ (p.val e ∨ q.val e) :=
by {simp[has_sup.sup, formula.or], exact or_iff_not_imp_left.symm }

@[simp] lemma models_iff {p q : formula L} {e : ℕ → |M|} : (p ⟷ q).val e ↔ (p.val e ↔ q.val e) :=
by simp[lrarrow_def]; exact iff_def.symm

@[simp] lemma models_conjunction' {n : ℕ} {P : finitary (formula L) n} {e : ℕ → |M|} :
  (conjunction' n P).val e ↔ ∀ i, (P i).val e :=
by { induction n with n IH; simp[has_top.top, formula.top],
     { intros i, exfalso, exact i.val.not_lt_zero i.property },
     { simp [IH], split,
       { rintros ⟨h0, h1⟩, intros i,
         have : i.val < n ∨ i.val = n := nat.lt_succ_iff_lt_or_eq.mp i.property,
         cases this,
         { have := h1 ⟨↑i, this⟩, simp at this, refine this },
         { simp[←this] at*, refine h0 } },
       { intros h, refine ⟨h _, λ _, h _⟩ } } }

@[simp] lemma models_pow {p : formula L} {i : ℕ} {e : ℕ → |M| } : (p^i).val e ↔ p.val (λ n, e (n + i)) :=
by simp[formula.pow_eq, rew_val_iff]

lemma models_subst {p : formula L} {i : ℕ} {t : term L} {e : ℕ → |M| } :
  (p.rew ι[i ⇝ t]).val e ↔ p.val (λ n, if n < i then e n else if i < n then e (n - 1) else t.val e) :=
by { simp[rew_val_iff],
     have : (λ (n : ℕ), term.val e (ι[i ⇝ t] n)) = (λ n, if n < i then e n else if i < n then e (n - 1) else t.val e),
     { funext n,
       have C : n < i ∨ n = i ∨ i < n, exact trichotomous n i,
       cases C, simp[C],
       cases C; simp[C], simp[asymm C] },
     simp[this] }

@[simp] lemma models_subst_0 {p : formula L} {t : term L} {e : ℕ → |M| } :
  (p.rew ι[0 ⇝ t]).val e ↔ p.val (t.val e ⌢ e) :=
by { have := @models_subst _ _ p 0 t e, simp at this,
     have eqn : (λ n, ite (0 < n) (e (n - 1)) (t.val e)) = t.val e ⌢ e,
     { funext n, cases n; simp }, rw[←eqn], exact this }

@[simp] lemma models_subst_1 {p : formula L} {t : term L} {e : ℕ → |M| } :
  (p.rew ι[1 ⇝ t]).val e ↔ p.val (e 0 ⌢ t.val e ⌢ (λ x, e (x + 1))) :=
by { have := @models_subst _ _ p 1 t e,
     have eqn : (λ n, ite (n < 1) (e n) (ite (1 < n) (e (n - 1)) (t.val e))) =
       e 0 ⌢ t.val e ⌢ (λ x, e (x + 1)),
     { funext n, cases n; simp[←nat.add_one], cases n; simp }, rw[←eqn], exact this }

lemma nfal_models_iff : ∀ {n} {p : formula L}, M ⊧ nfal p n ↔ M ⊧ p
| 0     _ := iff.rfl
| (n+1) p := by { simp[←@nfal_models_iff n p], refine ⟨λ h e, _, λ h e d, h _⟩,
  have : ((e 0) ⌢ λ x, e (x + 1) )= e, { ext x, cases x; simp[concat] },
  have := h (λ x, e (x + 1)) (e 0), simp* at* }


theorem soundness {T : theory L} : ∀ {p}, T ⊢ p → ∀ {M}, M ⊧ₜₕ T → M ⊧ p := λ p hyp,
begin
  induction hyp,
  case fopl.provable.GE : T p hyp_p IH
  { intros M hyp_T e d, exact IH (modelsth_sf hyp_T) _ },
  case fopl.provable.MP : T p q hyp_pq hyp_p IH_pq IH_p
  { intros M hyp_T e, exact IH_pq hyp_T e (IH_p hyp_T e) },
  case fopl.provable.AX : T p hyp_p
  { intros M hyp_T e, exact hyp_T _ hyp_p _ },
  case fopl.provable.p1 : T p q
  { intros M hyp_T e h₁ h₂, exact h₁ },
  case fopl.provable.p2 : T p q r
  { intros M hyp_T e h₁ h₂ h₃, exact (h₁ h₃) (h₂ h₃) },
  case fopl.provable.p3 : T p q
  { intros M hyp_T e h₁, simp[formula.val], contrapose, exact h₁ },
  case fopl.provable.q1 : T p t
  { intros M hyp_T e h, simp[rew_val_iff] at h ⊢,
    have : (λ n, (ι[0 ⇝ t] n).val e) = (t.val e) ⌢ e,
    { funext n, cases n; simp[term.val, term.val, concat] },
    rw this, exact h _ },
  case fopl.provable.q2 : T p q
  { intros M hyp_T e h₁ h₂ d, exact (h₁ d) (h₂ d) },
  case fopl.provable.q3 : T p
  { intros M hyp_T e h d, simp, exact h },
  case fopl.provable.e1 : T
  { intros M hyp_T e t, simp[formula.val] },
  case fopl.provable.e2 : T
  { intros M hyp_T e t₁ t₂, simp[formula.val], refine eq.symm },
  case fopl.provable.e3 : T
  { intros M hyp_T e t₁ t₂ t₃, simp[formula.val], refine eq.trans },
  case fopl.provable.e4 : T n f
  { simp[eq_axiom4, nfal_models_iff], intros M hyp_T e,
    simp, intros h, simp[h] },
  case fopl.provable.e5 : T n f
  { simp[eq_axiom5, nfal_models_iff], intros M hyp_T e,
    simp, intros h, simp[h] },
end

theorem model_consistent {T : theory L} : M ⊧ₜₕ T → theory.consistent T :=
by { contrapose, simp[theory.consistent], intros p hp₁ hp₂ hyp,
     exact soundness hp₂ hyp (λ _, (default M.dom)) (soundness hp₁ hyp (λ _, (default M.dom))) }

lemma eval_eq : ∀ {t : term L} {e₁ e₂ : ℕ → |M|},
  (∀ n, n < t.arity → e₁ n = e₂ n) → t.val e₁ = t.val e₂
| (#n)               _  _  eqs := by simp at *; refine eqs _ _; simp
| (@term.app _ n f v)  e₁ e₂ eqs := by { simp at *, congr, funext i, refine @eval_eq (v i) _ _ (λ n eqn, _),
  have : (v i).arity ≤ finitary.Max 0 (λ i, (v i).arity), from finitary.Max_le 0 (λ i, (v i).arity) i,
  refine eqs n (lt_of_lt_of_le eqn this) }
  
lemma eval_iff : ∀ {p : formula L} {e₁ e₂ : ℕ → |M|},
  (∀ n, n < p.arity → e₁ n = e₂ n) → (M ⊧[e₁] p ↔ M ⊧[e₂] p)
| (@formula.app _ n p v) e₁ e₂ eqs := by { simp[sentence] at*,
    suffices : (λ i, term.val e₁ (v i)) = (λ i, term.val e₂ (v i)), { simp[this] },
    funext i, refine @eval_eq _ M (v i) _ _ (λ n eqn, eqs n _),
    have : (v i).arity ≤ finitary.Max 0 (λ i, (v i).arity), from finitary.Max_le 0 (λ i, (v i).arity) i,
    refine (lt_of_lt_of_le eqn this) }
| (t ≃₁ u)                e₁ e₂ eqs := by { simp[sentence, formula.arity] at*,
    simp[eval_eq (λ n h, eqs _ (or.inl h)), eval_eq (λ n h, eqs _ (or.inr h))] }
| (p ⟶ q)               e₁ e₂ eqs := by { simp[sentence, formula.arity] at*,
    simp[eval_iff (λ n h, eqs _ (or.inl h)), eval_iff (λ n h, eqs _ (or.inr h))] }
| (⁻p)                   e₁ e₂ eqs := by { simp[sentence, formula.arity] at*,
    simp[eval_iff eqs] }
| (∏₁ p)                   e₁ e₂ eqs := by { simp[sentence, formula.arity] at*,
    have : ∀ (d : |M|), p.val (d ⌢ e₁) ↔ p.val (d ⌢ e₂),
    { intros d, refine eval_iff (λ n eqn, _),
      cases n; simp[concat], refine eqs _ (by omega) },
    exact forall_congr this }

lemma eval_sentence_iff {p : formula L} {e : ℕ → |M|} (a : sentence p) : M ⊧[e] p ↔ M ⊧ p :=
⟨λ h e, by { refine (eval_iff $ λ n h, _).1 h, exfalso,
 simp[sentence] at*, rw[a] at h, exact nat.not_lt_zero n h},
 λ h, h e⟩

class theory_of_model (M : model L) (T : theory L) :=
(models : M ⊧ₜₕ T)

end fopl