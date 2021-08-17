import deduction

universes u v

namespace fopl
open dvector

structure model (L : language.{u}) :=
(dom : Type u)
(one : dom)
(fn : ∀ {n}, L.fn n → dvector dom n → dom)
(pr : ∀ {n}, L.pr n → dvector dom n → Prop)

notation `|`M`|` := model.dom M

variables {L : language.{u}} {M : model L}

instance (M : model L) : inhabited M.dom := ⟨M.one⟩

@[simp] def vecterm.val (e : ℕ → |M|) : ∀ {n} (t : vecterm L n), dvector M.dom (n+1)
| _ (vecterm.cons a v) := a.val.head :: v.val
| _ (#x)               := unary (e x)
| _ (vecterm.const c)  := unary (M.fn c dvector.nil)
| _ (vecterm.app f v)  := unary (M.fn f v.val)

@[simp] def term.val (e : ℕ → |M|) (t : term L) : M.dom := (t.val e).head

@[simp] def formula.val : (ℕ → |M|) → formula L → Prop
| _ (formula.const c) := M.pr c dvector.nil
| e (formula.app p v) := M.pr p (v.val e)
| e (t =̇ u)        := t.val e = u.val e
| e (p →̇ q)       := p.val e → q.val e
| e (¬̇p)           := ¬(p.val e)
| e (∀̇p)           := ∀ d : M.dom, (p.val (d ⌢ e))

notation M` ⊧[`:80 e`] `p :50 := @formula.val _ M e p

def models (M : model L) (p : formula L) : Prop := ∀ (e : ℕ → |M|), M ⊧[e] p
infix ` ⊧ `:50 := models

def modelsth (M : model L) (T : theory L) : Prop := ∀ p, p ∈ T → M ⊧ p
infix ` ⊧ₜₕ `:50 := modelsth

lemma rew_val_eq : ∀ (s : ℕ → term L) {n} (t : vecterm L n) (e : ℕ → |M|),
  (t.rew s).val e = t.val (λ n, (s n).val e)
| _ _ (vecterm.cons a v) _ := by simp[vecterm.rew, rew_val_eq _ a, rew_val_eq _ v]
| _ _ (#x)               _ := by {simp[vecterm.rew, term.val] }
| _ _ (vecterm.const c)  _ := rfl 
| _ _ (vecterm.app f v)  _ := by simp[vecterm.rew, rew_val_eq _ v]

@[simp] lemma pow_val_concat {n} (t : vecterm L n) : ∀ (e : ℕ → |M|) d, (t^1).val (d ⌢ e) = t.val e :=
by { induction t; simp[concat] at*; simp* }

lemma rew_val_iff : ∀ (s : ℕ → term L) (p : formula L) (e : ℕ → |M|),
  (p.rew s).val e ↔ p.val (λ n, (s n).val e)
| _ (formula.const c) _ := by simp[formula.rew]
| _ (formula.app p v) _ := by simp[formula.rew, rew_val_eq]
| _ (t =̇ u)        _ := by simp[formula.rew, term.val, rew_val_eq]
| _ (p →̇ q)       _ := by simp[formula.rew, rew_val_iff _ p, rew_val_iff _ q]
| _ (¬̇p)           _ := by simp[formula.rew, rew_val_iff _ p]
| s (∀̇p)           e := by { simp[formula.rew, rew_val_iff _ p], refine forall_congr (λ d, _),
    have : (λ n, (vecterm.val (d ⌢ e) (s^1 $ n)).head) = (d ⌢ λ n, ((s n).val e)),
    { funext n, cases n; simp[concat, term.val, vecterm.val], exact pow_val_concat _ _ _ },
    simp[this] }

@[simp] lemma pow_val_concat_iff : ∀ (p : formula L) (e : ℕ → |M|) d, (p^1).val (d ⌢ e) = p.val e
| (formula.const c) _ _ := rfl
| (formula.app p v) _ _ := by simp
| (t =̇ u)        _ _ := by simp[term.val]
| (p →̇ q)       _ _ := by simp[pow_val_concat_iff p, pow_val_concat_iff q]
| (¬̇p)           _ _ := by simp[pow_val_concat_iff p]
| (∀̇p)           e d₀ := by {intros, simp, simp[formula.pow_eq, rew_val_iff], apply forall_congr,
    intros d,
    have : (λ n, (vecterm.val (d ⌢ d₀ ⌢ e) ((λ x, #(x + 1))^1 $ n)).head) = (d ⌢ e),
    { ext n, cases n; simp[concat] }, simp[this] }

private lemma modelsth_sf {T} : M ⊧ₜₕ T → M ⊧ₜₕ ⇑T := λ h p hyp_p e,
by { rcases hyp_p with ⟨p, hyp_p', rfl⟩, simp[formula.pow_eq, rew_val_iff],
     refine h _ hyp_p' _ }

@[simp] lemma models_ex {p} {e : ℕ → |M|} : (∃̇p).val e ↔ ∃ d, p.val (d ⌢ e) :=
by simp[formula.ex, models, rew_val_iff]

@[simp] lemma models_and {p q} {e : ℕ → |M|} : (p ⩑ q).val e ↔ (p.val e ∧ q.val e) :=
by simp[formula.and]

@[simp] lemma models_iff {p q} {e : ℕ → |M|} : (p ↔̇ q).val e ↔ (p.val e ↔ q.val e) :=
by simp[formula.iff]; exact iff_def.symm

@[simp] lemma models_equals : ∀ {n} (v₁ v₂ : vecterm L n) (e : ℕ → |M|),
  (v₁ ≡̇ v₂).val e ↔ v₁.val e = v₂.val e
| 0     t₁ t₂ e := by simp[formula.val]
| (n+1) (vecterm.cons t₁ v₁) (vecterm.cons t₂ v₂) e := by simp[formula.val, models_equals v₁ v₂]

@[simp] lemma models_pow {p : formula L} {i : ℕ} {e : ℕ → |M| } : (p^i).val e ↔ p.val (λ n, e (n + i)) :=
by simp[formula.pow_eq, rew_val_iff]

lemma models_subst {p : formula L} {i : ℕ} {t : term L} {e : ℕ → |M| } :
  (p.rew ι[i ⇝ t]).val e ↔ p.val (λ n, if n < i then e n else if i < n then e (n - 1) else t.val e) :=
by { simp[rew_val_iff],
     have : (λ (n : ℕ), (vecterm.val e (ι[i ⇝ t] n)).head) =
     (λ n, if n < i then e n else if i < n then e (n - 1) else t.val e),
     { funext n,
       have C : n < i ∨ n = i ∨ i < n, exact trichotomous n i,
       cases C; simp[C],
       cases C; simp[C], simp[asymm C] },
     simp[this] }

@[simp] lemma models_subst_0 {p : formula L} {t : term L} {e : ℕ → |M| } :
  (p.rew ι[0 ⇝ t]).val e ↔ p.val (t.val e ⌢ e) :=
by { have := @models_subst _ _ p 0 t e, simp at this,
     have eqn : (λ n, ite (0 < n) (e (n - 1)) (t.val e)) = t.val e ⌢ e,
     { funext n, cases n; simp }, rw[←eqn], exact this }

@[simp] lemma models_subst_1 {p : formula L} {t : term L} {e : ℕ → |M| } :
  (p.rew ι[1 ⇝ t]).val e ↔ p.val (e 0 ⌢ t.val e ⌢ (λ x, e (x + 1))) :=
by { have := @models_subst _ _ p 1 t e, simp at this,
     have eqn : (λ n, ite (n < 1) (e n) (ite (1 < n) (e (n - 1)) (vecterm.val e t).head)) =
       e 0 ⌢ t.val e ⌢ (λ x, e (x + 1)),
     { funext n, cases n; simp[←nat.add_one], cases n; simp }, rw[←eqn], exact this }

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
    have : (λ n, (vecterm.val e (ι[0 ⇝ t] n)).head) = (t.val e) ⌢ e,
    { funext n, cases n; simp[term.val, vecterm.val, concat] },
    rw this, exact h _ },
  case fopl.provable.q2 : T p q
  { intros M hyp_T e h₁ h₂ d, exact (h₁ d) (h₂ d) },
  case fopl.provable.q3 : T p
  { intros M hyp_T e h d, simp, exact h },
  case fopl.provable.e1 : T t
  { intros M hyp_T e, simp[formula.val] },
  case fopl.provable.e2 : T t₁ t₂
  { intros M hyp_T e, simp[formula.val], refine eq.symm },
  case fopl.provable.e3 : T t₁ t₂ t₃
  { intros M hyp_T e, simp[formula.val], refine eq.trans },
  case fopl.provable.e4 : T n t₁ t₂ f
  { intros M hyp_T e, simp[formula.val], refine λ eqn, (by simp[eqn]) },
  case fopl.provable.e5 : T n t₁ t₂ f
  { intros M hyp_T e, simp[formula.val], refine λ eqn, (by simp[eqn]) },
end

theorem model_consistent {T : theory L} : M ⊧ₜₕ T → theory.consistent T :=
by { contrapose, simp[theory.consistent], intros p hp₁ hp₂ hyp,
     exact soundness hp₂ hyp (λ _, (default M.dom)) (soundness hp₁ hyp (λ _, (default M.dom))) }

lemma eval_eq : ∀ {n} {v : vecterm L n} {e₁ e₂ : ℕ → |M|},
  (∀ n, n < v.arity → e₁ n = e₂ n) → v.val e₁ = v.val e₂
| (n+1) (vecterm.cons t v) e₁ e₂ a := by { simp[vecterm.arity] at *,
    refine ⟨eval_eq (λ n h, a _ (or.inl h)), eval_eq (λ n h, a _ (or.inr h))⟩ }
| _     (#n)               _  _  a := by { simp[vecterm.arity] at *, refine a _ _, simp }
| _     (vecterm.const c)  _  _  a := by simp
| _     (vecterm.app f v)  e₁ e₂ a := by { simp[vecterm.arity] at *, 
    simp[eval_eq a] } 

lemma eval_iff : ∀ {p : formula L} {e₁ e₂ : ℕ → |M|},
  (∀ n, n < p.arity → e₁ n = e₂ n) → (M ⊧[e₁] p ↔ M ⊧[e₂] p)
| (formula.const _) _  _  _ := by simp* at *
| (formula.app p v) e₁ e₂ a := by { simp[sentence, formula.arity] at*, simp[eval_eq a] }
| (t =̇ u)        e₁ e₂ a := by { simp[sentence, formula.arity] at*,
  simp[eval_eq (λ n h, a _ (or.inl h)), eval_eq (λ n h, a _ (or.inr h))] }
| (p →̇ q)       e₁ e₂ a := by { simp[sentence, formula.arity] at*,
    simp[eval_iff (λ n h, a _ (or.inl h)), eval_iff (λ n h, a _ (or.inr h))] }
| (¬̇p)           e₁ e₂ a := by { simp[sentence, formula.arity] at*,
    simp[eval_iff a] }
| (∀̇p)           e₁ e₂ a := by { simp[sentence, formula.arity] at*,
    have : ∀ (d : |M|), p.val (d ⌢ e₁) ↔ p.val (d ⌢ e₂),
    { intros d, refine eval_iff (λ n eqn, _),
      cases n; simp[concat], refine a _ (nat.lt_sub_right_of_add_lt eqn) },
    exact forall_congr this }

lemma eval_sentence_iff {p : formula L} {e : ℕ → |M|} (a : sentence p) : M ⊧[e] p ↔ M ⊧ p :=
⟨λ h e, by { refine (eval_iff $ λ n h, _).1 h, exfalso,
 simp[sentence] at*, rw[a] at h, exact nat.not_lt_zero n h},
 λ h, h e⟩

lemma nfal_models_iff : ∀ {n} {p : formula L}, M ⊧ p ↔ M ⊧ nfal p n
| 0     _ := iff.rfl
| (n+1) p := by { simp[@nfal_models_iff n p], refine ⟨λ h e d, h _, λ h e, _⟩,
  have : ((e 0) ⌢ λ x, e (x + 1) )= e, { ext x, cases x; simp[concat] },
  have := h (λ x, e (x + 1)) (e 0), simp* at * }

end fopl