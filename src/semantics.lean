import deduction

universes u v

namespace fopl
open dvector

structure model (L : language.{u}) :=
(dom : Type v)
(one : dom)
(fn : ∀ {n}, L.fn n → dvector dom n → dom)
(pr : ∀ {n}, L.pr n → dvector dom n → Prop)


variables {L : language.{u}} {M : model L}

instance (M : model L) : inhabited M.dom := ⟨M.one⟩

@[simp] def vecterm.val (e : ℕ → M.dom) : ∀ {n} (t : vecterm L n), dvector M.dom (n+1)
| _ (vecterm.cons a v) := a.val.append v.val
| _ (#x)               := unary (e x)
| _ (vecterm.const c)  := unary (M.fn c dvector.nil)
| _ (vecterm.app f v)  := unary (M.fn f v.val)

@[simp] def term.val (e : ℕ → M.dom) (t : term L) : M.dom := (t.val e).extract

@[simp] def form.val : (ℕ → M.dom) → form L → Prop
| _ (form.const c) := M.pr c dvector.nil
| e (form.app p v) := M.pr p (v.val e)
| e (t =̇ u)        := t.val e = u.val e
| e (p →̇ q)       := p.val e → q.val e
| e (¬̇p)           := ¬(p.val e)
| e (Ȧp)           := ∀ d : M.dom, (p.val (d ^ˢ e))

def models (M : model L) (p : form L) : Prop := ∀ (e : ℕ → M.dom), p.val e
infix ` ⊧ `:50 := models

def modelsth (M : model L) (T : form L → Prop) : Prop := ∀ (e : ℕ → M.dom) p, T p → p.val e
infix ` ⊧ₜₕ `:50 := modelsth

lemma rew_val_eq : ∀ (s : ℕ → term L) {n} (t : vecterm L n) (e : ℕ → M.dom),
  (t.rew s).val e = t.val (λ n, (s n).val e)
| _ _ (vecterm.cons a v) _ := by simp[vecterm.rew, rew_val_eq _ a, rew_val_eq _ v]
| _ _ (#x)               _ := by simp[vecterm.rew, term.val]
| _ _ (vecterm.const c)  _ := rfl 
| _ _ (vecterm.app f v)  _ := by simp[vecterm.rew, rew_val_eq _ v]

@[simp] lemma sf_slide_val {n} (t : vecterm L n) : ∀ (e : ℕ → M.dom) d, t.sf.val (d ^ˢ e) = t.val e :=
by induction t; simp[slide]; simp*

lemma rew_val_iff : ∀ (s : ℕ → term L) (p : form L) (e : ℕ → M.dom),
  (p.rew s).val e ↔ p.val (λ n, (s n).val e)
| _ (form.const c) _ := by simp[form.rew]
| _ (form.app p v) _ := by simp[form.rew, rew_val_eq]
| _ (t =̇ u)        _ := by simp[form.rew, term.val, rew_val_eq]
| _ (p →̇ q)       _ := by simp[form.rew, rew_val_iff _ p, rew_val_iff _ q]
| _ (¬̇p)           _ := by simp[form.rew, rew_val_iff _ p]
| s (Ȧp)           e := by { simp[form.rew, rew_val_iff _ p], refine forall_congr (λ d, _),
    have : (λ n, (((#0 ^ˢ λ x, (s x).sf) n).val (d ^ˢ e)).extract) = (d ^ˢ λ n, ((s n).val e)),
    { funext n,cases n; simp[slide, term.val, vecterm.val] },
    simp[this] }

@[simp] lemma sf_slide_val_iff : ∀ (p : form L) (e : ℕ → M.dom) d, p.sf.val (d ^ˢ e) = p.val e
| (form.const c) _ _ := rfl
| (form.app p v) _ _ := by simp
| (t =̇ u)        _ _ := by simp[term.val]
| (p →̇ q)       _ _ := by simp[sf_slide_val_iff p, sf_slide_val_iff q]
| (¬̇p)           _ _ := by simp[sf_slide_val_iff p]
| (Ȧp)           _ _ := by simp[term.val, form.sf, rew_val_iff, slide]

private lemma modelsth_sf {T} : M ⊧ₜₕ T → M ⊧ₜₕ ⇑T := λ h e p hyp_p,
by { cases hyp_p with p hyp_p', simp[rew_val_iff],
     refine h _ _ hyp_p' }

theorem soundness {T : theory L} : ∀ {p}, T ⊢̇ p → ∀ {M}, M ⊧ₜₕ T → M ⊧ p := λ p hyp,
begin
  induction hyp,
  case fopl.provable.GE : T p hyp_p IH
  { intros M hyp_T e d, exact IH (modelsth_sf hyp_T) _ },
  case fopl.provable.MP : T p q hyp_pq hyp_p IH_pq IH_p
  { intros M hyp_T e, exact IH_pq hyp_T e (IH_p hyp_T e) },
  case fopl.provable.AX : T p hyp_p
  { intros M hyp_T e, exact hyp_T e _ hyp_p },
  case fopl.provable.p1 : T p q
  { intros M hyp_T e h₁ h₂, exact h₁ },
  case fopl.provable.p2 : T p q r
  { intros M hyp_T e h₁ h₂ h₃, exact (h₁ h₃) (h₂ h₃) },
  case fopl.provable.p3 : T p q
  { intros M hyp_T e h₁, simp[form.val], contrapose, exact h₁ },
  case fopl.provable.q1 : T p t
  { intros M hyp_T e h, simp[form.subst₁, rew_val_iff] at h ⊢,
    have : (λ n, (vecterm.val e (t ^ˢ vecterm.var $ n)).extract) = (t.val e) ^ˢ e,
    { funext n, cases n; simp[slide, term.val, vecterm.val] },
    rw this, exact h _ },
  case fopl.provable.q2 : T p q
  { intros M hyp_T e h₁ h₂ d, exact (h₁ d) (h₂ d) },
  case fopl.provable.q3 : T p
  { intros M hyp_T e h d, simp, exact h },
  case fopl.provable.e1 : T t
  { intros M hyp_T e, simp[form.val] },
  case fopl.provable.e2 : T p t u
  { intros M hyp_T e, simp[form.subst₁, rew_val_iff],
    intros eqn h,
    have : (λ n, (vecterm.val e (u ^ˢ vecterm.var $ n)).extract) = (λ n, ((t ^ˢ vecterm.var) n).val e),
    { funext n, cases n; simp[slide, term.val, eqn] },
    simp[this, h], }
end

theorem model_consistent {T : theory L} : M ⊧ₜₕ T → T.consistent :=
by { contrapose, simp[theory.consistent], intros p hp₁ hp₂ hyp,
     exact soundness hp₂ hyp (λ _, (default M.dom)) (soundness hp₁ hyp (λ _, (default M.dom))) }

@[simp] lemma models_ex {p} {e : ℕ → M.dom} : (Ėp).val e ↔ ∃ d, p.val (d ^ˢ e) :=
by simp[form.ex, models, form.subst₁, rew_val_iff]

@[simp] lemma models_and {p q} {e : ℕ → M.dom} : (p ⩑ q).val e ↔ (p.val e ∧ q.val e) :=
by simp[form.and]

@[simp] lemma models_iff {p q} {e : ℕ → M.dom} : (p ↔̇ q).val e ↔ (p.val e ↔ q.val e) :=
by simp[form.iff]; exact iff_def.symm

end fopl