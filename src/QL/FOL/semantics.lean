import QL.FOL.deduction

universes u v
open_locale logic_symbol

namespace fol
open logic formula

structure Structure (L : language.{u}) :=
(dom : Type u)
(inhabited : inhabited dom)
(fn : ∀ {n}, L.fn n → (fin n → dom) → dom)
(pr : ∀ {n}, L.pr n → (fin n → dom) → Prop)

instance {L : language} : has_coe_to_sort (Structure L) (Type*) := ⟨Structure.dom⟩

variables {L : language.{u}} {S : Structure L}

instance (S : Structure L) : inhabited S.dom := S.inhabited

variables (S) {m n : ℕ}

open subterm subformula

namespace  subterm
variables {m} {m₁ m₂ : ℕ} {n} (me : fin m → S) (e : fin n → S)

@[simp] def val (me : fin m → S) (e : fin n → S) : subterm L m n → S
| (&x)           := me x
| (#x)           := e x
| (function f v) := S.fn f (λ i, (v i).val)

lemma val_rew (s : finitary (subterm L m₂ n) m₁) (me : fin m₂ → S) (e : fin n → S) : ∀ (t : subterm L m₁ n),
  (rew s t).val S me e = t.val S (val S me e ∘ s) e
| (&x)           := by simp
| (#x)           := by simp
| (function f v) := by simp; refine congr_arg _ (by ext i; exact val_rew (v i))

@[simp] lemma val_mlift (x : S) (t : subterm L m n) :
  t.mlift.val S (x *> me) e = t.val S me e :=
by simp[mlift_eq_rew, val_rew]; congr; ext x; simp

@[simp] lemma val_lift (x : S) (t : subterm L m n) :
  t.lift.val S me (x *> e) = t.val S me e :=
by induction t; simp*

@[simp] lemma val_push (me : fin m → S) (x : S) (e : fin n → S) (t : subterm L m (n + 1)) :
  val S (x *> me) e t.push = val S me (e <* x) t :=
by { induction t; simp*, case var : u { refine fin.last_cases _ _ u; simp } }

@[simp] lemma val_pull (me : fin m → S) (x : S) (e : fin n → S) (t : subterm L (m + 1) n) :
  val S me (e <* x) t.pull = val S (x *> me) e t :=
by { induction t; simp*, case metavar : u { refine fin.cases _ _ u; simp } }

end  subterm

namespace subformula
variables {m₁ m₂ : ℕ} {n} (me : fin m → S) (e : fin n → S)

@[simp] def val' (me : fin m → S) : ∀ {n} (e : fin n → S), subformula L m n → Prop
| n _ verum          := true
| n e (relation p v) := S.pr p (subterm.val S me e ∘ v)
| n e (equal t u)    := t.val S me e = u.val S me e
| n e (imply p q)    := p.val' e → q.val' e
| n e (neg p)        := ¬(p.val' e)
| n e (fal p)        := ∀ x : S.dom, (p.val' (x *> e))

@[irreducible] def val (me : fin m → S) (e : fin n → S) : subformula L m n →ₗ Prop :=
{ to_fun := val' S me e,
  map_neg' := λ _, by refl,
  map_imply' := λ _ _, by refl,
  map_and' := λ p q, by unfold has_inf.inf; simp[and]; refl,
  map_or' := λ p q, by unfold has_sup.sup; simp[or, ←or_iff_not_imp_left]; refl,
  map_top' := by refl,
  map_bot' := by simp[bot_def]; unfold has_top.top has_negation.neg; simp }

@[simp] lemma val_relation {p} (r : L.pr p) (v) :
  val S me e (relation r v) ↔ S.pr r (subterm.val S me e ∘ v) :=  by simp[val]; refl

@[simp] lemma val_equal (t u : subterm L m n) :
  val S me e (t =' u) ↔ (t.val S me e = u.val S me e) := by simp[val]; refl

@[simp] lemma val_fal (p : subformula L m (n + 1)) :
  val S me e (∀'p) ↔ ∀ x : S, val S me (x *> e) p := by simp[val]; refl

lemma val_rew (me : fin m₂ → S) : ∀ {n} (e : fin n → S) (s : finitary (subterm L m₂ n) m₁) (p : subformula L m₁ n),
  val S me e (rew s p) ↔ val S (subterm.val S me e ∘ s) e p
| n e s (relation r v) := by simp[subterm.val_rew]; refine iff_of_eq (congr_arg _ (by ext x; simp[subterm.val_rew]))
| n e s (equal t u)    := by simp[equal_eq, subterm.val_rew]  
| n e s verum          := by simp[top_eq]
| n e s (imply p q)    := by simp[imply_eq, val_rew _ _ p, val_rew _ _ q]
| n e s (neg p)        := by simp[neg_eq, val_rew _ _ p]
| n e s (fal p)        :=
    by{ simp[fal_eq, val_rew _ _ p], refine forall_congr (λ x, _),
        have : (subterm.val S me (x *> e) ∘ subterm.lift ∘ s) = subterm.val S me e ∘ s, by funext x; simp,
        rw this }
 
@[simp] lemma val_mlift (e : fin n → S) (x : S) (p : subformula L m n) :
  val S (x *> me) e p.mlift = val S me e p :=
by { simp[mlift_eq_rew, val_rew],
     have : subterm.val S (x *> me) e ∘ metavar ∘ fin.succ = me, by funext x; simp,
     rw this }

@[simp] lemma val_push (x : S) : ∀ {n} (e : fin n → S) (p : subformula L m (n + 1)),
  val S (x *> me) e p.push ↔ val S me (e <* x) p
| n e (relation r v) := by simp; refine iff_of_eq (congr_arg _ $ funext $ by simp)
| n e (equal t u)    := by simp[equal_eq]
| n e verum          := by simp[top_eq]
| n e (imply p q)    := by simp[imply_eq, val_push _ p, val_push _ q]
| n e (neg p)        := by simp[neg_eq, val_push _ p]
| n e (fal p)        := by { simp[fal_eq], refine forall_congr _,
  { intros y, simp[fin.left_right_concat_assoc], exact val_push (y *> e) p} }
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.2.complexity)⟩]}

@[simp] lemma val_pull (x : S) : ∀ {n} (e : fin n → S) (p : subformula L (m + 1) n),
  val S me (e <* x) p.pull ↔ val S (x *> me) e p
| n e (relation r v) := by simp; refine iff_of_eq (congr_arg _ $ funext $ by simp)
| n e (equal t u)    := by simp[equal_eq]
| n e verum          := by simp[top_eq]
| n e (imply p q)    := by simp[imply_eq, val_pull _ p, val_pull _ q]
| n e (neg p)        := by simp[neg_eq, val_pull _ p]
| n e (fal p)        := by { simp[fal_eq], refine forall_congr _,
  { intros y, simp[fin.left_right_concat_assoc], exact val_pull (y *> e) p} }

@[simp] lemma val_dummy (x : S) : ∀ {n} (e : fin n → S) (p : subformula L m n),
  val S me (e <* x) p.dummy ↔ val S me e p :=
by simp[dummy]

lemma val_msubst (p : subformula L (m + 1) n) (t : subterm L m n) :
  val S me e (msubst t p) ↔ val S (subterm.val S me e t *> me) e p :=
by simp[msubst, val_rew, fin.comp_left_concat, show subterm.val S me e ∘ metavar = me, from funext (by simp)]

lemma val_subst (p : subformula L m (n + 1)) (t : subterm L m n) :
  val S me e (subst t p) ↔ val S me (e <* subterm.val S me e t) p :=
by simp[subst, val_msubst]

@[simp] lemma val_universal_closure (p : subformula L m n) :
  val S me fin_zero_elim (∀'* p) ↔ ∀ v, val S me v p :=
begin
  induction n with n IH,
  { simp },
  { simp[IH (∀'p)], split,
    { intros h v, simpa[fin.left_concat_eq] using h (v ∘ fin.succ) (v 0) },
    { intros h v x, exact h (x *> v) } }
end

end subformula

namespace formula
variables (S) {me : fin m → S}

@[reducible] def val (me : fin m → S) : formula L m →ₗ Prop := subformula.val S me fin_zero_elim

notation S` ⊧[`:80 e`] `p :50 := val S e p

variables {S} {p q : formula L m}

@[simp] lemma models_relation {k} {r : L.pr k} {v} :
  S ⊧[me] relation r v ↔ S.pr r (subterm.val S me fin_zero_elim ∘ v) := by simp[val]

@[simp] lemma models_equal {t u : term L m} :
  S ⊧[me] (t =' u) ↔ t.val S me fin_zero_elim = u.val S me fin_zero_elim := by simp[val]

@[simp] lemma models_fal {p : subformula L m 1} :
  S ⊧[me] (∀'p : subformula _ _ _) ↔ ∀ x, S ⊧[x *> me] p.push :=
by simp[val, fin.concat_zero]

@[simp] lemma models_subst {p : subformula L m 1} (t : subterm L m 0) :
  S ⊧[me] (subst t p : subformula _ _ _) ↔ S ⊧[subterm.val S me fin_zero_elim t *> me] p.push :=
by simp[val, subformula.val_subst]

@[simp] lemma models_rew {x : S} : S ⊧[x *> me] p.mlift ↔ S ⊧[me] p :=
by simp[val]

end formula

def sentence.val : sentence L → Prop := formula.val S fin_zero_elim

def models (S : Structure L) (p : formula L m) : Prop := ∀ e, S ⊧[e] p

instance : semantics (formula L m) (Structure L) := ⟨models⟩

lemma models_def {S : Structure L} {p : formula L m} : S ⊧ p ↔ (∀ e, S ⊧[e] p) := by refl

abbreviation satisfiable (p : formula L m) : Prop := semantics.satisfiable (Structure L) p

abbreviation Satisfiable (T : preTheory L m) : Prop := semantics.Satisfiable (Structure L) T

namespace formula
variables {S} {m}

@[simp] lemma models_mlift {p : formula L m} : S ⊧ p.mlift ↔ S ⊧ p :=
by{ simp[models_def], split,
    { intros h e,
      have : S ⊧[default *> e] p.mlift, from h _,
      exact models_rew.mp this },
    { intros h e, rw ←fin.left_concat_eq e, simpa using h (e ∘ fin.succ)} }

end formula

namespace preTheory
variables {S} {m} {T : preTheory L m}

@[simp] lemma models_mlift : S ⊧ T.mlift ↔ S ⊧ T :=
⟨by { intros h p hp,
      have : S ⊧ p.mlift, from @h p.mlift (by simpa using hp),
      exact formula.models_mlift.mp this },
 by { intros h p hp,
      rcases preTheory.mem_mlift_iff.mp hp with ⟨q, hq, rfl⟩,
      exact formula.models_mlift.mpr (h hq) }⟩

end preTheory

instance : has_double_turnstile (preTheory L m) (formula L m) := ⟨semantics.consequence (Structure L)⟩

lemma consequence_def {T : preTheory L m} {p : formula L m} :
  T ⊧ p ↔ (∀ S : Structure L, S ⊧ T → S ⊧ p) := by refl

variables {S}

theorem soundness {T : preTheory L m} {p} : T ⊢ p → T ⊧ p := λ h,
begin
  apply provable.rec_on h,
  { intros m T p b IH S hT me,
    simp[formula.val], intros x,
    have : S ⊧ p, from @IH S (by simpa using hT),
    exact this (x *> me) },
  { intros m T p q b₁ b₂ m₁ m₂ S hT me,
    have h₁ : S ⊧[me] p → S ⊧[me] q, by simpa using m₁ hT me,
    have h₂ : S ⊧[me] p, from m₂ hT me,
    exact h₁ h₂ },
  { intros m T p hp S hS, exact hS hp },
  { intros m T S h me, simp },
  { intros m T p q S hS me, simp, intros h _, exact h },
  { intros m T p q r S hS me, simp,  intros h₁ h₂ h₃, exact h₁ h₃ (h₂ h₃) },
  { intros m T p q S hS me, simp, intros h₁, contrapose, exact h₁ },
  { intros m T p t S hS me, simp, intros h, exact h _ },
  { intros m T p q S hS me, simp, intros h₁ h₂ x, exact h₁ x h₂ },
  { intros T S hS me, simp },
  { intros T S hS me, simp, intros x₁ x₂, exact eq.symm },
  { intros T S hS me, simp, intros x₁ x₂ x₃, exact eq.trans },
  { intros T k f S hS me, simp[eq_axiom4], intros v h, exact congr_arg _ (funext h) },
  { intros T k r S hS me, simp[eq_axiom5], intros v h, exact cast (congr_arg _ (funext h)) }
end

namespace Structure
variables {L} (A B : Structure L)

structure hom :=
(to_fun : A → B)
(function {k} (f : L.fn k) : ∀ (a : fin k → A), to_fun (A.fn f a) = B.fn f (to_fun ∘ a))
(relation {k} (r : L.pr k) : ∀ (a : fin k → A), A.pr r a ↔ B.pr r (to_fun ∘ a))

infix ` →ₛ `:50 := hom

instance : has_coe_to_fun (hom A B) (λ _, A → B) := ⟨hom.to_fun⟩

end Structure

end fol