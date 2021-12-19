import deduction

universes u v

namespace fopl
open formula term

namespace language

class translation (L₁ : language.{u}) (L₂ : language.{u}) :=
(tr_pr : Π {n}, L₁.pr n → finitary (term L₁) n → formula L₂)
(tr_eq : term L₁ → term L₁ → formula L₂)

@[simp] def translation.tr {L₁ L₂ : language.{u}} [translation L₁ L₂] : formula L₁ → formula L₂
| (app p v)            := translation.tr_pr p v
| ((t : term L₁) ≃ u)  := translation.tr_eq t u
| (p ⟶ q)              := translation.tr p ⟶ translation.tr q
| (⁻p)                 := ⁻translation.tr p
| (∏ (p : formula L₁)) := ∏ translation.tr p

notation `tr[` p `]` := translation.tr p

instance {L₁ L₂ : language.{u}} : has_coe_to_fun (translation L₁ L₂) (λ _, formula L₁ → formula L₂) :=
⟨λ t, @translation.tr L₁ L₂ t⟩

lemma app_translation {L₁ L₂ : language.{u}} (tr : translation L₁ L₂) {n} (p : L₁.pr n) (v) :
  tr (formula.app p v) = @translation.tr_pr _ _ tr n p v := rfl

def translation.tr_theory {L₁ L₂ : language.{u}} [translation L₁ L₂] (T : theory L₁) : theory L₂ :=
translation.tr '' T

class term_translation_aux (L₁ : language.{u}) (L₂ : language.{u}) :=
(tr_fn : Π {n}, L₁.fn n → finitary (term L₂) n → term L₂)

@[simp] def term_translation_aux.tr {L₁ L₂ : language.{u}} [term_translation_aux L₁ L₂] : term L₁ → term L₂
| #n        := #n
| (app f v) := term_translation_aux.tr_fn f (λ i, term_translation_aux.tr (v i))

notation `trₜ[` t `]` := term_translation_aux.tr t

class term_translation (L₁ : language.{u}) (L₂ : language.{u})
  extends translation L₁ L₂, term_translation_aux L₁ L₂ :=
(consistence : ∀ (t u : term L₁), (tr[(t ≃ u : formula L₁)] : formula L₂) = ((trₜ[t] : term L₂) ≃ trₜ[u]))


namespace translation
variables {L₁ L₂ : language.{u}}

def of_term_translation [term_translation_aux L₁ L₂]
  (tr_pr' : Π {n}, L₁.pr n → finitary (term L₂) n → formula L₂) : translation L₁ L₂ :=
{ tr_pr := λ n p v, tr_pr' p (λ i, trₜ[v i]),
  tr_eq := λ t u, (trₜ[t] : term L₂) ≃ trₜ[u] } 

end translation

instance : has_add language := ⟨λ L₁ L₂ : language.{u}, ⟨λ n, L₁.fn n ⊕ L₂.fn n, λ n, L₁.pr n ⊕ L₂.pr n⟩⟩ 

section

variables {L₁ L₂ : language.{u}} [translation L₁ L₂]

@[simp] lemma translation_ex_eq (p : formula L₁) :
  (tr[(∐ p : formula L₁)] : formula L₂) = ∐ (tr[p] : formula L₂) := rfl

@[simp] lemma translation_and_eq (p q : formula L₁) :
  (tr[p ⊓ q] : formula L₂) = tr[p] ⊓ tr[q] := rfl

@[simp] lemma translation_or_eq (p q : formula L₁) :
  (tr[p ⊔ q] : formula L₂) = tr[p] ⊔ tr[q] := rfl

@[simp] lemma translation_iff_eq (p q : formula L₁) :
  (tr[p ⟷ q] : formula L₂) = tr[p] ⟷ tr[q] := rfl

@[reducible] def theory_tr (L₂ : language) [translation L₁ L₂] (T : theory L₁) : theory L₂ := translation.tr '' T

notation `Tr[` T `]` := theory_tr _ T

@[simp] lemma mem_theory_tr_of_mem {T : theory L₁} {p} (mem : p ∈ T): tr[p] ∈ (L₂.theory_tr T) :=
⟨p, mem, rfl⟩

end

section 
variables {L₁ L₂ : language.{u}} 

def fn_to_add {n} (f : L₁.fn n) : (L₁ + L₂).fn n := sum.inl f

def pr_to_add {n} (p : L₁.pr n) : (L₁ + L₂).pr n := sum.inl p

@[simp] def add_tr_v1 : term L₁ → term (L₁ + L₂)
| (#x)       := #x
| (app f v)  := app (fn_to_add f) (λ i, add_tr_v1 (v i))

instance : translation L₁ (L₁ + L₂) :=
⟨λ n p v, app (pr_to_add p) (λ i, add_tr_v1 (v i)), λ t u, (add_tr_v1 t : term (L₁ + L₂)) ≃ add_tr_v1 u⟩


instance {n} : has_coe (L₁.fn n) ((L₁ + L₂).fn n) := ⟨fn_to_add⟩

instance {n} : has_coe (L₁.pr n) ((L₁ + L₂).pr n) := ⟨pr_to_add⟩

instance : has_coe (term L₁) (term (L₁ + L₂)) := ⟨add_tr_v1⟩

instance : has_coe (formula L₁) (formula (L₁ + L₂)) := ⟨translation.tr⟩

instance : has_coe (theory L₁) (theory (L₁ + L₂)) := ⟨theory_tr (L₁ + L₂)⟩

instance [has_zero_symbol L₁] : has_zero_symbol (L₁ + L₂) := ⟨fn_to_add has_zero_symbol.zero⟩

instance [has_succ_symbol L₁] : has_succ_symbol (L₁ + L₂) := ⟨fn_to_add has_succ_symbol.succ⟩

instance [has_add_symbol L₁] : has_add_symbol (L₁ + L₂) := ⟨fn_to_add has_add_symbol.add⟩

instance [has_mul_symbol L₁] : has_mul_symbol (L₁ + L₂) := ⟨fn_to_add has_mul_symbol.mul⟩

instance [has_le_symbol L₁] : has_le_symbol (L₁ + L₂) := ⟨pr_to_add has_le_symbol.le⟩

instance [has_mem_symbol L₁] : has_mem_symbol (L₁ + L₂) := ⟨pr_to_add has_mem_symbol.mem⟩

@[simp] lemma add_tr_v1_var (n) : ((#n : term L₁) : term (L₁ + L₂)) = #n := rfl

lemma add_tr_v1_app {n} (f : L₁.fn n) (v : finitary (term L₁) n) :
  ((❨f❩ v : term L₁) : term (L₁ + L₂)) = ❨fn_to_add f❩ (λ i, add_tr_v1 (v i)) := by unfold_coes; simp

@[simp] lemma add_tr_v1_zero [has_zero_symbol L₁] :
  ((0 : term L₁) : term (L₁ + L₂)) = 0 := by { unfold has_zero.zero, unfold_coes, simp, refl }

@[simp] lemma add_tr_v1_succ [has_succ_symbol L₁] (t : term L₁) :
  ((Succ t : term L₁) : term (L₁ + L₂)) = Succ t :=
by { unfold has_succ.succ, unfold_coes, simp, split, { refl }, { ext; simp } }

@[simp] lemma add_tr_v1_numeral [has_zero_symbol L₁] [has_succ_symbol L₁] (n : ℕ) :
  ((n˙ : term L₁) : term (L₁ + L₂)) = n˙ :=
by induction n; simp[*, numeral]

@[simp] lemma add_tr_v1_add [has_add_symbol L₁] (t u : term L₁) :
  ((t + u : term L₁) : term (L₁ + L₂)) = t + u :=
by { unfold has_add.add, unfold_coes, simp, split, { refl }, { ext; simp } }

@[simp] lemma add_tr_v1_mul [has_mul_symbol L₁] (t u : term L₁) :
  ((t * u : term L₁) : term (L₁ + L₂)) = t * u :=
by { unfold has_mul.mul, unfold_coes, simp, split, { refl }, { ext; simp } }

@[simp] lemma add_tr_v1_le [has_le_symbol L₁] (t u : term L₁) :
  ((t ≼ u : formula L₁) : formula (L₁ + L₂)) = ((t : term (L₁ + L₂)) ≼ u) :=
by { unfold has_preceq.preceq, unfold_coes, simp[translation.tr_pr], split,
     { refl }, { ext; simp } }

@[simp] lemma add_tr_v1_mem [has_mem_symbol L₁] (t u : term L₁) :
  ((t ∊ u : formula L₁) : formula (L₁ + L₂)) = ((t : term (L₁ + L₂)) ∊ u) :=
by { unfold has_elem.elem, unfold_coes, simp[translation.tr_pr], split,
     { refl }, { ext; simp } }

@[simp] lemma fn_imply {i} (f : L₁.fn i) (v : finitary (term L₁) i)  :
  (↑(term.app f v : term L₁) : term (L₁ + L₂)) = term.app (f : (L₁ + L₂).fn i) (λ i, v i) := rfl

@[simp] lemma pr_imply {i} (p : L₁.pr i) (v : finitary (term L₁) i)  :
  (↑(formula.app p v : formula L₁) : formula (L₁ + L₂)) = formula.app (p : (L₁ + L₂).pr i) (λ i, v i) := rfl

@[simp] lemma eq_imply (t u : term L₁)  :
  (↑(t ≃ u : formula L₁) : formula (L₁ + L₂)) = ((↑t : term (L₁ + L₂)) ≃ ↑u) := rfl

@[simp] lemma add_imply (p q : formula L₁)  :
  (↑(p ⟶ q) : formula (L₁ + L₂)) = (↑p ⟶ ↑q) := rfl

@[simp] lemma add_and (p q : formula L₁)  :
  (↑(p ⊓ q) : formula (L₁ + L₂)) = (↑p ⊓ ↑q) := rfl

@[simp] lemma add_or (p q : formula L₁)  :
  (↑(p ⊔ q) : formula (L₁ + L₂)) = (↑p ⊔ ↑q) := rfl

@[simp] lemma neg_imply (p : formula L₁)  :
  (↑(⁻p) : formula (L₁ + L₂)) = ⁻(↑p) := rfl

@[simp] lemma add_fal (p : formula L₁)  :
  (↑(∏ p : formula L₁) : formula (L₁ + L₂)) = ∏ (↑p : formula (L₁ + L₂)) := rfl

@[simp] lemma add_ex (p : formula L₁)  :
  (↑(∐ p : formula L₁) : formula (L₁ + L₂)) = ∐ (↑p : formula (L₁ + L₂)) := rfl

@[simp] lemma add_top :
  (↑(⊤ : formula L₁) : formula (L₁ + L₂)) = ⊤ := by unfold has_top.top; simp[formula.top]

@[simp] lemma add_bot :
  (↑(⊥ : formula L₁) : formula (L₁ + L₂)) = ⊥ := by unfold has_bot.bot; simp[formula.bot]

@[simp] lemma add_conjunction (P : list (formula L₁)) :
  (↑(conjunction P) : formula (L₁ + L₂)) = conjunction (P.map coe) :=
by induction P with p P IH; simp[conjunction, *]

@[simp] lemma add_tr_v1_arity : ∀ t : term L₁, (t : term (L₁ + L₂)).arity = t.arity
| (#x)    := rfl
| (❨f❩ v) := by simp[add_tr_v1_app, show ∀ i, (add_tr_v1 (v i)).arity = (v i).arity, from λ i, (add_tr_v1_arity (v i))]

@[simp] lemma add_open (p : formula L₁) : (p : formula (L₁ + L₂)).is_open ↔ p.is_open :=
by unfold_coes; induction p; simp[translation.tr_pr, translation.tr_eq, *]

@[simp] lemma function_coe_inj {n} {f g : L₁.fn n} : (f : (L₁ + L₂).fn n) = g ↔ f = g :=
sum.inl.inj_iff

@[simp] lemma predicate_coe_inj {n} {r s : L₁.pr n} : (r : (L₁ + L₂).pr n) = s ↔ r = s :=
sum.inl.inj_iff

@[simp] lemma term_coe_inj : ∀ {t u : term L₁}, (t : term (L₁ + L₂)) = u ↔ t = u
| (#m)                   (#n)                   := by simp
| (#m)                   (term.app f v)         := by simp
| (term.app f v)         (#n)                   := by simp
| (@term.app _ n₁ f₁ v₁) (@term.app _ n₂ f₂ v₂) := by { 
    simp, rintros rfl,
    simp[fn_to_add, sum.inl.inj_iff],
    rintros rfl, 
    have IH : ∀ i, ↑(v₁ i) = ↑(v₂ i) ↔ v₁ i = v₂ i, from λ i, @term_coe_inj (v₁ i) (v₂ i),
    refine ⟨λ h, funext (λ i, (IH i).mp (congr_fun h i)), by { rintros rfl, refl }⟩ }

@[simp] lemma formula_coe_inj : ∀ {p q : formula L₁}, (p : formula (L₁ + L₂)) = q ↔ p = q
| (@formula.app _ n₁ r₁ v₁) (@formula.app _ n₂ r₂ v₂) :=
    by { simp,  rintros rfl, simp, rintros rfl,
         refine ⟨λ h, funext (λ i, term_coe_inj.mp (congr_fun h i)), by { rintros rfl, refl }⟩ }
| (formula.app r₁ v₁)       ((t : term L₁) ≃ u)       := by simp
| (formula.app r₁ v₁)       (p ⟶ q)                   := by simp
| (formula.app r₁ v₁)       ⁻p                        := by simp
| (formula.app r₁ v₁)       (∏ (p : formula L₁))      := by simp
| ((t : term L₁) ≃ u)       p                         := by cases p; simp
| (p ⟶ q)                   r                         := by cases r; simp[@formula_coe_inj p, @formula_coe_inj q]
| (⁻p)                      q                         := by cases q; simp[@formula_coe_inj p]
| (∏ (p : formula L₁))      q                         := by cases q; simp[@formula_coe_inj p]

@[simp] lemma coe_mem_coe_iff {T : theory L₁} {p} : ↑p ∈ (↑T : theory (L₁ + L₂)) ↔ p ∈ T := 
⟨λ ⟨p', h, eqn⟩, by { simp [formula_coe_inj.mp eqn] at h, exact h }, λ h, ⟨p, h, rfl⟩⟩

lemma mem_coe_iff {T : theory L₁} {p : formula (L₁ + L₂)} :
  p ∈ (↑T : theory (L₁ + L₂)) ↔ ∃ p₁ ∈ T, p = ↑p₁ := 
⟨λ ⟨p₁, h, eqn⟩, ⟨p₁, h, eq.symm eqn⟩, by { rintros ⟨p₁, mem, rfl⟩, simp[mem] }⟩

@[simp] def add_term_retract : term (L₁ + L₂) → option (term L₁)
| (#n)                     := some (#n)
| (term.app (sum.inl f) v) := (finitary.of_option (λ i, add_term_retract (v i))).map (λ v, term.app f v)
| (term.app (sum.inr f) v) := none

lemma term_coe_rew_var : ∀ (t : term L₁) (s : ℕ → ℕ),
  (↑t : term (L₁ + L₂)).rew (λ x, #(s x)) = ↑(t.rew (λ x, #(s x)))
| (#n) s := by simp
| (@term.app _ n f v) s := by { simp, funext i, simp[@term_coe_rew_var (v i)] }

lemma formula_coe_rew_var : ∀ (p : formula L₁) (s : ℕ → ℕ),
  (↑p : formula (L₁ + L₂)).rew (λ x, #(s x)) = ↑(p.rew (λ x, #(s x)))
| (@formula.app _ n r v) s := by { simp, funext i, simp[term_coe_rew_var] }
| ((t : term L₁) ≃ u)    s := by simp[term_coe_rew_var]
| (p ⟶ q)                s := by simp[formula_coe_rew_var p, formula_coe_rew_var q]
| (⁻p)                   s := by simp[formula_coe_rew_var p]
| (∏ (p : formula L₁))   s := by { 
    have eqn₁ : ((λ x, #(s x))^1 : ℕ → term L₁) = (λ x, #(if x = 0 then 0 else s (x - 1) + 1)),
    { funext x, cases x; simp },
    have eqn₂ : ((λ x, #(s x))^1 : ℕ → term (L₁ + L₂)) = (λ x, #(if x = 0 then 0 else s (x - 1) + 1)),
    { funext x, cases x; simp },
    simp[fal_pow, eqn₁, eqn₂, formula_coe_rew_var p] }

@[simp] lemma term_coe_pow (t : term L₁) (k : ℕ) : (↑t : term (L₁ + L₂))^k = ↑(t^k) :=
by simp[has_pow.pow, term_coe_rew_var]

@[simp] lemma formula_coe_pow (p : formula L₁) (k : ℕ) : (↑p : formula (L₁ + L₂))^k = ↑(p^k) :=
by simp[has_pow.pow, formula_coe_rew_var]

@[simp] def add_retract : formula (L₁ + L₂) → formula L₁
| (formula.app (sum.inl p) v)  :=
    option.cases_on (finitary.of_option (λ i, add_term_retract (v i))) ⊤ (λ v, formula.app p v)
| (formula.app (sum.inr p) v)  := ⊤
| ((t : term (L₁ + L₂)) ≃ u)   :=
    option.cases_on
      ((≃) <$> add_term_retract t <*> add_term_retract u : option (formula L₁)) ⊤ (λ p : formula L₁, p)
| (p ⟶ q)                     := add_retract p ⟶ add_retract q
| (⁻p)                        := ⁻add_retract p
| (∏ (p : formula (L₁ + L₂))) := ∏ add_retract p

@[simp] lemma add_retract_app_left {n} (p : L₁.pr n) (v : finitary (term (L₁ + L₂)) n) :
  add_retract (formula.app (↑p) v) =
  option.cases_on (finitary.of_option (λ i, add_term_retract (v i))) ⊤ (λ v, formula.app p v) := rfl

lemma add_retract_fal_eq (p : formula (L₁ + L₂)) :
  add_retract (∏ p : formula (L₁ + L₂)) = ∏ add_retract p := rfl

@[simp] lemma add_term_retract_coe_eq : ∀ (t : term L₁), add_term_retract (t : term (L₁ + L₂)) = some t
| (#n)           := by simp
| (term.app f v) := by { simp,
    have IH : (λ i, add_term_retract (add_tr_v1 (v i))) = (λ i, some (v i)),
      from funext (λ i, add_term_retract_coe_eq (v i)),
    unfold_coes, simp[fn_to_add], rw IH, simp }
/-
@[simp] lemma add_term_retract_coe_eq : ∀ (t : term (L₁ + L₂)) (s : ℕ → term L₁),
  add_term_retract (t.rew (λ x, s x)) = (add_term_retract t).map (λ p, p.rew s)
| (#n)           s := by simp
| (@term.app (L₁ + L₂) n (sum.inl f) v) s := by { simp,
    have IH := λ i, add_term_retract_coe_eq (v i),
    unfold_coes, simp[fn_to_add], rw IH, simp }
-/

@[simp] lemma add_retract_coe_eq : ∀ (p : formula L₁), add_retract (p : formula (L₁ + L₂)) = p
| (@formula.app _ n p v) := by { simp, 
    have : (λ i, add_term_retract (v i : term (L₁ + L₂))) = (λ i, some (v i)),
    { funext i, simp },
    rw [this, show finitary.of_option (λ (i : fin n), some (v i)) = some v, from finitary.of_option_some _] }
| ((t : term L₁) ≃ u)  := by { simp,
    rw [add_term_retract_coe_eq, add_term_retract_coe_eq,
        show has_eq.eq <$> some t <*> some u = some (t ≃ u), from rfl] }
| (p ⟶ q)                := by simp[add_retract_coe_eq p, add_retract_coe_eq q]
| (⁻p)                   := by simp[add_retract_coe_eq p]
| (∏ (p : formula L₁))   := by simp[add_retract_coe_eq p]

end

/-
| q1 : ∀ {T p t}, provable T (∏₁ p ⟶ p.rew ι[0 ⇝ t])
| q2 : ∀ {T p q}, provable T (∏₁ (p ⟶ q) ⟶ ∏₁ p ⟶ ∏₁ q)
| q3 : ∀ {T p}, provable T (p ⟶ ∏₁ (p^1))
| e1 : ∀ {T}, provable T ∏₁ (#0 ≃₁ #0)
| e2 : ∀ {T}, provable T ∏₁ ∏₁ ((#0 ≃₁ #1) ⟶ (#1 ≃₁ #0))
| e3 : ∀ {T}, provable T ∏₁ ∏₁ ∏₁ ((#0 ≃₁ #1) ⟶ (#1 ≃₁ #2) ⟶ (#0 ≃₁ #2))
| e4 : ∀ {T n} {f : L.fn n}, provable T (eq_axiom4 f)
| e5 : ∀ {T n} {r : L.pr n}, provable T (eq_axiom5 r)

-/

variables (L₁ : language.{u}) (L₂ : language.{u})



local infix ` ≃₁ `:50 := ((≃) : term L₁ → term L₁ → formula L₁)
local infix ` ≃₂ `:50 := ((≃) : term L₂ → term L₂ → formula L₂)

class conservative_translation extends translation L₁ L₂ :=
(pow_eq : ∀ (p : formula L₁) (k : ℕ), (tr[p]^k : formula L₂) = tr[p^k])
(specialize : ∀ {p : formula L₁} {t : term L₁} {T : theory L₂}, T ⊢ tr[∏ p ⟶ p.rew ι[0 ⇝ t]])
(eq_reflexivity : ∀ {T : theory L₂}, T ⊢ tr[∏ (#0 ≃₁ #0)] )
(eq_symmetry : ∀ {T : theory L₂}, T ⊢ tr[∏ ∏ ((#0 ≃₁ #1) ⟶ (#1 ≃₁ #0))])
(eq_transitive : ∀ {T : theory L₂}, T ⊢ tr[∏ ∏ ∏ ((#0 ≃₁ #1) ⟶ (#1 ≃₁ #2) ⟶ (#0 ≃₁ #2))])
(function_ext : ∀ {n} {f : L₁.fn n} {T : theory L₂}, T ⊢ tr[eq_axiom4 f])
(predicate_ext : ∀ {n} {r : L₁.pr n} {T : theory L₂}, T ⊢ tr[eq_axiom5 r])

namespace translation
variables {L₁} {L₂} [translation L₁ L₂]

noncomputable def inv : translation L₂ L₁ :=
{ tr_pr := λ n p v, (function.partial_inv translation.tr (formula.app p v)).get_or_else ⊤,
  tr_eq := λ t u, (function.partial_inv translation.tr (t ≃₂ u)).get_or_else ⊤ }

lemma inv_reduce (I : function.injective (tr : formula L₁ → formula L₂)) :
  ∀ (p : formula L₂), (tr[(inv p : formula L₁)] : formula L₂) = p := λ p₂,
begin
  induction p₂,
  case app : n p v { simp[app_translation, tr, tr_pr], exact classical.some_spec },
  case equal : t u { simp, intros p₁ eqn, simp[tr, tr_eq], simp[←eqn, function.partial_inv_left I] },
  case imply : p q IHpq IHp { simp, intros r₁ eqn, cases r₁; simp[tr_eq] at eqn, } 
end

lemma inv_reduce :
  ∀ (p₂ : formula L₂), (∃ p₁ : formula L₁, tr[p₁] = p₂) → (tr[(inv p₂ : formula L₁)] : formula L₂) = p₂ :=
begin
  intros p₂, induction p₂,
  case app : n p v { intros h, simp[app_translation, tr, tr_pr, function.partial_inv, h],
  have := (classical.some_spec h),
  exact cast (by { congr, simp[tr_pr] }) this,
  sorry  },
  case equal : t u { intros h, simp at h, simp[app_translation, tr, tr_eq, function.partial_inv, h],
   sorry },
  case imply : p q IHpq IHp { simp[app_translation],   } 
end



lemma inv_reduce (I : function.injective (tr : formula L₁ → formula L₂)) :
  ∀ (p : formula L₁), (inv (tr[p] : formula L₂) : formula L₁) = p :=
begin
  suffices : ∀ (q : formula L₂) (p : formula L₁), tr[p] = q → tr[q] = p,
  { intros p, exact this tr[p] p rfl },
  intros q, induction q,
  case app : n p v { intros p₁ eqn, simp[tr, tr_pr], simp[←eqn, function.partial_inv_left I] },
  case equal : t u { simp, intros p₁ eqn, simp[tr, tr_eq], simp[←eqn, function.partial_inv_left I] },
  case imply : p q IHpq IHp { simp, intros r₁ eqn, cases r₁; simp[tr_eq] at eqn, } 
end

end translation

namespace conservative_translation
open provable axiomatic_classical_logic'
variables (L₁) (L₂)

def tr_rew_var_eq_tr [translation L₁ L₂]
  (predicate_eq : ∀ {n} (p : L₁.pr n) (v : finitary (term L₁) n) (s : ℕ → ℕ),
    (tr[formula.app p v] : formula L₂).rew (λ x, #(s x)) = tr[(formula.app p v).rew (λ x, #(s x))])
  (equal_eq : ∀ (t u : term L₁) (s : ℕ → ℕ), 
    (tr[(t ≃ u : formula L₁)] : formula L₂).rew (λ x, #(s x)) = tr[(t ≃ u : formula L₁).rew (λ x, #(s x))]) :
  ∀ (p : formula L₁) (s : ℕ → ℕ),
  (tr[p] : formula L₂).rew (λ x, #(s x)) = tr[p.rew (λ x, #(s x))]
| (formula.app p v) s   := predicate_eq p v s
| ((t : term L₁) ≃ u) s := equal_eq t u s
| (p ⟶ q) s             := by simp[tr_rew_var_eq_tr p, tr_rew_var_eq_tr q]
| (⁻p) s                := by simp[tr_rew_var_eq_tr p]
| (∏ p) s               := by { 
    have eqn₁ : ((λ x, #(s x))^1 : ℕ → term L₂) = (λ x, #(if x = 0 then 0 else s (x - 1) + 1)),
    { funext x, cases x; simp },
    have eqn₂ : ((λ x, #(s x))^1 : ℕ → term L₁) = (λ x, #(if x = 0 then 0 else s (x - 1) + 1)),
    { funext x, cases x; simp },
    simp [eqn₁, eqn₂, tr_rew_var_eq_tr p] }

variables [conservative_translation L₁ L₂]

@[simp] lemma mem_pow_theory_tr_of_mem_pow {T : theory L₁} {p} {i : ℕ} (mem : p ∈ T^i) :
  tr[p] ∈ (Tr[T] : theory L₂)^i :=
by { simp[theory_sf_itr_eq] at mem ⊢, rcases mem with ⟨q, mem, rfl⟩, 
  refine ⟨q, mem, by simp[pow_eq]⟩ }

lemma provability (T : theory L₁) (p : formula L₁) (i : ℕ) :
  T^i ⊢ p → (Tr[T] : theory L₂)^i ⊢ tr[p] :=
begin
  refine provable.rec' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  { intros i p _ h, simp at h ⊢, 
    exact generalize h },
  { intros i p q _ _ hpq hp, simp at hpq,
    exact hpq ⨀ hp },
  { intros i p mem, refine by_axiom (by simp[mem]) },
  { intros, simp },
  { intros, simp },
  { intros, simp },
  { intros, exact specialize },
  { intros, simp },
  { intros, simp[←pow_eq] },
  { intros, exact eq_reflexivity },
  { intros, exact eq_symmetry },
  { intros, exact eq_transitive },
  { intros, exact function_ext },
  { intros, exact predicate_ext },
end

lemma provability' (T : theory L₁) (p : formula L₁) (i : ℕ) :
  T ⊢ p → (Tr[T] : theory L₂) ⊢ tr[p] :=
by { have := provability L₁ L₂ T p 0, simp at this, exact this }

noncomputable def inv : conservative_translation L₂ L₁ :=
{ tr_pr := λ n p v, (function.partial_inv translation.tr (formula.app p v)).get_or_else ⊤,
  tr_eq := λ t u, (function.partial_inv translation.tr (t ≃₂ u)).get_or_else ⊤,
  pow_eq := λ p k, by {  } }



end conservative_translation

instance : conservative_translation L₁ (L₁ + L₂) :=
{ pow_eq := λ p k, by { exact formula_coe_pow _ _ },
  specialize := λ p t T, by { simp, sorry },
  eq_reflexivity := λ T, by { show T ⊢ (∏ (#0 ≃ #0)), simp },
  eq_symmetry := λ T, by { show T ⊢ ∏ ∏ ((#0 ≃ #1) ⟶ (#1 ≃ #0)), simp },
  eq_transitive := λ T, by { show T ⊢ ∏ ∏ ∏ ((#0 ≃ #1) ⟶ (#1 ≃ #2) ⟶ (#0 ≃ #2)), simp },
  function_ext := λ n f T, by { simp[eq_axiom4], }
   }


namespace translation
variables {L₁ L₂ : language.{u}} 

class retract (L₁ : language.{u}) (L₂ : language.{u}) :=
(trans : translation L₁ L₂)
(trans_inv : translation L₂ L₁)
(left_inv : ∀ p : formula L₁, tr[(tr[p] : formula L₂)] = p)


end translation

end language


end fopl
