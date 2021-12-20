import deduction

universes u v

namespace fopl
open formula term

namespace language

structure translation (L₁ : language.{u}) (L₂ : language.{u}) :=
(to_fun : formula L₁ → formula L₂)
(map_imply : ∀ (p q : formula L₁), to_fun (p ⟶ q) = to_fun p ⟶ to_fun q)
(map_neg : ∀ (p : formula L₁), to_fun (⁻p) = ⁻to_fun p)
(map_univ : ∀ (p : formula L₁), to_fun (∏ p) = ∏ to_fun p)
(map_pow : ∀ (p : formula L₁) (k : ℕ), to_fun (p^k) = (to_fun p)^k)

instance {L₁ L₂ : language.{u}} : has_coe_to_fun (translation L₁ L₂) (λ _, formula L₁ → formula L₂) :=
⟨@translation.to_fun L₁ L₂⟩

namespace translation
variables {L₁ L₂ L₃ : language.{u}} 

@[simp] lemma app_eq (to_fun) (map_imply) (map_neg) (map_univ) (map_pow) (p : formula L₁) :
  ({to_fun := to_fun, map_imply := map_imply, map_neg := map_neg,
     map_univ := map_univ, map_pow := map_pow} : translation L₁ L₂) p = to_fun p := rfl

@[simp] def fun_of_atom {L₁ L₂ : language.{u}}
  (tr_pr : Π {n}, L₁.pr n → finitary (term L₁) n → formula L₂)
  (tr_eq : term L₁ → term L₁ → formula L₂) : formula L₁ → formula L₂
| (app p v)            := tr_pr p v
| ((t : term L₁) ≃ u)  := tr_eq t u
| (p ⟶ q)              := fun_of_atom p ⟶ fun_of_atom q
| (⁻p)                 := ⁻fun_of_atom p
| (∏ (p : formula L₁)) := ∏ fun_of_atom p

lemma mk_of_atom_map_map_pow {L₁ L₂ : language.{u}}
  (tr_pr : Π {n}, L₁.pr n → finitary (term L₁) n → formula L₂)
  (tr_eq : term L₁ → term L₁ → formula L₂)
  (map_rew_var_pr : ∀ {n} (p : L₁.pr n) (v : finitary (term L₁) n) (s : ℕ → ℕ),
    tr_pr p (λ i, (v i).rew (λ x, #(s x))) = (tr_pr p v).rew (λ x, #(s x)))
  (map_rew_var_eq : ∀ (t u : term L₁) (s : ℕ → ℕ),
    tr_eq (t.rew (λ x, #(s x))) (u.rew (λ x, #(s x))) = (tr_eq t u).rew (λ x, #(s x))) :
  ∀ (p : formula L₁) (s : ℕ → ℕ),
    fun_of_atom @tr_pr tr_eq (p.rew (λ x, #(s x))) = (fun_of_atom @tr_pr tr_eq p).rew (λ x, #(s x))
| (formula.app p v) s := by { simp, exact map_rew_var_pr p v s }
| ((t : term L₁) ≃ u) s := by { simp, exact map_rew_var_eq t u s }
| (p ⟶ q) s := by simp[mk_of_atom_map_map_pow p, mk_of_atom_map_map_pow q]
| (⁻p) s := by simp[mk_of_atom_map_map_pow p]
| (∏ p) s := by { simp,
    have : ((λ x, #(s x))^1 : ℕ → term L₁) = (λ x, #(if x = 0 then 0 else s (x - 1) + 1)),
    { funext x, cases x; simp },
    have : ((λ x, #(s x))^1 : ℕ → term L₂) = (λ x, #(if x = 0 then 0 else s (x - 1) + 1)),
    { funext x, cases x; simp }, simp* }

def mk_of_atom {L₁ L₂ : language.{u}}
  (tr_pr : Π {n}, L₁.pr n → finitary (term L₁) n → formula L₂)
  (tr_eq : term L₁ → term L₁ → formula L₂)
  (map_rew_var_pr : ∀ {n} (p : L₁.pr n) (v : finitary (term L₁) n) (s : ℕ → ℕ),
    tr_pr p (λ i, (v i).rew (λ x, #(s x))) = (tr_pr p v).rew (λ x, #(s x)))
  (map_rew_var_eq : ∀ (t u : term L₁) (s : ℕ → ℕ),
    tr_eq (t.rew (λ x, #(s x))) (u.rew (λ x, #(s x))) = (tr_eq t u).rew (λ x, #(s x))) :
  translation L₁ L₂ :=
{ to_fun := translation.fun_of_atom @tr_pr @tr_eq,
  map_imply := by simp,
  map_neg := by simp,
  map_univ := by simp,
  map_pow := λ p k, 
    mk_of_atom_map_map_pow @tr_pr @tr_eq @map_rew_var_pr @map_rew_var_eq p _ }

def mk_of_atom' {L₁ L₂ : language.{u}}
  (tr_pr : Π {n}, L₁.pr n → finitary (term L₁) n → formula L₂)
  (tr_eq : term L₁ → term L₁ → formula L₂)
  (map_pow : ∀ (p : formula L₁) (k : ℕ), fun_of_atom @tr_pr @tr_eq (p ^ k) = fun_of_atom @tr_pr @tr_eq p ^ k) :
  translation L₁ L₂ :=
{ to_fun := translation.fun_of_atom @tr_pr @tr_eq,
  map_imply := by simp,
  map_neg := by simp,
  map_univ := by simp,
  map_pow := map_pow }

@[simp] lemma app_translation_pr {L₁ L₂ : language.{u}}
  (tr_pr) (tr_eq) (map_rew_var_pr) (map_rew_var_eq) {n} (p : L₁.pr n) (v) :
  (@translation.mk_of_atom L₁ L₂ tr_pr tr_eq map_rew_var_pr map_rew_var_eq) (formula.app p v) = tr_pr p v := rfl

@[simp] lemma app_translation_eq {L₁ L₂ : language.{u}}
  (tr_pr) (tr_eq) (map_rew_var_pr) (map_rew_var_eq) (t u : term L₁) :
  (@translation.mk_of_atom L₁ L₂ tr_pr tr_eq map_rew_var_pr map_rew_var_eq) (t ≃ u) = tr_eq t u := rfl

variables (τ : translation L₁ L₂)

@[simp] lemma map_imply' (p q : formula L₁) :
  τ (p ⟶ q) = τ p ⟶ τ q := τ.map_imply p q

@[simp] lemma map_neg' (p : formula L₁) :
  τ (⁻p) = ⁻τ p := τ.map_neg p

@[simp] lemma map_univ' (p : formula L₁) :
  τ (∏ p) = ∏ τ p := τ.map_univ p

lemma map_pow' (p : formula L₁) (k : ℕ) :
  τ (p^k) = (τ p)^k := τ.map_pow p k

@[simp] lemma map_ex' (p : formula L₁) :
  τ (∐ p) = ∐ (τ p) := by { unfold has_exists_quantifier.ex formula.ex, simp }

@[simp] lemma map_and' (p q : formula L₁) :
  τ (p ⊓ q) = τ p ⊓ τ q := by { unfold has_inf.inf formula.and, simp }

@[simp] lemma map_or' (p q : formula L₁) :
  τ (p ⊔ q) = τ p ⊔ τ q := by { unfold has_sup.sup formula.or, simp }

@[simp] lemma map_equiv' (p q : formula L₁) :
  τ (p ⟷ q) = τ p ⟷ τ q := by simp[lrarrow_def]

variables (L₁) (L₂) (L₃)

def refl : translation L₁ L₁ :=
{ to_fun := id, map_imply := by simp, map_neg := by simp, map_univ := by simp, map_pow := by simp }

variables {L₁} {L₂} {L₃}

def transitive : translation L₁ L₂ → translation L₂ L₃ → translation L₁ L₃ := λ τ₁₂ τ₂₃,
{ to_fun := τ₂₃ ∘ τ₁₂, map_imply := by simp, map_neg := by simp,
  map_univ := by simp, map_pow := by simp[map_pow'] }

end translation

def tr_theory {L₁ L₂ : language} (τ : translation L₁ L₂) (T : theory L₁) : theory L₂ := τ '' T

@[simp] lemma mem_theory_tr_of_mem {L₁ L₂ : language} {τ : translation L₁ L₂}
  {T : theory L₁} {p} (mem : p ∈ T) : τ p ∈ tr_theory τ T :=
⟨p, mem, rfl⟩

structure term_translation (L₁ : language.{u}) (L₂ : language.{u}) :=
(to_fun_chr : Π {n}, L₁.fn n → finitary (term L₂) n → term L₂)
(to_fun : term L₁ → term L₂)
(map_fn : Π {n} (f : L₁.fn n) (v : finitary (term L₁) n),
  to_fun (term.app f v) = to_fun_chr f (λ i, to_fun (v i)))

instance {L₁ L₂ : language.{u}} : has_coe_to_fun (term_translation L₁ L₂) (λ _, term L₁ → term L₂) :=
⟨λ τ, τ.to_fun⟩

namespace term_translation
variables {L₁ L₂ : language.{u}}

@[simp] lemma translation.map_imply' (τ : term_translation L₁ L₂) {n} (f : L₁.fn n) (v : finitary (term L₁) n) :
  τ (term.app f v) = τ.to_fun_chr f (λ i, τ (v i)) := τ.map_fn _ _

@[simp] lemma app_eq (fc) (f) (map_fn) (t : term L₁) :
  ({to_fun_chr := fc, to_fun := f, map_fn := map_fn} : term_translation L₁ L₂) t = f t := rfl

@[simp] def mk_fun_of_atom {L₁ L₂ : language.{u}} 
  (to_fun_chr : Π {n}, L₁.fn n → finitary (term L₂) n → term L₂) : term L₁ → term L₂
| #n        := #n
| (app f v) := to_fun_chr f (λ i, mk_fun_of_atom (v i))

@[simp] def mk_of_atom {L₁ L₂ : language.{u}}
  (to_fun_chr : Π {n}, L₁.fn n → finitary (term L₂) n → term L₂) : term_translation L₁ L₂ :=
{ to_fun_chr := @to_fun_chr,
  to_fun := mk_fun_of_atom @to_fun_chr,
  map_fn := by simp }

end term_translation

structure term_formula_translation (L₁ : language.{u}) (L₂ : language.{u}) :=
(formula_tr : translation L₁ L₂)
(term_tr : term_translation L₁ L₂)
(consistence : ∀ (t u : term L₁),
  formula_tr (t ≃ u : formula L₁) = (term_tr t ≃ term_tr u))

namespace term_formula_translation
variables {L₁ L₂ : language.{u}}

@[simp] def mk_of_term_tr (τ : term_translation L₁ L₂)
  (tr_pr' : Π {n}, L₁.pr n → finitary (term L₂) n → formula L₂)
  (map_pr' : ∀ {n} (p : L₁.pr n) (v : finitary (term L₁) n) (s : ℕ → ℕ),
    tr_pr' p (λ i, τ ((v i).rew (λ x, #(s x)))) =
    (tr_pr' p (λ (i : fin n), τ (v i))).rew (λ x, #(s x)))
  (map_rew_var : ∀ (t : term L₁) (s : ℕ → ℕ),
    τ (t.rew (λ x, #(s x))) = (τ t).rew (λ x, #(s x))) : term_formula_translation L₁ L₂ :=
{ formula_tr := translation.mk_of_atom (λ n p v, tr_pr' p (λ i, τ (v i))) (λ t u, τ t ≃ τ u)
    @map_pr' (by simp*),
  term_tr := τ,
  consistence := by simp }

@[simp] lemma app_pr {L₁ L₂ : language.{u}} (τ : term_translation L₁ L₂)
  (tr_pr') (map_pr') (map_rew_var) {n} (p : L₁.pr n) (v) :
  ((@mk_of_term_tr L₁ L₂ τ tr_pr' map_pr' map_rew_var).formula_tr 
    : translation L₁ L₂) (formula.app p v) = tr_pr' p (λ i, τ (v i)) := rfl

@[simp] lemma app_eq {L₁ L₂ : language.{u}} (τ : term_translation L₁ L₂)
  (tr_pr') (map_pr') (map_rew_var) (t u : term L₁) :
  ((@mk_of_term_tr L₁ L₂ τ tr_pr' map_pr' map_rew_var).formula_tr 
    : translation L₁ L₂) (t ≃ u) = (τ t ≃ τ u) := rfl

end term_formula_translation

instance : has_add language := ⟨λ L₁ L₂ : language.{u}, ⟨λ n, L₁.fn n ⊕ L₂.fn n, λ n, L₁.pr n ⊕ L₂.pr n⟩⟩ 

section 
variables {L₁ L₂ : language.{u}} 

def fn_to_add {n} (f : L₁.fn n) : (L₁ + L₂).fn n := sum.inl f

def pr_to_add {n} (p : L₁.pr n) : (L₁ + L₂).pr n := sum.inl p

@[simp] def add_tr_v1 : term L₁ → term (L₁ + L₂)
| (#x)       := #x
| (app f v)  := app (fn_to_add f) (λ i, add_tr_v1 (v i))

def add_term_translation : term_translation L₁ (L₁ + L₂) :=
{ to_fun_chr := λ n f v, term.app (sum.inl f) v,
  to_fun := add_tr_v1,
  map_fn := λ n f v, by { simp, refl } }

lemma term_coe_rew_var : ∀ (t : term L₁) (s : ℕ → ℕ),
  (add_term_translation t : term (L₁ + L₂)).rew (λ x, #(s x)) = add_term_translation (t.rew (λ x, #(s x)))
| (#n)                s := by simp[add_term_translation]
| (@term.app _ n f v) s := by { simp[add_term_translation], funext i, exact @term_coe_rew_var (v i) _ }

def add_translation : term_formula_translation L₁ (L₁ + L₂) :=
term_formula_translation.mk_of_term_tr add_term_translation (λ n p v, formula.app (pr_to_add p) v)
(λ n p v s, by simp[term_coe_rew_var]) (λ t s, by simp[term_coe_rew_var])

instance {n} : has_coe (L₁.fn n) ((L₁ + L₂).fn n) := ⟨fn_to_add⟩

instance {n} : has_coe (L₁.pr n) ((L₁ + L₂).pr n) := ⟨pr_to_add⟩

instance : has_coe (term L₁) (term (L₁ + L₂)) := ⟨add_term_translation⟩

instance : has_coe (formula L₁) (formula (L₁ + L₂)) := ⟨add_translation.formula_tr⟩

instance : has_coe (theory L₁) (theory (L₁ + L₂)) := ⟨tr_theory add_translation.formula_tr⟩

instance [has_zero_symbol L₁] : has_zero_symbol (L₁ + L₂) := ⟨fn_to_add has_zero_symbol.zero⟩

instance [has_succ_symbol L₁] : has_succ_symbol (L₁ + L₂) := ⟨fn_to_add has_succ_symbol.succ⟩

instance [has_add_symbol L₁] : has_add_symbol (L₁ + L₂) := ⟨fn_to_add has_add_symbol.add⟩

instance [has_mul_symbol L₁] : has_mul_symbol (L₁ + L₂) := ⟨fn_to_add has_mul_symbol.mul⟩

instance [has_le_symbol L₁] : has_le_symbol (L₁ + L₂) := ⟨pr_to_add has_le_symbol.le⟩

instance [has_mem_symbol L₁] : has_mem_symbol (L₁ + L₂) := ⟨pr_to_add has_mem_symbol.mem⟩

lemma add_formula_coe_eq (p : formula L₁) : (p : formula (L₁ + L₂)) =
(add_translation.formula_tr : translation L₁ (L₁ + L₂)) p := rfl

lemma add_term_coe_eq (t : term L₁) : (t : term (L₁ + L₂)) =
(add_translation.term_tr : term_translation L₁ (L₁ + L₂)) t := rfl

@[simp] lemma add_tr_v1_var (n) : ((#n : term L₁) : term (L₁ + L₂)) = #n := rfl

lemma add_tr_v1_app {n} (f : L₁.fn n) (v : finitary (term L₁) n) :
  ((❨f❩ v : term L₁) : term (L₁ + L₂)) = ❨fn_to_add f❩ (λ i, (v i)) := by refl

@[simp] lemma add_tr_v1_zero [has_zero_symbol L₁] :
  ((0 : term L₁) : term (L₁ + L₂)) = 0 := by { unfold has_zero.zero,
   simp [ add_term_coe_eq, add_term_translation, add_translation], refl }

@[simp] lemma add_tr_v1_succ [has_succ_symbol L₁] (t : term L₁) :
  ((Succ t : term L₁) : term (L₁ + L₂)) = Succ t :=
by { unfold has_succ.succ, simp [add_term_coe_eq, add_term_translation, add_translation],
     split, { refl }, { ext; simp } }

@[simp] lemma add_tr_v1_numeral [has_zero_symbol L₁] [has_succ_symbol L₁] (n : ℕ) :
  ((n˙ : term L₁) : term (L₁ + L₂)) = n˙ :=
by induction n; simp[*, numeral]

@[simp] lemma add_tr_v1_add [has_add_symbol L₁] (t u : term L₁) :
  ((t + u : term L₁) : term (L₁ + L₂)) = t + u :=
by { unfold has_add.add, simp [add_term_coe_eq, add_term_translation, add_translation],
     split, { refl }, { ext; simp } }

@[simp] lemma add_tr_v1_mul [has_mul_symbol L₁] (t u : term L₁) :
  ((t * u : term L₁) : term (L₁ + L₂)) = t * u :=
by { unfold has_mul.mul, simp [add_term_coe_eq, add_term_translation, add_translation],
     split, { refl }, { ext; simp } }

@[simp] lemma add_tr_v1_le [has_le_symbol L₁] (t u : term L₁) :
  ((t ≼ u : formula L₁) : formula (L₁ + L₂)) = ((t : term (L₁ + L₂)) ≼ u) :=
by { unfold has_preceq.preceq, simp [add_formula_coe_eq, add_term_translation, add_translation], split,
     { refl }, { ext; simp; refl } }

@[simp] lemma add_tr_v1_mem [has_mem_symbol L₁] (t u : term L₁) :
  ((t ∊ u : formula L₁) : formula (L₁ + L₂)) = ((t : term (L₁ + L₂)) ∊ u) :=
by { unfold has_elem.elem, simp [add_formula_coe_eq, add_term_translation, add_translation],
     split, { refl }, { ext; simp; refl } }

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
| (❨f❩ v) := by simp[λ i, add_tr_v1_arity (v i)]

@[simp] lemma add_open (p : formula L₁) : (p : formula (L₁ + L₂)).is_open ↔ p.is_open :=
by { induction p; simp[*] }

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

end

variables (L₁ L₂ L₃ : language.{u})
local infix ` ≃₁ `:50 := ((≃) : term L₁ → term L₁ → formula L₁)
local infix ` ≃₂ `:50 := ((≃) : term L₂ → term L₂ → formula L₂)

structure conservative_translation extends translation L₁ L₂ :=
(specialize : ∀ (p : formula L₁) (t : term L₁) (T : theory L₂), T ⊢ to_fun (∏ p ⟶ p.rew ι[0 ⇝ t]))
(eq_reflexivity : ∀ (T : theory L₂), T ⊢ to_fun (∏ (#0 ≃₁ #0)) )
(eq_symmetry : ∀ (T : theory L₂), T ⊢ to_fun (∏ ∏ ((#0 ≃₁ #1) ⟶ (#1 ≃₁ #0))))
(eq_transitive : ∀ (T : theory L₂), T ⊢ to_fun (∏ ∏ ∏ ((#0 ≃₁ #1) ⟶ (#1 ≃₁ #2) ⟶ (#0 ≃₁ #2))))
(function_ext : ∀ {n} (f : L₁.fn n) (T : theory L₂), T ⊢ to_fun (eq_axiom4 f))
(predicate_ext : ∀ {n} (r : L₁.pr n) (T : theory L₂), T ⊢ to_fun (eq_axiom5 r))

instance : has_coe (conservative_translation L₁ L₂) (translation L₁ L₂) :=
⟨conservative_translation.to_translation⟩

namespace conservative_translation
open provable axiomatic_classical_logic'

variables {L₁} {L₂}
variables (τ : conservative_translation L₁ L₂)

@[simp] lemma map_imply' (p q : formula L₁) :
  τ (p ⟶ q) = τ p ⟶ τ q := τ.map_imply p q

@[simp] lemma map_neg' (p : formula L₁) :
  τ (⁻p) = ⁻τ p := τ.map_neg p

@[simp] lemma map_univ' (p : formula L₁) :
  τ (∏ p) = ∏ τ p := τ.map_univ p

lemma map_pow' (p : formula L₁) (k : ℕ) :
  τ (p^k) = (τ p)^k := τ.map_pow p k

@[simp] lemma map_ex' (p : formula L₁) :
  τ (∐ p) = ∐ (τ p) := by { unfold has_exists_quantifier.ex formula.ex, simp }

@[simp] lemma map_and' (p q : formula L₁) :
  τ (p ⊓ q) = τ p ⊓ τ q := by { unfold has_inf.inf formula.and, simp }

@[simp] lemma map_or' (p q : formula L₁) :
  τ (p ⊔ q) = τ p ⊔ τ q := by { unfold has_sup.sup formula.or, simp }

@[simp] lemma map_equiv' (p q : formula L₁) :
  τ (p ⟷ q) = τ p ⟷ τ q := by simp[lrarrow_def]

@[simp] lemma mem_pow_theory_tr_of_mem_pow {T : theory L₁} {p} {i : ℕ} (mem : p ∈ T^i) :
  (τ p) ∈ (tr_theory (↑ τ) T : theory L₂)^i :=
by { simp[theory_sf_itr_eq] at mem ⊢, rcases mem with ⟨q, mem, rfl⟩, 
  refine ⟨τ q, mem_theory_tr_of_mem mem, _⟩, simp[map_pow'] }

lemma provability_pow (T : theory L₁) (p : formula L₁) (i : ℕ) :
  T^i ⊢ p → (tr_theory (↑τ) T)^i ⊢ τ p :=
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
  { intros, exact specialize _ _ _ _ },
  { intros, simp },
  { intros, simp[map_pow'] },
  { intros, exact eq_reflexivity _ _ },
  { intros, exact eq_symmetry _ _ },
  { intros, exact eq_transitive _ _ },
  { intros, exact function_ext _ _ _ },
  { intros, exact predicate_ext _ _ _ },
end

lemma provability (T : theory L₁) (p : formula L₁) :
  T ⊢ p → τ '' T ⊢ τ p :=
by { have := provability_pow τ T p 0, simp at this, exact this }

lemma provability_tautology (p : formula L₁) :
  (∀ T, T ⊢ p) → ∀ T, T ⊢ τ p := λ h T,
by { have := provability τ ∅ p (h ∅), simp at this, exact weakening this (by simp) }

def refl : conservative_translation L₁ L₁ :=
{ specialize := by simp[translation.refl],
  eq_reflexivity := by simp[translation.refl],
  eq_symmetry := by simp[translation.refl],
  eq_transitive := by simp[translation.refl],
  function_ext := by simp[translation.refl],
  predicate_ext := by simp[translation.refl],
  ..translation.refl L₁ }

def transitive :
  conservative_translation L₁ L₂ →
  conservative_translation L₂ L₃ →
  conservative_translation L₁ L₃ := λ τ₁₂ τ₂₃,
{ specialize := λ p t T, provability_tautology τ₂₃ _ (τ₁₂.specialize p t) T,
  eq_reflexivity := λ T, provability_tautology τ₂₃ _ (τ₁₂.eq_reflexivity) T,
  eq_symmetry := λ T, provability_tautology τ₂₃ _ (τ₁₂.eq_symmetry) T,
  eq_transitive := λ T, provability_tautology τ₂₃ _ (τ₁₂.eq_transitive) T,
  function_ext := λ n f T, provability_tautology τ₂₃ _ (τ₁₂.function_ext f) T,
  predicate_ext := λ n f T, provability_tautology τ₂₃ _ (τ₁₂.predicate_ext f) T,
  ..translation.transitive (τ₁₂ : translation L₁ L₂) (τ₂₃ : translation L₂ L₃) }

end conservative_translation



namespace translation
variables {L₁} {L₂} (τ : translation L₁ L₂)

noncomputable def inv : translation L₂ L₁ :=
mk_of_atom' (λ n p v, (function.partial_inv τ (formula.app p v)).get_or_else ⊤)
  (λ t u, (function.partial_inv τ (t ≃₂ u)).get_or_else ⊤)
  (λ p k, by {  }) 

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
