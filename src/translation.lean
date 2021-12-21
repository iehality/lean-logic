import deduction

universes u v

namespace fopl
open formula term

namespace language

structure translation (L₁ : language.{u}) (L₂ : language.{u}) :=
(to_fun : ℕ → formula L₁ → formula L₂)
(map_imply : ∀ (p q : formula L₁) (i : ℕ), to_fun i (p ⟶ q) = to_fun i p ⟶ to_fun i q)
(map_neg : ∀ (p : formula L₁) (i), to_fun i (⁻p) = ⁻to_fun i p)
(map_univ : ∀ (p : formula L₁) (i), to_fun i (∏ p) = ∏ to_fun (i + 1) p)
(map_pow : ∀ (p : formula L₁) (i), to_fun (i + 1) (p^1) = (to_fun i p)^1)

instance {L₁ L₂ : language.{u}} : has_coe_to_fun (translation L₁ L₂) (λ _, ℕ → formula L₁ → formula L₂) :=
⟨@translation.to_fun L₁ L₂⟩

namespace translation
variables {L₁ L₂ L₃ : language.{u}} 

@[simp] lemma app_eq (to_fun) (map_imply) (map_neg) (map_univ) (map_pow) (p : formula L₁) (i) :
  ({to_fun := to_fun, map_imply := map_imply, map_neg := map_neg,
     map_univ := map_univ, map_pow := map_pow} : translation L₁ L₂) i p = to_fun i p := rfl

@[simp] def fun_of_atom {L₁ L₂ : language.{u}}
  (tr_pr : ℕ → Π {n}, L₁.pr n → finitary (term L₁) n → formula L₂)
  (tr_eq : ℕ → term L₁ → term L₁ → formula L₂) : ℕ → formula L₁ → formula L₂
| k (app p v)            := tr_pr k p v
| k ((t : term L₁) ≃ u)  := tr_eq k t u
| k (p ⟶ q)              := fun_of_atom k p ⟶ fun_of_atom k q
| k (⁻p)                 := ⁻fun_of_atom k p
| k (∏ (p : formula L₁)) := ∏ fun_of_atom (k + 1) p

def mk_of_atom' {L₁ L₂ : language.{u}}
  (tr_pr : ℕ → Π {n}, L₁.pr n → finitary (term L₁) n → formula L₂)
  (tr_eq : ℕ → term L₁ → term L₁ → formula L₂)
  (map_pow : ∀ (p : formula L₁) (k : ℕ), fun_of_atom @tr_pr @tr_eq (k + 1) (p^1) = (fun_of_atom @tr_pr @tr_eq k p)^1) :
  translation L₁ L₂ :=
{ to_fun := translation.fun_of_atom @tr_pr @tr_eq,
  map_imply := by simp,
  map_neg := by simp,
  map_univ := by simp,
  map_pow := map_pow }

variables (τ : translation L₁ L₂) (i : ℕ)

@[simp] lemma map_imply' (p q : formula L₁) :
  τ i (p ⟶ q) = τ i p ⟶ τ i q := τ.map_imply p q i

@[simp] lemma map_neg' (p : formula L₁) :
  τ i (⁻p) = ⁻τ i p := τ.map_neg p i

@[simp] lemma map_univ' (p : formula L₁) :
  τ i (∏ p) = ∏ τ (i + 1) p := τ.map_univ p i

lemma map_pow' (p : formula L₁) (k : ℕ) :
  τ (i + k) (p^k) = (τ i p)^k := by { induction k with k IH; simp[←nat.add_one, ←add_assoc],
  have : τ (i + k + 1) (p^(k + 1)) = τ (i + k) (p^k)^1, simp[←formula.pow_add], from map_pow τ (p^k) (i + k), 
  simp[IH, formula.pow_add] at this, exact this }

@[simp] lemma map_ex' (p : formula L₁) :
  τ i (∐ p) = ∐ (τ (i + 1) p) := by { unfold has_exists_quantifier.ex formula.ex, simp }

@[simp] lemma map_and' (p q : formula L₁) :
  τ i (p ⊓ q) = τ i p ⊓ τ i q := by { unfold has_inf.inf formula.and, simp }

@[simp] lemma map_or' (p q : formula L₁) :
  τ i (p ⊔ q) = τ i p ⊔ τ i q := by { unfold has_sup.sup formula.or, simp }

@[simp] lemma map_equiv' (p q : formula L₁) :
  τ i (p ⟷ q) = τ i p ⟷ τ i q := by simp[lrarrow_def]

variables (L₁) (L₂) (L₃)

def refl : translation L₁ L₁ :=
{ to_fun := λ _, id, map_imply := by simp, map_neg := by simp, map_univ := by simp, map_pow := by simp }

def shift (k : ℕ) : translation L₁ L₁ :=
{ to_fun := λ i p, p.rew (λ x, if x < i then #x else #(x + k)),
  map_imply := by simp,
  map_neg := by simp,
  map_univ := λ p i, by { simp[rewriting_sf_itr.pow_eq], congr, funext x, cases x; simp[←nat.add_one],
    by_cases C : x < i; simp[C], omega },
  map_pow := λ p k, by { simp[formula.pow_eq, formula.nested_rew], congr, 
    funext x, by_cases C : x < k; simp[C], omega } }

variables {L₁} {L₂} {L₃}

def comp : translation L₁ L₂ → translation L₂ L₃ → translation L₁ L₃ := λ τ₁₂ τ₂₃,
{ to_fun := λ i, τ₂₃ i ∘ τ₁₂ i, map_imply := by simp, map_neg := by simp,
  map_univ := by simp, map_pow := by simp[map_pow'] }

end translation

def tr_theory {L₁ L₂ : language} (τ : translation L₁ L₂) (i) (T : theory L₁) : theory L₂ := τ i '' T

@[simp] lemma mem_theory_tr_of_mem {L₁ L₂ : language} {τ : translation L₁ L₂} {i}
  {T : theory L₁} {p} (mem : p ∈ T) : τ i p ∈ tr_theory τ i T :=
⟨p, mem, rfl⟩

structure term_translation (L₁ : language.{u}) (L₂ : language.{u}) :=
(to_fun_chr : ℕ → Π {n}, L₁.fn n → finitary (term L₂) n → term L₂)
(to_fun : ℕ → term L₁ → term L₂)
(map_fn : Π (k : ℕ) {n} (f : L₁.fn n) (v : finitary (term L₁) n),
  to_fun k (term.app f v) = to_fun_chr k f (λ i, to_fun k (v i)))

instance {L₁ L₂ : language.{u}} : has_coe_to_fun (term_translation L₁ L₂) (λ _, ℕ → term L₁ → term L₂) :=
⟨λ τ, τ.to_fun⟩

namespace term_translation
variables {L₁ L₂ : language.{u}}

@[simp] lemma translation.map_imply' (τ : term_translation L₁ L₂) {n} (f : L₁.fn n) (v : finitary (term L₁) n) (k) :
  τ k (term.app f v) = τ.to_fun_chr k f (λ i, τ k (v i)) := τ.map_fn k f v

@[simp] lemma app_eq (fc) (f) (map_fn) (t : term L₁) (i) :
  ({to_fun_chr := fc, to_fun := f, map_fn := map_fn} : term_translation L₁ L₂) i t = f i t := rfl

@[simp] def mk_fun_of_atom {L₁ L₂ : language.{u}} 
  (to_fun_chr : ℕ → Π {n}, L₁.fn n → finitary (term L₂) n → term L₂) : ℕ → term L₁ → term L₂
| _ #n        := #n
| k (app f v) := to_fun_chr k f (λ i, mk_fun_of_atom k (v i))

@[simp] def mk_of_atom {L₁ L₂ : language.{u}}
  (to_fun_chr : ℕ → Π {n}, L₁.fn n → finitary (term L₂) n → term L₂) : term_translation L₁ L₂ :=
{ to_fun_chr := @to_fun_chr,
  to_fun := mk_fun_of_atom @to_fun_chr,
  map_fn := by simp }

end term_translation

structure term_formula_translation (L₁ : language.{u}) (L₂ : language.{u}) :=
(formula_tr : translation L₁ L₂)
(term_tr : term_translation L₁ L₂)
(consistence : ∀ (t u : term L₁) (k),
  formula_tr k (t ≃ u : formula L₁) = (term_tr k t ≃ term_tr k u))

namespace term_formula_translation
variables {L₁ L₂ : language.{u}}

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
{ to_fun_chr := λ k n f v, term.app (sum.inl f) v,
  to_fun     := λ k, add_tr_v1,
  map_fn     := λ k n f v, by { simp, refl } }

instance {n} : has_coe (L₁.fn n) ((L₁ + L₂).fn n) := ⟨fn_to_add⟩

instance {n} : has_coe (L₁.pr n) ((L₁ + L₂).pr n) := ⟨pr_to_add⟩

instance : has_coe (term L₁) (term (L₁ + L₂)) := ⟨add_term_translation 0⟩

@[simp] def add_tr1 : formula L₁ → formula (L₁ + L₂)
 | (formula.app p v)   := formula.app (↑p) (λ i, (v i))
 | ((t : term L₁) ≃ u) := (↑t : term (L₁ + L₂)) ≃ ↑u
 | (p ⟶ q)             := add_tr1 p ⟶ add_tr1 q
 | (⁻p)                := ⁻add_tr1 p
 | (∏ p)               := ∏ add_tr1 p

lemma term_coe_rew_var : ∀ (t : term L₁) (s : ℕ → ℕ),
  (t : term (L₁ + L₂)).rew (λ x, #(s x)) = (t.rew (λ x, #(s x)))
| (#n)                s := by unfold_coes; simp[add_term_translation]
| (@term.app _ n f v) s := by { unfold_coes; simp[add_term_translation], funext i, exact @term_coe_rew_var (v i) _ }

lemma formula_coe_rew_var : ∀ (p : formula L₁) (s : ℕ → ℕ),
  (add_tr1 p : formula (L₁ + L₂)).rew (λ x, #(s x)) = add_tr1 (p.rew (λ x, #(s x)))
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

def add_translation : translation L₁ (L₁ + L₂) :=
{ to_fun := λ i, add_tr1,
  map_imply := by simp,
  map_neg := by simp,
  map_univ := by simp,
  map_pow := λ p k, eq.symm (formula_coe_rew_var p (λ x, x + 1)) }

instance : has_coe (formula L₁) (formula (L₁ + L₂)) := ⟨add_translation 0⟩

def add_t_f_translation : term_formula_translation L₁ (L₁ + L₂) :=
{ term_tr := add_term_translation,
  formula_tr := add_translation,
  consistence := λ t u k, by { simp[add_translation, add_term_translation], refine ⟨rfl, rfl⟩ } }

instance : has_coe (theory L₁) (theory (L₁ + L₂)) := ⟨tr_theory add_translation 0⟩

instance [has_zero_symbol L₁] : has_zero_symbol (L₁ + L₂) := ⟨fn_to_add has_zero_symbol.zero⟩

instance [has_succ_symbol L₁] : has_succ_symbol (L₁ + L₂) := ⟨fn_to_add has_succ_symbol.succ⟩

instance [has_add_symbol L₁] : has_add_symbol (L₁ + L₂) := ⟨fn_to_add has_add_symbol.add⟩

instance [has_mul_symbol L₁] : has_mul_symbol (L₁ + L₂) := ⟨fn_to_add has_mul_symbol.mul⟩

instance [has_le_symbol L₁] : has_le_symbol (L₁ + L₂) := ⟨pr_to_add has_le_symbol.le⟩

instance [has_mem_symbol L₁] : has_mem_symbol (L₁ + L₂) := ⟨pr_to_add has_mem_symbol.mem⟩

lemma add_formula_coe_eq (k) (p : formula L₁) :
  (add_translation : translation L₁ (L₁ + L₂)) k p = p := rfl

lemma add_term_coe_eq (k) (t : term L₁) :
  (add_term_translation : term_translation L₁ (L₁ + L₂)) k t = (t : term (L₁ + L₂)) := rfl

@[simp] lemma add_tr_v1_var (n) : ((#n : term L₁) : term (L₁ + L₂)) = #n := rfl

lemma add_tr_v1_app {n} (f : L₁.fn n) (v : finitary (term L₁) n) :
  ((❨f❩ v : term L₁) : term (L₁ + L₂)) = ❨fn_to_add f❩ (λ i, (v i)) := by refl

@[simp] lemma add_tr_v1_zero [has_zero_symbol L₁] :
  ((0 : term L₁) : term (L₁ + L₂)) = 0 := by { unfold has_zero.zero has_zero_symbol.zero,
   simp [←add_term_coe_eq 0, add_term_translation, add_translation] }

@[simp] lemma add_tr_v1_succ [has_succ_symbol L₁] (t : term L₁) :
  ((Succ t : term L₁) : term (L₁ + L₂)) = Succ t :=
by { unfold has_succ.succ, simp [← add_term_coe_eq 0, add_term_translation, add_translation],
     split, { refl }, { ext; simp } }

@[simp] lemma add_tr_v1_numeral [has_zero_symbol L₁] [has_succ_symbol L₁] (n : ℕ) :
  ((n˙ : term L₁) : term (L₁ + L₂)) = n˙ :=
by induction n; simp[*, numeral]

@[simp] lemma add_tr_v1_add [has_add_symbol L₁] (t u : term L₁) :
  ((t + u : term L₁) : term (L₁ + L₂)) = t + u :=
by { unfold has_add.add, simp [←add_term_coe_eq 0, add_term_translation, add_translation],
     split, { refl }, { ext; simp } }

@[simp] lemma add_tr_v1_mul [has_mul_symbol L₁] (t u : term L₁) :
  ((t * u : term L₁) : term (L₁ + L₂)) = t * u :=
by { unfold has_mul.mul, simp [←add_term_coe_eq 0, add_term_translation, add_translation],
     split, { refl }, { ext; simp } }

@[simp] lemma add_tr_v1_le [has_le_symbol L₁] (t u : term L₁) :
  ((t ≼ u : formula L₁) : formula (L₁ + L₂)) = ((t : term (L₁ + L₂)) ≼ u) :=
by { unfold has_preceq.preceq, simp [←add_formula_coe_eq 0, add_term_translation, add_translation], split,
     { refl }, { ext; simp; refl } }

@[simp] lemma add_tr_v1_mem [has_mem_symbol L₁] (t u : term L₁) :
  ((t ∊ u : formula L₁) : formula (L₁ + L₂)) = ((t : term (L₁ + L₂)) ∊ u) :=
by { unfold has_elem.elem, simp [←add_formula_coe_eq 0, add_term_translation, add_translation],
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

variables {L₁ L₂ L₃ : language.{u}}
local infix ` ≃₁ `:50 := ((≃) : term L₁ → term L₁ → formula L₁)
local infix ` ≃₂ `:50 := ((≃) : term L₂ → term L₂ → formula L₂)

class translation.conservative (τ : translation L₁ L₂) :=
(specialize : ∀ (k) (p : formula L₁) (t : term L₁) (T : theory L₂), T ⊢ τ k (∏ p ⟶ p.rew ι[0 ⇝ t]))
(eq_reflexivity : ∀ (k) (T : theory L₂), T ⊢ τ k (∏ (#0 ≃₁ #0)) )
(eq_symmetry : ∀ (k) (T : theory L₂), T ⊢ τ k (∏ ∏ ((#0 ≃₁ #1) ⟶ (#1 ≃₁ #0))))
(eq_transitive : ∀ (k) (T : theory L₂), T ⊢ τ k (∏ ∏ ∏ ((#0 ≃₁ #1) ⟶ (#1 ≃₁ #2) ⟶ (#0 ≃₁ #2))))
(function_ext : ∀ (k) {n} (f : L₁.fn n) (T : theory L₂), T ⊢ τ k (eq_axiom4 f))
(predicate_ext : ∀ (k) {n} (r : L₁.pr n) (T : theory L₂), T ⊢ τ k (eq_axiom5 r))

namespace translation

open provable axiomatic_classical_logic' translation.conservative

variables {L₁} {L₂}
variables (τ : translation L₁ L₂) [conservative τ] (i : ℕ)

@[simp] lemma mem_pow_theory_tr_of_mem_pow {T : theory L₁} {k : ℕ} {p} {i : ℕ} (mem : p ∈ T^k) :
  (τ (i + k) p) ∈ (tr_theory τ i T : theory L₂)^k :=
by { simp[theory_sf_itr_eq] at mem ⊢, rcases mem with ⟨q, mem, rfl⟩, 
  refine ⟨τ i q, mem_theory_tr_of_mem mem, _⟩, simp[translation.map_pow'] }

lemma provability_pow (T : theory L₁) (p : formula L₁) (i k : ℕ) :
  T^i ⊢ p → (tr_theory τ k T)^i ⊢ τ (k + i) p :=
begin
  refine provable.rec' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  { intros i p _ h, simp at h ⊢, simp[add_assoc],
    exact generalize h },
  { intros i p q _ _ hpq hp, simp at hpq,
    exact hpq ⨀ hp },
  { intros i p mem, refine by_axiom (by simp[mem]) },
  { intros, simp },
  { intros, simp },
  { intros, simp },
  { intros, exact specialize _ _ _ _ },
  { intros, simp },
  { intros, simp[translation.map_pow'] },
  { intros, exact eq_reflexivity _ _ },
  { intros, exact eq_symmetry _ _ },
  { intros, exact eq_transitive _ _ },
  { intros, exact function_ext _ _ _ },
  { intros, exact predicate_ext _ _ _ },
end

lemma provability (T : theory L₁) (p : formula L₁) (k : ℕ) :
  T ⊢ p → τ k '' T ⊢ τ k p :=
by { have := provability_pow τ T p 0, simp at this, exact this k }

lemma provability_tautology (p : formula L₁) (k : ℕ):
  (∀ T, T ⊢ p) → ∀ T, T ⊢ τ k p := λ h T,
by { have := provability τ ∅ p k (h ∅), simp at this, exact weakening this (by simp) }

instance refl_conservative : conservative (refl L₁) :=
{ specialize := by simp[translation.refl],
  eq_reflexivity := by simp[translation.refl],
  eq_symmetry := by simp[translation.refl],
  eq_transitive := by simp[translation.refl],
  function_ext := by simp[translation.refl],
  predicate_ext := by simp[translation.refl] }

instance shift_conservative (k : ℕ) : conservative (shift L₁ k) :=
{ specialize := λ l p t T, by {simp[translation.shift], 
    have : (p.rew ι[0 ⇝ t]).rew (λ x, ite (x < l) #x #(x + k)) = 
      (p.rew (λ x, ite (x < l + 1) #x #(x + k))).rew ι[0 ⇝ (t.rew (λ x, ite (x < l) #x #(x + k)))],
    { simp[formula.nested_rew], congr, funext x, cases x with x; simp[←nat.add_one],
      by_cases C : x < l; simp[C, show x + 1 + k = x + k + 1, by omega] },
    simp [this] },
  eq_reflexivity := by simp[translation.shift],
  eq_symmetry := by simp[translation.shift],
  eq_transitive := λ l, by simp[translation.shift, show 2 < l + 1 + 1 + 1, by omega], 
  function_ext := by simp[translation.shift],
  predicate_ext := by simp[translation.shift] }

instance comp_conservative
  (τ₁₂ : translation L₁ L₂) (τ₂₃ : translation L₂ L₃) [conservative τ₁₂] [conservative τ₂₃] :
  conservative (τ₁₂.comp τ₂₃) :=
{ specialize :=
    λ k p t T, (provability_tautology τ₂₃ _ k (conservative.specialize k p t) T : T ⊢ τ₂₃ k (τ₁₂ k _)),
  eq_reflexivity :=
    λ k T, (provability_tautology τ₂₃ _ k (conservative.eq_reflexivity k) T : T ⊢ τ₂₃ k (τ₁₂ k _)),
  eq_symmetry :=
    λ k T, (provability_tautology τ₂₃ _ k (conservative.eq_symmetry k) T : T ⊢ τ₂₃ k (τ₁₂ k _)),
  eq_transitive :=
    λ k T, (provability_tautology τ₂₃ _ k (conservative.eq_transitive k) T : T ⊢ τ₂₃ k (τ₁₂ k _)),
  function_ext :=
    λ k n f T, (provability_tautology τ₂₃ _ k (conservative.function_ext k f) T : T ⊢ τ₂₃ k (τ₁₂ k _)),
  predicate_ext :=
    λ k n f T, (provability_tautology τ₂₃ _ k (conservative.predicate_ext k f) T : T ⊢ τ₂₃ k (τ₁₂ k _)) }

end translation

end language


end fopl
