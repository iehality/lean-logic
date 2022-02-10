import deduction lindenbaum

universes u v

namespace fopl
open formula term

namespace language
variables {L L₁ L₂ L₃ : language.{u}}
local infix ` ≃₀ `:50 := ((≃) : term L → term L → formula L)
local infix ` ≃₁ `:50 := ((≃) : term L₁ → term L₁ → formula L₁)
local infix ` ≃₂ `:50 := ((≃) : term L₂ → term L₂ → formula L₂)

structure language_translation (L₁ : language) (L₂ : language) :=
(fn : Π {n}, L₁.fn n → L₂.fn n)
(pr : Π {n}, L₁.pr n → L₂.pr n)

infix ` ↝ᴸ `:25 := language_translation

class language_translation_coe (L₁ : language) (L₂ : language) :=
(ltr : L₁ ↝ᴸ L₂)
(fn_inj : ∀ {n} (f g : L₁.fn n), ltr.fn f = ltr.fn g → f = g)
(pr_inj : ∀ {n} (p q : L₁.pr n), ltr.pr p = ltr.pr q → p = q)

structure translation (L₁ : language) (L₂ : language.{v}) :=
(to_fun : ℕ → formula L₁ → formula L₂)
(map_verum : ∀ i, to_fun i ⊤ = ⊤)
(map_imply : ∀ (p q : formula L₁) (i : ℕ), to_fun i (p ⟶ q) = to_fun i p ⟶ to_fun i q)
(map_neg : ∀ (p : formula L₁) (i), to_fun i (⁻p) = ⁻to_fun i p)
(map_univ : ∀ (p : formula L₁) (i), to_fun i (∏ p) = ∏ to_fun (i + 1) p)
(map_pow : ∀ (p : formula L₁) (i), to_fun (i + 1) (p^1) = (to_fun i p)^1)

infix ` ↝ `:25 := translation

instance {L₁ L₂ : language} : has_coe_to_fun (translation L₁ L₂) (λ _, ℕ → formula L₁ → formula L₂) :=
⟨@translation.to_fun L₁ L₂⟩

structure term_translation (L₁ : language) (L₂ : language) :=
(to_fun_chr : ℕ → Π {n}, L₁.fn n → finitary (term L₂) n → term L₂)
(to_fun : ℕ → term L₁ → term L₂)
(map_fn : Π (k : ℕ) {n} (f : L₁.fn n) (v : finitary (term L₁) n),
  to_fun k (term.app f v) = to_fun_chr k f (λ i, to_fun k (v i)))

infix ` ↝ᵀ `:25 := term_translation

instance {L₁ L₂ : language} : has_coe_to_fun (term_translation L₁ L₂) (λ _, ℕ → term L₁ → term L₂) :=
⟨λ τ, τ.to_fun⟩

def tr_theory {L₁ L₂ : language} (τ : translation L₁ L₂) (i) (T : theory L₁) : theory L₂ := τ i '' T

@[simp] lemma mem_theory_tr_of_mem {L₁ L₂ : language} {τ : translation L₁ L₂} {i}
  {T : theory L₁} {p} (mem : p ∈ T) : τ i p ∈ tr_theory τ i T :=
⟨p, mem, rfl⟩

structure term_formula_translation (L₁ : language) (L₂ : language) :=
(tr : translation L₁ L₂)
(tr_term : term_translation L₁ L₂)
(consistence_eq : ∀ (t u : term L₁) (k), tr k (t ≃ u : formula L₁) = (tr_term k t ≃ tr_term k u))

class translation.conservative (τ : translation L₁ L₂) :=
(ax : ℕ → theory L₁ → theory L₂)
(ax_ss : ∀ T k, tr_theory τ k T ⊆ ax k T)
(specialize : ∀ (k) (p : formula L₁) (t : term L₁) (T : theory L₁) (i : ℕ), 
  (ax k T)^i ⊢ τ (k + i) (∏ p ⟶ p.rew ı[0 ⇝ t]))
(eq_reflexivity : ∀ (k) (T : theory L₁) (i : ℕ),
  (ax k T)^i ⊢ τ (k + i) (∏ (#0 ≃₁ #0)))
(eq_symmetry : ∀ (k) (T : theory L₁) (i : ℕ),
  (ax k T)^i ⊢ τ (k + i) (∏ ∏ ((#0 ≃₁ #1) ⟶ (#1 ≃₁ #0))))
(eq_transitive : ∀ (k) (T : theory L₁) (i : ℕ),
  (ax k T)^i ⊢ τ (k + i) (∏ ∏ ∏ ((#0 ≃₁ #1) ⟶ (#1 ≃₁ #2) ⟶ (#0 ≃₁ #2))))
(function_ext : ∀ (k) {n} (f : L₁.fn n) (T : theory L₁) (i : ℕ),
  (ax k T)^i ⊢ τ (k + i) (eq_axiom4 f))
(predicate_ext : ∀ (k) {n} (r : L₁.pr n) (T : theory L₁) (i : ℕ),
  (ax k T)^i ⊢ τ (k + i) (eq_axiom5 r))

namespace translation

@[simp] lemma app_eq (to_fun) (map_verum) (map_imply) (map_neg) (map_univ) (map_pow) (p : formula L₁) (i) :
  ({ to_fun := to_fun, map_verum := map_verum, map_imply := map_imply, map_neg := map_neg,
     map_univ := map_univ, map_pow := map_pow} : translation L₁ L₂) i p = to_fun i p := rfl

@[simp] def fun_of_atom {L₁ L₂ : language}
  (tr_pr : ℕ → Π {n}, L₁.pr n → finitary (term L₁) n → formula L₂)
  (tr_eq : ℕ → term L₁ → term L₁ → formula L₂) : ℕ → formula L₁ → formula L₂
| k ⊤                    := ⊤
| k (app p v)            := tr_pr k p v
| k ((t : term L₁) ≃ u)  := tr_eq k t u
| k (p ⟶ q)              := fun_of_atom k p ⟶ fun_of_atom k q
| k (⁻p)                 := ⁻fun_of_atom k p
| k (∏ (p : formula L₁)) := ∏ fun_of_atom (k + 1) p

def mk_of_atom' {L₁ L₂ : language}
  (tr_pr : ℕ → Π {n}, L₁.pr n → finitary (term L₁) n → formula L₂)
  (tr_eq : ℕ → term L₁ → term L₁ → formula L₂)
  (map_pow : ∀ (p : formula L₁) (k : ℕ), fun_of_atom @tr_pr @tr_eq (k + 1) (p^1) = (fun_of_atom @tr_pr @tr_eq k p)^1) :
  translation L₁ L₂ :=
{ to_fun := fun_of_atom @tr_pr @tr_eq,
  map_verum := by simp,
  map_imply := by simp,
  map_neg := by simp,
  map_univ := by simp,
  map_pow := map_pow }

variables (τ : translation L₁ L₂) (i : ℕ)

@[simp] lemma map_verum' :
  τ i ⊤ = ⊤ := τ.map_verum i

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

@[simp] lemma map_falsum' :
  τ i ⊥ = ⊥ := by { unfold has_bot.bot, simp }

@[simp] lemma map_ex' (p : formula L₁) :
  τ i (∐ p) = ∐ (τ (i + 1) p) := by { unfold has_exists_quantifier.ex formula.ex, simp }

@[simp] lemma map_and' (p q : formula L₁) :
  τ i (p ⊓ q) = τ i p ⊓ τ i q := by { unfold has_inf.inf formula.and, simp }

@[simp] lemma map_or' (p q : formula L₁) :
  τ i (p ⊔ q) = τ i p ⊔ τ i q := by { unfold has_sup.sup formula.or, simp }

@[simp] lemma map_equiv' (p q : formula L₁) :
  τ i (p ⟷ q) = τ i p ⟷ τ i q := by simp[lrarrow_def]

@[simp] lemma map_nfal' (p : formula L₁) (k : ℕ) :
  τ i (∏[k] p) = ∏[k] τ (i + k) p :=
by { induction k with k IH generalizing i; simp[*],
     { simp[show i + k.succ = i + 1 + k, by omega] } }

@[simp] lemma map_conjunction'' {n} (P : finitary (formula L₁) n) :
  τ i (⋀ j, P j) = ⋀ j, (τ i (P j)) :=
by { induction n with n IH generalizing P; simp* }

@[simp] lemma map_disjunction'' {n} (P : finitary (formula L₁) n) :
  τ i (⋁ j, P j) = ⋁ j, (τ i (P j)) :=
by { induction n with n IH generalizing P; simp* }

variables (L₁) (L₂) (L₃)

def refl : translation L₁ L₁ :=
{ to_fun := λ _, id,
  map_verum := by simp, map_imply := by simp, map_neg := by simp, map_univ := by simp, map_pow := by simp }

def shift (k : ℕ) : translation L₁ L₁ :=
{ to_fun := λ i p, p.rew (λ x, if x < i then #x else #(x + k)),
  map_verum := by simp,
  map_imply := by simp,
  map_neg := by simp,
  map_univ := λ p i, by { simp[rewriting_sf_itr.pow_eq], congr, funext x, cases x; simp[←nat.add_one],
    by_cases C : x < i; simp[C], omega },
  map_pow := λ p i, by { simp[formula.pow_eq, formula.nested_rew], congr, 
    funext x, by_cases C : x < i; simp[C], omega } }

variables {L₁} {L₂} {L₃}

def comp : translation L₁ L₂ → translation L₂ L₃ → translation L₁ L₃ := λ τ₁₂ τ₂₃,
{ to_fun := λ i, τ₂₃ i ∘ τ₁₂ i,
  map_verum := by simp, map_imply := by simp, map_neg := by simp,
  map_univ := by simp, map_pow := by simp[map_pow'] }

end translation

namespace term_translation

@[simp] lemma translation.map_imply' (τ : term_translation L₁ L₂) {n} (f : L₁.fn n) (v : finitary (term L₁) n) (k) :
  τ k (term.app f v) = τ.to_fun_chr k f (λ i, τ k (v i)) := τ.map_fn k f v

@[simp] lemma app_eq (fc) (f) (map_fn) (t : term L₁) (i) :
  ({to_fun_chr := fc, to_fun := f, map_fn := map_fn} : term_translation L₁ L₂) i t = f i t := rfl

@[simp] def mk_fun_of_atom {L₁ L₂ : language} 
  (to_fun_chr : ℕ → Π {n}, L₁.fn n → finitary (term L₂) n → term L₂) : ℕ → term L₁ → term L₂
| _ #n        := #n
| k (app f v) := to_fun_chr k f (λ i, mk_fun_of_atom k (v i))

@[simp] def mk_of_atom {L₁ L₂ : language}
  (to_fun_chr : ℕ → Π {n}, L₁.fn n → finitary (term L₂) n → term L₂) : term_translation L₁ L₂ :=
{ to_fun_chr := @to_fun_chr,
  to_fun := mk_fun_of_atom @to_fun_chr,
  map_fn := by simp }

end term_translation

namespace language_translation
variables (τ : L₁ ↝ᴸ L₂)

@[simp] def fun_term : term L₁ → term L₂
| #n        := #n
| (app f v) := app (τ.fn f) (λ i, fun_term (v i))

def tr_term : term_translation L₁ L₂ :=
{ to_fun_chr := λ k n f v, app (τ.fn f) v,
  to_fun     := λ k, τ.fun_term,
  map_fn     := λ k n f v, by simp }

@[simp] def fun_formula : formula L₁ → formula L₂
| ⊤                    := ⊤
| (app p v)            := app (τ.pr p) (λ i, fun_term τ (v i))
| ((t : term L₁) ≃ u)  := fun_term τ t ≃ fun_term τ u
| (p ⟶ q)              := fun_formula p ⟶ fun_formula q
| (⁻p)                 := ⁻fun_formula p
| (∏ (p : formula L₁)) := ∏ fun_formula p

lemma fun_term_rew_var : ∀ (t : term L₁) (s : ℕ → ℕ),
  (fun_term τ t).rew (λ x, #(s x)) = fun_term τ (t.rew (λ x, #(s x)))
| (#n)                s := by simp
| (@term.app _ n f v) s := by { simp, funext i, exact @fun_term_rew_var (v i) _ }

lemma fun_formula_rew_var : ∀ (p : formula L₁) (s : ℕ → ℕ),
  (fun_formula τ p).rew (λ x, #(s x)) = fun_formula τ (p.rew (λ x, #(s x)))
| ⊤                      _ := by simp
| (@formula.app _ n r v) s := by { simp, funext i, simp[fun_term_rew_var] }
| ((t : term L₁) ≃ u)    s := by simp[fun_term_rew_var]
| (p ⟶ q)                s := by simp[fun_formula_rew_var p, fun_formula_rew_var q]
| (⁻p)                   s := by simp[fun_formula_rew_var p]
| (∏ (p : formula L₁))   s := by { 
    have eqn₁ : ((λ x, #(s x))^1 : ℕ → term L₁) = (λ x, #(if x = 0 then 0 else s (x - 1) + 1)),
    { funext x, cases x; simp },
    have eqn₂ : ((λ x, #(s x))^1 : ℕ → term L₂) = (λ x, #(if x = 0 then 0 else s (x - 1) + 1)),
    { funext x, cases x; simp },
    simp[fal_pow, eqn₁, eqn₂, fun_formula_rew_var p] }

def tr : translation L₁ L₂ :=
{ to_fun := λ _, τ.fun_formula,
  map_verum := by simp,
  map_imply := by simp,
  map_neg := by simp,
  map_univ := by simp,
  map_pow := λ p i, eq.symm (τ.fun_formula_rew_var p (λ x, x + 1)) }

lemma tr_term_app_eq (k) (t) : 
  τ.tr_term k t = τ.fun_term t := by refl

lemma tr_app_eq (k) (p) : 
  τ.tr k p = τ.fun_formula p := by refl

@[simp] lemma tr_term_to_fun_chr_app_eq (k) {n} (f : L₁.fn n) (v : finitary (term L₂) n) :
  τ.tr_term.to_fun_chr k f v = app (τ.fn f) v := rfl

@[simp] lemma fun_term_pow (t : term L₁) (i : ℕ) :
  (τ.fun_term (t^i) : term L₂) = (τ.fun_term t)^i :=
eq.symm (τ.fun_term_rew_var t (λ x, x + i))

@[simp] lemma fun_formula_pow (p : formula L₁) (i : ℕ) :
  (τ.fun_formula (p^i) : formula L₂) = (τ.fun_formula p)^i := 
eq.symm (τ.fun_formula_rew_var p (λ x, x + i))

lemma fun_term_rew : ∀ (t : term L₁) (s : ℕ → term L₁),
  τ.fun_term (t.rew s) = (τ.fun_term t).rew (λ x, τ.fun_term (s x))
| (#x)           s := by simp
| (term.app p v) s := by simp[λ i, fun_term_rew (v i)]

lemma fun_formula_rew : ∀ (p : formula L₁) (s : ℕ → term L₁),
  τ.fun_formula (p.rew s) = (τ.fun_formula p).rew (λ x, τ.fun_term (s x))
| ⊤                 s := by simp
| (formula.app f v) s := by simp[fun_term_rew]
| (t ≃₁ u)          s := by simp[fun_term_rew]
| (p ⟶ q)           s := by simp[fun_formula_rew p, fun_formula_rew q]
| (⁻p)              s := by simp[fun_formula_rew p]
| (∏ p)             s := by
    { simp[fun_formula_rew p, rewriting_sf_itr.pow_eq'], congr, funext x, cases x; simp }

end language_translation

namespace language_translation_coe
open language_translation
variables [σ : language_translation_coe L₁ L₂]
include σ

instance {n} : has_coe (L₁.fn n) (L₂.fn n) := ⟨λ n, σ.ltr.fn n⟩

instance {n} : has_coe (L₁.pr n) (L₂.pr n) := ⟨λ n, σ.ltr.pr n⟩

instance : has_coe (term L₁) (term L₂) := ⟨σ.ltr.fun_term⟩

lemma app_term_extention_eq (t : term L₁) (i : ℕ) :
  (σ.ltr.tr_term i t : term L₂) = ↑t := rfl

instance : has_coe (formula L₁) (formula L₂) := ⟨σ.ltr.fun_formula⟩

lemma app_formula_extention_eq (p : formula L₁) (i : ℕ) :
  (σ.ltr.tr i p : formula L₂) = ↑p := rfl

def t_f_translation : term_formula_translation L₁ L₂ :=
{ tr_term := σ.ltr.tr_term,
  tr := σ.ltr.tr,
  consistence_eq := λ t u k, by { simp[tr], refine ⟨rfl, rfl⟩ } }

instance : has_coe (theory L₁) (theory L₂) := ⟨tr_theory σ.ltr.tr 0⟩

instance [has_zero_symbol L₁] : has_zero_symbol L₂ := ⟨σ.ltr.fn has_zero_symbol.zero⟩

instance [has_succ_symbol L₁] : has_succ_symbol L₂ := ⟨σ.ltr.fn has_succ_symbol.succ⟩

instance [has_add_symbol L₁] : has_add_symbol L₂ := ⟨σ.ltr.fn has_add_symbol.add⟩

instance [has_mul_symbol L₁] : has_mul_symbol L₂ := ⟨σ.ltr.fn has_mul_symbol.mul⟩

instance [has_le_symbol L₁] : has_le_symbol L₂ := ⟨σ.ltr.pr has_le_symbol.le⟩

instance [has_mem_symbol L₁] : has_mem_symbol L₂ := ⟨σ.ltr.pr has_mem_symbol.mem⟩

lemma app_formula_extention_eq_coe (k) (p : formula L₁) :
  (σ.ltr.tr : translation L₁ L₂) k p = ↑p := rfl

lemma app_term_extention_eq_coe (k) (t : term L₁) :
  (σ.ltr.tr_term : term_translation L₁ L₂) k t = ↑t := rfl

@[simp] lemma add_tr_v1_var (n) : ((#n : term L₁) : term L₂) = #n := rfl

lemma add_tr_v1_app {n} (f : L₁.fn n) (v : finitary (term L₁) n) :
  ((❨f❩ v : term L₁) : term L₂) = ❨σ.ltr.fn f❩ (λ i, (v i)) := by refl

@[simp] lemma coe_tr_v1_zero [has_zero_symbol L₁] :
  ((0 : term L₁) : term L₂) = 0 := by { unfold has_zero.zero has_zero_symbol.zero,
   simp [←app_term_extention_eq_coe 0] }

@[simp] lemma coe_tr_v1_succ [has_succ_symbol L₁] (t : term L₁) :
  ((Succ t : term L₁) : term L₂) = Succ t :=
by { unfold has_succ.succ, simp [←app_term_extention_eq_coe 0],
     split, { refl }, { ext; simp } }

@[simp] lemma coe_tr_v1_numeral [has_zero_symbol L₁] [has_succ_symbol L₁] (n : ℕ) :
  ((n˙ : term L₁) : term L₂) = n˙ :=
by induction n; simp[*, numeral]

@[simp] lemma coe_tr_v1_add [has_add_symbol L₁] (t u : term L₁) :
  ((t + u : term L₁) : term L₂) = t + u :=
by { unfold has_add.add, simp [←app_term_extention_eq_coe 0],
     split, { refl }, { ext; simp } }

@[simp] lemma coe_tr_v1_mul [has_mul_symbol L₁] (t u : term L₁) :
  ((t * u : term L₁) : term L₂) = t * u :=
by { unfold has_mul.mul, simp [←app_term_extention_eq_coe 0],
     split, { refl }, { ext; simp } }

@[simp] lemma coe_tr_v1_le [has_le_symbol L₁] (t u : term L₁) :
  ((t ≼ u : formula L₁) : formula L₂) = ((t : term L₂) ≼ u) :=
by { unfold has_preceq.preceq, simp [←app_formula_extention_eq_coe 0, tr_app_eq], 
     split, { refl }, { ext; simp; refl } }

@[simp] lemma coe_tr_v1_mem [has_mem_symbol L₁] (t u : term L₁) :
  ((t ∊ u : formula L₁) : formula L₂) = ((t : term L₂) ∊ u) :=
by { unfold has_elem.elem, simp [←app_formula_extention_eq_coe 0, tr_app_eq],
     split, { refl }, { ext; simp; refl } }

@[simp] lemma coe_term_app {i} (f : L₁.fn i) (v : finitary (term L₁) i) :
  (↑(term.app f v : term L₁) : term L₂) = term.app (f : L₂.fn i) (λ i, v i) := rfl

@[simp] lemma coe_formula_app {i} (p : L₁.pr i) (v : finitary (term L₁) i) :
  (↑(formula.app p v : formula L₁) : formula L₂) = formula.app (p : L₂.pr i) (λ i, v i) := rfl

@[simp] lemma coe_equal (t u : term L₁) :
  (↑(t ≃ u : formula L₁) : formula L₂) = ((↑t : term L₂) ≃ ↑u) := rfl

@[simp] lemma coe_imply (p q : formula L₁) :
  (↑(p ⟶ q) : formula L₂) = (↑p ⟶ ↑q) := rfl

@[simp] lemma coe_and (p q : formula L₁) :
  (↑(p ⊓ q) : formula L₂) = (↑p ⊓ ↑q) := rfl

@[simp] lemma coe_or (p q : formula L₁) :
  (↑(p ⊔ q) : formula L₂) = (↑p ⊔ ↑q) := rfl

@[simp] lemma coe_neg (p : formula L₁) :
  (↑(⁻p) : formula L₂) = ⁻(↑p) := rfl

@[simp] lemma coe_pow_term (t : term L₁) (i : ℕ) :
  (↑(t^i) : term L₂) = (↑t)^i :=
by simp [tr_term_app_eq, ←app_term_extention_eq_coe 0]

@[simp] lemma coe_pow_formula (p : formula L₁) (i : ℕ) :
  (↑(p^i) : formula L₂) = (↑p)^i := 
by simp [tr_app_eq, ←app_formula_extention_eq_coe 0]

@[simp] lemma coe_fal (p : formula L₁)  :
  (↑(∏ p : formula L₁) : formula L₂) = ∏ (↑p : formula L₂) := rfl

@[simp] lemma coe_ex (p : formula L₁)  :
  (↑(∐ p : formula L₁) : formula L₂) = ∐ (↑p : formula L₂) := rfl

@[simp] lemma coe_top :
  (↑(⊤ : formula L₁) : formula L₂) = ⊤ := rfl

@[simp] lemma coe_bot :
  (↑(⊥ : formula L₁) : formula L₂) = ⊥ := rfl

@[simp] lemma coe_conjunction (P : list (formula L₁)) :
  (↑(conjunction P) : formula L₂) = conjunction (P.map coe) :=
by induction P with p P IH; simp[conjunction, *]

@[simp] lemma coe_nfal (p : formula L₁) (k : ℕ) :
  (↑(∏[k] p) : formula L₂) = ∏[k] ↑p :=
by { induction k with k IH; simp[*] }

@[simp] lemma coe_conjunction' {n : ℕ} (P : finitary (formula L₁) n) :
  (↑(⋀ j, P j) : formula L₂) = ⋀ j, P j :=
by { induction n with n IH generalizing P; simp* }

@[simp] lemma coe_disjunction' {n : ℕ} (P : finitary (formula L₁) n) :
  (↑(⋁ j, P j) : formula L₂) = ⋁ j, P j :=
by { induction n with n IH generalizing P; simp* }

@[simp] lemma coe_tr_v1_arity : ∀ t : term L₁, (t : term L₂).arity = t.arity
| (#x)    := rfl
| (❨f❩ v) := by simp[λ i, coe_tr_v1_arity (v i)]

@[simp] lemma coe_is_open (p : formula L₁) : (p : formula L₂).is_open ↔ p.is_open :=
by { induction p; simp[*] }

@[simp] lemma function_coe_inj {n} {f g : L₁.fn n} : (f : L₂.fn n) = g ↔ f = g :=
⟨by { have := σ.fn_inj, exact this f g }, congr_arg _⟩

@[simp] lemma predicate_coe_inj {n} {r s : L₁.pr n} : (r : L₂.pr n) = s ↔ r = s :=
⟨by { have := σ.pr_inj, exact this r s }, congr_arg _⟩

@[simp] lemma term_coe_inj : ∀ {t u : term L₁}, (t : term L₂) = u ↔ t = u
| (#m)                   (#n)                   := by simp
| (#m)                   (term.app f v)         := by simp
| (term.app f v)         (#n)                   := by simp
| (@term.app _ n₁ f₁ v₁) (@term.app _ n₂ f₂ v₂) := by { 
    simp, rintros rfl, simp,
    rintros rfl, 
    have IH : ∀ i, ↑(v₁ i) = ↑(v₂ i) ↔ v₁ i = v₂ i, from λ i, @term_coe_inj (v₁ i) (v₂ i),
    refine ⟨λ h, funext (λ i, (IH i).mp (congr_fun h i)), by { rintros rfl, refl }⟩ }

@[simp] lemma formula_coe_inj : ∀ {p q : formula L₁}, (p : formula L₂) = q ↔ p = q
| (@formula.app _ n₁ r₁ v₁) (@formula.app _ n₂ r₂ v₂) :=
    by { simp,  rintros rfl, simp, rintros rfl,
         refine ⟨λ h, funext (λ i, term_coe_inj.mp (congr_fun h i)), by { rintros rfl, refl }⟩ }
| ⊤                   q        := by simp; cases q; simp
| (formula.app r₁ v₁) (t ≃₁ u) := by simp
| (formula.app r₁ v₁) ⊤        := by simp
| (formula.app r₁ v₁) (p ⟶ q)  := by simp
| (formula.app r₁ v₁) ⁻p       := by simp
| (formula.app r₁ v₁) (∏ p)    := by simp
| (t ≃₁ u)            p        := by cases p; simp
| (p ⟶ q)             r        := by cases r; simp[@formula_coe_inj p, @formula_coe_inj q]
| (⁻p)                q        := by cases q; simp[@formula_coe_inj p]
| (∏ p)               q        := by cases q; simp[@formula_coe_inj p]

@[simp] lemma coe_mem_coe_iff {T : theory L₁} {p} : ↑p ∈ (↑T : theory L₂) ↔ p ∈ T := 
⟨λ ⟨p', h, eqn⟩, by { simp [formula_coe_inj.mp eqn] at h, exact h }, λ h, ⟨p, h, rfl⟩⟩

lemma mem_coe_iff {T : theory L₁} {p : formula L₂} :
  p ∈ (↑T : theory L₂) ↔ ∃ p₁ ∈ T, p = ↑p₁ := 
⟨λ ⟨p₁, h, eqn⟩, ⟨p₁, h, eq.symm eqn⟩, by { rintros ⟨p₁, mem, rfl⟩, simp[mem] }⟩

end language_translation_coe

namespace language_translation
variables (τ : L₁ ↝ᴸ L₂)

instance conservative : τ.tr.conservative :=
{ ax := λ k T, tr_theory τ.tr k T,
  ax_ss := by { intros, refl },
  specialize := λ k p t T i, by {
    have : (λ (x : ℕ), τ.fun_term (ı[0 ⇝ t] x)) = ı[0 ⇝ τ.fun_term t],
    { funext x, cases x; simp },
    simp[tr_app_eq, fun_formula_rew, this] },
  eq_reflexivity := by simp[tr_app_eq],
  eq_symmetry := by simp[tr_app_eq],
  eq_transitive := by simp[tr_app_eq],
  function_ext := λ k n f T i, by { simp[eq_axiom4], simp[tr_app_eq],
    exact (show _ ⊢ eq_axiom4 (τ.fn f), by simp) },
  predicate_ext := λ k n f T i, by { simp[eq_axiom5], simp[tr_app_eq],
    exact (show _ ⊢ eq_axiom5 (τ.pr f), by simp) } }

end language_translation

namespace translation
open provable axiomatic_classical_logic' translation.conservative
variables {L₁} {L₂}
variables (τ : translation L₁ L₂) [conservative τ] (i : ℕ)

@[simp] lemma mem_pow_theory_tr_of_mem_pow {T : theory L₁} {k : ℕ} {p} {i : ℕ} (mem : p ∈ T^k) :
  (τ (i + k) p) ∈ (tr_theory τ i T : theory L₂)^k :=
by { simp[theory_sf_itr_eq] at mem ⊢, rcases mem with ⟨q, mem, rfl⟩, 
  refine ⟨τ i q, mem_theory_tr_of_mem mem, _⟩, simp[translation.map_pow'] }

lemma provability_pow (T : theory L₁) (p : formula L₁) (i k : ℕ) (h : T^i ⊢ p) :
  (ax τ k T)^i ⊢ τ (k + i) p :=
begin
  refine provable.rec_on' h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  { intros i p _ h, simp[add_assoc] at h ⊢,
    exact generalize h },
  { intros i p q _ _ hpq hp, simp at hpq,
    exact hpq ⨀ hp },
  { intros i p mem,
    suffices : (tr_theory τ k T)^i ⊢ τ (k + i) p,
    { exact weakening this (by simp[ax_ss]) },
    refine (by_axiom (by {simp[mem]})) },
  { intros, simp },
  { intros, simp },
  { intros, simp },
  { intros, simp },
  { intros, refine specialize _ _ _ _ _ },
  { intros, simp },
  { intros, simp[translation.map_pow'] },
  { intros, refine eq_reflexivity _ _ _ },
  { intros, exact eq_symmetry _ _ _ },
  { intros, exact eq_transitive _ _ _ },
  { intros, exact function_ext _ _ _ _ },
  { intros, exact predicate_ext _ _ _ _ },
end

lemma provability (T : theory L₁) (p : formula L₁) (k : ℕ) :
  T ⊢ p → ax τ k T ⊢ τ k p :=
by { have := provability_pow τ T p 0, simp at this, exact this k }

lemma provability_tautology (p : formula L₁) (k : ℕ):
  (∀ T, T ⊢ p) → ∀ T, ax τ k T ⊢ τ k p := λ h T,
provability τ T p k (h T)

lemma consistency (T : theory L₁) (k : ℕ) : 
  (ax τ k T).consistent → T.consistent :=
by { simp[theory.consistent_iff_bot], contrapose, simp,
     have := provability τ T ⊥ k, simp at this,
     exact this }

instance refl_conservative : conservative (refl L₁) :=
{ ax := λ k T, tr_theory (refl L₁) k T,
  ax_ss := by { intros, refl },
  specialize := by simp[translation.refl],
  eq_reflexivity := by simp[translation.refl],
  eq_symmetry := by simp[translation.refl],
  eq_transitive := by simp[translation.refl],
  function_ext := by { intros,  simp[translation.refl] },
  predicate_ext := by { intros, simp[translation.refl] } }

instance shift_conservative (k : ℕ) : conservative (shift L₁ k) :=
{ ax := λ l T, tr_theory (shift L₁ k) l T,
  ax_ss := by { intros, refl },
  specialize := λ l p t T i, by {simp[translation.shift], 
    have : ∀ l, (p.rew ı[0 ⇝ t]).rew (λ x, ite (x < l) #x #(x + k)) = 
      (p.rew (λ x, ite (x < l + 1) #x #(x + k))).rew ı[0 ⇝ (t.rew (λ x, ite (x < l) #x #(x + k)))],
    { intros l, simp[formula.nested_rew], congr, funext x, cases x with x; simp[←nat.add_one],
      by_cases C : x < l; simp[C, show x + 1 + k = x + k + 1, by omega] },
    simp [this] },
  eq_reflexivity := by simp[translation.shift],
  eq_symmetry := by simp[translation.shift],
  eq_transitive := λ _ _ _, by simp[translation.shift, show ∀ l, 2 < l + 1 + 1 + 1, by omega], 
  function_ext := λ _ _ _ _, by simp[translation.shift],
  predicate_ext := λ _ _ _ _, by simp[translation.shift] }

end translation

namespace language_translation_coe
open language_translation
variables [σ : language_translation_coe L₁ L₂]
include σ

lemma provability_pow {T : theory L₁} {p : formula L₁} {i : ℕ} :
  T^i ⊢ p → (↑T : theory L₂)^i ⊢ ↑p :=
by { simp[← app_formula_extention_eq_coe i],
     exact translation.provability_pow σ.ltr.tr T p i 0 }

lemma provability {T : theory L₁} {p : formula L₁} :
  T ⊢ p → (↑T : theory L₂) ⊢ ↑p :=
translation.provability σ.ltr.tr T p 0

@[simp] lemma theory_coe_pow {T : theory L₁} {i : ℕ} :
  (↑T : theory L₂)^i = ↑(T^i) := 
begin
  ext p,
  simp[theory_sf_itr_eq, mem_coe_iff], split,
  { rintros ⟨p', ⟨p₁, mem, rfl⟩, rfl⟩,
    refine ⟨p₁^i, ⟨p₁, mem, rfl⟩, by simp⟩ },
  { rintros ⟨_, ⟨p₁, mem, rfl⟩, rfl⟩, 
    refine ⟨p₁, ⟨p₁, mem, rfl⟩, by simp⟩ } 
end

end language_translation_coe

instance : has_add language := ⟨λ L₁ L₂ : language.{u}, ⟨λ n, L₁.fn n ⊕ L₂.fn n, λ n, L₁.pr n ⊕ L₂.pr n⟩⟩ 

def sum {ι : Type*} (l : ι → language) : language := ⟨λ n, Σ i, (l i).fn n, λ n, Σ i, (l i).pr n⟩

namespace extention
open language_translation

def to_extention₁ : L₁ ↝ᴸ L₁ + L₂ := ⟨λ n f, sum.inl f, λ n p, sum.inl p⟩

instance ltr₁ : language_translation_coe L₁ (L₁ + L₂) :=
{ ltr := to_extention₁,
  fn_inj := λ n f g, sum.inl.inj,
  pr_inj := λ n f g, sum.inl.inj }

lemma coe_fn₁ {n} (f : L₁.fn n) : (↑f : (L₁ + L₂).fn n) = sum.inl f:= rfl

lemma coe_pr₁ {n} (r : L₁.pr n) : (↑r : (L₁ + L₂).pr n) = sum.inl r:= rfl

def to_extention₂ : L₂ ↝ᴸ L₁ + L₂ := ⟨λ n f, sum.inr f, λ n p, sum.inr p⟩

instance ltr₂ : language_translation_coe L₂ (L₁ + L₂) :=
{ ltr := to_extention₂,
  fn_inj := λ n f g, sum.inr.inj,
  pr_inj := λ n f g, sum.inr.inj }

lemma coe_fn₂ {n} (f : L₂.fn n) : (↑f : (L₁ + L₂).fn n) = sum.inr f:= rfl

lemma coe_pr₂ {n} (r : L₂.pr n) : (↑r : (L₁ + L₂).pr n) = sum.inr r:= rfl

variables {ι : Type*} (l : ι → language)

def to_extention (i : ι) : l i ↝ᴸ sum l :=
⟨λ n f, ⟨i, f⟩, λ n r, ⟨i, r⟩⟩

instance ltr (i : ι) : language_translation_coe (l i) (sum l) :=
{ ltr := to_extention l i,
  fn_inj := λ n f g, by simp[to_extention],
  pr_inj := λ n f g, by simp[to_extention] }

def to_extention_ss {s t : set ι} (ss : s ⊆ t) : sum (λ i : s, l i) ↝ᴸ sum (λ i : t, l i) :=
⟨λ n ⟨⟨i, hi⟩, f⟩, ⟨⟨i, ss hi⟩, f⟩, λ n ⟨⟨i, hi⟩, f⟩, ⟨⟨i, ss hi⟩, f⟩⟩

def ltr_ss {s t : set ι} (ss : s ⊆ t) : language_translation_coe (sum (λ i : s, l i)) (sum (λ i : t, l i)) :=
{ ltr := to_extention_ss l ss,
  fn_inj := λ n ⟨⟨i, pi⟩, f⟩ ⟨⟨j, pj⟩, g⟩, by { simp[to_extention_ss], rintros rfl, simp },
  pr_inj := λ n ⟨⟨i, pi⟩, f⟩ ⟨⟨j, pj⟩, g⟩, by { simp[to_extention_ss], rintros rfl, simp } }

def to_extention_subtype (s : set ι) : sum (λ i : s, l i) ↝ᴸ sum l :=
⟨λ n ⟨i, f⟩, ⟨i, f⟩, λ n ⟨i, r⟩, ⟨i, r⟩⟩

instance ltr_subtype (s : set ι) : language_translation_coe (sum (λ i : s, l i)) (sum l) :=
{ ltr := to_extention_subtype l s,
  fn_inj := λ n ⟨⟨i, pi⟩, f⟩ ⟨⟨j, pj⟩, g⟩, by { simp[to_extention_subtype], rintros rfl, simp },
  pr_inj := λ n ⟨⟨i, pi⟩, f⟩ ⟨⟨j, pj⟩, g⟩, by { simp[to_extention_subtype], rintros rfl, simp } }

@[simp] lemma to_extention_ss_subtype_consistence_term {s t : set ι} (ss : s ⊆ t) : ∀ (u : term (sum (λ i : s, l i))),
  ((to_extention_ss l ss).fun_term u : term (sum l)) = u
| #n                  := by simp
| (@term.app _ n f v) :=
  by { rcases f with ⟨⟨i, hi⟩, f⟩, simp[to_extention_ss],
       refine ⟨rfl, funext (λ i, to_extention_ss_subtype_consistence_term (v i))⟩}

@[simp] lemma to_extention_ss_subtype_consistence {s t : set ι} (ss : s ⊆ t) : ∀ (p : formula (sum (λ i : s, l i))),
  ((to_extention_ss l ss).fun_formula p : formula (sum l)) = p
| ⊤                                       := by simp
| (app r v)                               := by { simp, rcases r with ⟨⟨i, hi⟩, r⟩, simp[to_extention_ss], refl }
| ((t : term (sum (λ (i : s), l i))) ≃ u) := by simp
| (p ⟶ q)                                 := by simp[to_extention_ss_subtype_consistence p, to_extention_ss_subtype_consistence q]
| (⁻p)                                    := by simp[to_extention_ss_subtype_consistence p]
| (∏ p)                                   := by simp[to_extention_ss_subtype_consistence p]

lemma finite_retruct_term : ∀ (t : term (sum l)),
  ∃ (s : set ι) (t₀ : term (sum (λ i : s, l i))), set.finite s ∧ ↑t₀ = t
| #n                  := ⟨λ i, false, #n, set.finite_empty, rfl⟩
| (@term.app L n f v) := by { 
  have : ∃ (s : fin n → set ι),
    ∀ i, ∃ (t₀ : term (sum (λ (i : ↥(s i)), l ↑i))), (s i).finite ∧ ↑t₀ = v i,
    from classical.skolem.mp (λ i, finite_retruct_term (v i)),
  rcases this with ⟨s, hs⟩,
  rcases f with ⟨i₀, f⟩,
  let S := insert i₀ (⋃ (i : fin n), s i),
  refine ⟨S, _⟩,
  have ufinite : (⋃ i, s i).finite,
  { have : ∀ i, set.finite {j | s i j}, { intros i, rcases hs i with ⟨_, fin, _⟩, exact fin },
    have : (⋃ i, s i).finite, from set.finite_Union this, exact this },
  have mem_S : ∀ i, s i ⊆ S,
  { intros i, exact (set.subset_Union s i).trans (set.subset_insert i₀ _) },
  { have : ∃ (w : Π (i : fin n), term (sum (λ (j : ↥(s i)), l ↑j))), ∀ (i : fin n), (s i).finite ∧ ↑(w i) = v i,
      from classical.skolem.mp hs,
    rcases this with ⟨w, hw⟩,
    let w' : Π (i : fin n), term (sum (λ (j : S), l ↑j)) := λ i, (to_extention_ss l (mem_S i)).fun_term (w i),
    let f' : (sum (λ (i : S), l ↑i)).fn n := ⟨⟨i₀, set.mem_insert i₀ _⟩, f⟩,
    refine ⟨app f' w', set.finite.insert _ ufinite, _⟩,
    simp[f', w'], refine ⟨rfl, funext (λ i, (hw i).2)⟩ } }

lemma finite_retruct : ∀ (p : formula (sum l)),
  ∃ (s : set ι) (p₀ : formula (sum (λ i : s, l i))), set.finite s ∧ ↑p₀ = p
| ⊤ := ⟨∅, ⊤, set.finite_empty, rfl⟩
| ((t : term (sum l)) ≃ u) := by { 
    rcases finite_retruct_term l t with ⟨s₁, t₁, hs₁, rfl⟩,
    rcases finite_retruct_term l u with ⟨s₂, t₂, hs₂, rfl⟩,
    let t₁' : term (sum (λ (i : s₁ ∪ s₂), l i)) := (to_extention_ss l (set.subset_union_left s₁ s₂)).fun_term t₁,
    let t₂' : term (sum (λ (i : s₁ ∪ s₂), l i)) := (to_extention_ss l (set.subset_union_right s₁ s₂)).fun_term t₂,
    refine ⟨s₁ ∪ s₂, t₁' ≃ t₂', set.finite.union hs₁ hs₂, by simp⟩ }
| (p ⟶ q) := by { 
    rcases finite_retruct p with ⟨s₁, p₁, hs₁, rfl⟩,
    rcases finite_retruct q with ⟨s₂, p₂, hs₂, rfl⟩,
    let p₁' : formula (sum (λ (i : s₁ ∪ s₂), l i)) := (to_extention_ss l (set.subset_union_left s₁ s₂)).fun_formula p₁,
    let p₂' : formula (sum (λ (i : s₁ ∪ s₂), l i)) := (to_extention_ss l (set.subset_union_right s₁ s₂)).fun_formula p₂,
    refine ⟨s₁ ∪ s₂, p₁' ⟶ p₂', set.finite.union hs₁ hs₂, by simp⟩ }
| (⁻p) := by { 
    rcases finite_retruct p with ⟨s, p, hs, rfl⟩,
    refine ⟨s, ⁻p, hs, by simp⟩ }
| (∏ p) := by { 
    rcases finite_retruct p with ⟨s, p, hs, rfl⟩,
    refine ⟨s, ∏ p, hs, by simp⟩ }
| (@formula.app L n r v) := by { 
    have : ∃ (s : fin n → set ι), ∀ (i : fin n), ∃ (t₀ : term (sum (λ (i : s i), l ↑i))), (s i).finite ∧ ↑t₀ = v i,
      from classical.skolem.mp (λ i, finite_retruct_term l (v i) : ∀ i, ∃ (s : set ι) t₀, s.finite ∧ ↑t₀ = v i),
    rcases this with ⟨s, hs⟩,
    rcases r with ⟨i₀, r⟩,
    let S := insert i₀ (⋃ (i : fin n), s i),
    refine ⟨S, _⟩,
    have ufinite : (⋃ i, s i).finite,
    { have : ∀ i, set.finite {j | s i j}, { intros i, rcases hs i with ⟨_, fin, _⟩, exact fin },
      have : (⋃ i, s i).finite, from set.finite_Union this, exact this },
    have mem_S : ∀ i, s i ⊆ S,
    { intros i, exact (set.subset_Union s i).trans (set.subset_insert i₀ _) },
    { have : ∃ (w : Π (i : fin n), term (sum (λ (j : ↥(s i)), l ↑j))), ∀ (i : fin n), (s i).finite ∧ ↑(w i) = v i,
        from classical.skolem.mp hs,
      rcases this with ⟨w, hw⟩,
      let w' : Π (i : fin n), term (sum (λ (j : S), l ↑j)) := λ i, (to_extention_ss l (mem_S i)).fun_term (w i),
      let r' : (sum (λ (i : S), l ↑i)).pr n := ⟨⟨i₀, set.mem_insert i₀ _⟩, r⟩,
      refine ⟨app r' w', set.finite.insert _ ufinite, _⟩,
      simp[r', w'], refine ⟨rfl, funext (λ i, (hw i).2)⟩ } }

def sum_to_add {ι : Type} [decidable_eq ι] (l : ι → language) {s : set ι} (i : ι) :
  sum (λ i : insert i s, l i) ↝ᴸ sum (λ i : s, l i) + l i :=
{ fn := λ n ⟨⟨j, mem_j⟩, f⟩, by { 
    simp at mem_j f, 
    by_cases C : j = i,
    { rw[C] at f, refine sum.inr f },
    { simp[C] at mem_j,
      refine sum.inl ⟨⟨j, mem_j⟩, f⟩ } },
  pr := λ n ⟨⟨j, mem_j⟩, r⟩, by { 
    simp at mem_j r, 
    by_cases C : j = i,
    { rw[C] at r, refine sum.inr r },
    { simp[C] at mem_j,
      refine sum.inl ⟨⟨j, mem_j⟩, r⟩ } } }

def add_to_sum {ι : Type} (l : ι → language) {s : set ι} (i : ι) :
  sum (λ i : s, l i) + l i ↝ᴸ sum (λ i : insert i s, l i) :=
{ fn := λ n f, by { rcases f with (⟨⟨j, mem_j⟩, f⟩ | f),
    { refine ⟨⟨j, set.mem_insert_of_mem i mem_j⟩, f⟩ },
    { refine ⟨⟨i, set.mem_insert i s⟩, f⟩ } },
  pr := λ n r, by { rcases r with (⟨⟨j, mem_j⟩, r⟩ | r),
    { refine ⟨⟨j, set.mem_insert_of_mem i mem_j⟩, r⟩ },
    { refine ⟨⟨i, set.mem_insert i s⟩, r⟩ } } }

end extention

def singleton_fn (m : ℕ) : language.{u} := ⟨λ n, if n = m then punit else pempty, λ n, pempty⟩

def symbol {m : ℕ} : (singleton_fn.{u} m).fn m := by { simp[singleton_fn]; simp[show (m = m) ↔ true, by simp], refine punit.star }

notation `sing` := singleton_fn 0

def const_right {L : language.{u}} : term (L + sing) := 
extention.to_extention₂.fun_term (@term.app sing 0 symbol finitary.nil : term sing)

def const_at_right {ι : Type u} {L : language.{u}} (i : ι) : term (L + sum (λ i : ι, singleton_fn.{u} 0)) :=
extention.to_extention₂.fun_term ((extention.to_extention (λ i : ι, singleton_fn.{u} 0) i).fun_term
  (@term.app sing 0 symbol finitary.nil : term (singleton_fn.{u} 0)))

notation `●ᴿ` := const_right

notation `●ᴿ[` i `]` := const_at_right i

namespace add_sing

@[simp] def fun_term : ℕ → term (L + sing) → term L
| k #n        := if n < k then #n else #(n + 1)
| k (app f v) := by { rcases f,
    refine app f (λ i, fun_term k (v i)),
    refine #k }

def tr_term : L + sing ↝ᵀ L :=
{ to_fun_chr := λ k n f v, by { rcases f, refine app f v, refine #k },
  to_fun     := fun_term,
  map_fn     := λ k n f v, by simp }

@[simp] def fun_formula : ℕ → formula (L + sing) → formula L
| k ⊤                           := ⊤
| k (app p v)                   := by { rcases p with (p | p), { refine app p (λ i, fun_term k (v i)) }, { refine ⊤ } }
| k ((t : term (L + sing)) ≃ u) := fun_term k t ≃ fun_term k u
| k (p ⟶ q)                     := fun_formula k p ⟶ fun_formula k q
| k (⁻p)                        := ⁻fun_formula k p
| k (∏ p)                       := ∏ fun_formula (k + 1) p

lemma fun_term_rew_iddiscard : ∀ (t : term (L + sing)) {k s : ℕ} (le : s ≤ k),
  (fun_term k t).rew ı-{s} = fun_term (k + 1) (t.rew ı-{s})
| (#n)                k s le := by { simp[discard, ı],
   have C_k : n < k ∨ k ≤ n, from lt_or_ge n k,
    rcases C_k with (C_k | C_k),
    { simp[C_k], by_cases C_s : n < s; simp[C_k, C_s, show n < k + 1, from nat.lt.step C_k] },
    { have le : s ≤ n, from le_trans le C_k,
      have : ¬n < k, from not_lt.mpr C_k,
      have : ¬n < s, from not_lt.mpr le,
      have : ¬n + 1 < s, from not_lt.mpr (le_add_right le),
      simp* } }
| (@term.app _ n f v) k s le := by { rcases f; simp[le],
    { funext i, exact fun_term_rew_iddiscard (v i) le } }

lemma fun_term_pow (t : term (L + sing)) (k : ℕ) :
  (fun_term k t)^1 = fun_term (k + 1) (t^1) :=
by { have : t^1 = t.rew ı-{0}, { simp[term.pow_eq, discard_0_eq_add_one] },
     have : ∀ t : term L, t^1 = t.rew ı-{0}, { simp[term.pow_eq, discard_0_eq_add_one] },
     simp[*, fun_term_rew_iddiscard] }

lemma fun_formula_rew_iddiscard : ∀ (p : formula (L + sing)) {k s : ℕ} (le : s ≤ k),
  (fun_formula k p).rew ı-{s} = fun_formula (k + 1) (p.rew ı-{s})
| ⊤                           k s le := by simp
| (app r v)                   k s le := by { rcases r; simp[le], { funext i, exact fun_term_rew_iddiscard (v i) le } }
| ((t : term (L + sing)) ≃ u) k s le := by { simp, simp[fun_term_rew_iddiscard _ le] }
| (p ⟶ q)                     k s le := by { simp, exact ⟨fun_formula_rew_iddiscard p le, fun_formula_rew_iddiscard q le⟩ }
| (⁻p)                        k s le := by { simp, exact fun_formula_rew_iddiscard p le }
| (∏ p)                       k s le := by { simp[id_discard_pow], exact fun_formula_rew_iddiscard p (add_le_add_right le 1) }

lemma fun_formula_pow (p : formula (L + sing)) (k : ℕ) :
  (fun_formula k p)^1 = fun_formula (k + 1) (p^1) :=
by { have : p^1 = p.rew ı-{0}, { simp[formula.pow_eq, discard_0_eq_add_one] },
     have : ∀ p : formula L, p^1 = p.rew ı-{0}, { simp[formula.pow_eq, discard_0_eq_add_one] },
     simp[*, fun_formula_rew_iddiscard] }

def tr : L + sing ↝ L :=
{ to_fun := fun_formula,
  map_verum := by simp,
  map_imply := by simp,
  map_neg := by simp,
  map_univ := by simp,
  map_pow := λ p i, by simp[fun_formula_pow] }

lemma fun_term_rew_subst (t₀ : term (L + sing)) : ∀ (t : term (L + sing)) {k s : ℕ} (le : s ≤ k),
  (fun_term (k + 1) t).rew ı[s ⇝ fun_term k t₀] = fun_term k (t.rew ı[s ⇝ t₀])
| (#n)      k s le := by { simp, have C : s < n ∨ s = n ∨ n < s, from trichotomous s n,
    rcases C with (C | rfl | C),
    { simp[C], cases n; simp[←nat.add_one], { simp at C, contradiction },
      { by_cases C' : n < k; simp[C', C], have : s < n + 1 + 1, from nat.lt.step C, simp[this] } },
    { have : s < k + 1, from nat.lt_succ_iff.mpr le, simp* },
    { have : s < k + 1, from nat.lt_succ_iff.mpr le, simp*,
      simp[show n < k, from gt_of_ge_of_gt le C, show n < k + 1, from lt_trans C this, C] } }
| (app f v) k s le := by { rcases f, { simp, funext i, exact fun_term_rew_subst (v i) le },
    { have : s < k + 1, from nat.lt_succ_iff.mpr le, simp* } }

lemma fun_formula_rew_subst : ∀ (t₀ : term (L + sing)) (p : formula (L + sing)) {k s : ℕ} (le : s ≤ k),
  (fun_formula (k + 1) p).rew ı[s ⇝ fun_term k t₀] = fun_formula k (p.rew ı[s ⇝ t₀])
| t₀ ⊤                           k s le := by simp
| t₀ (@formula.app _ n r v)      k s le := by { rcases r, { simp[fun_term_rew_subst t₀ _ le] }, { simp } }
| t₀ ((t : term (L + sing)) ≃ u) k s le := by { simp[fun_term_rew_subst t₀ _ le] }
| t₀ (p ⟶ q)                     k s le := by { simp, refine ⟨fun_formula_rew_subst t₀ p le, fun_formula_rew_subst t₀ q le⟩ }
| t₀ (⁻p)                        k s le := by { simp, refine fun_formula_rew_subst t₀ p le }
| t₀ (∏ p)                       k s le := by { simp[subst_pow, fun_term_pow], exact fun_formula_rew_subst (t₀^1) p (add_le_add_right le 1) }

lemma fun_formula_rew_subst0 (t₀ : term (L + sing)) (p : formula (L + sing)) (k : ℕ) :
  (fun_formula (k + 1) p).rew ı[0 ⇝ fun_term k t₀] = fun_formula k (p.rew ı[0 ⇝ t₀]) :=
fun_formula_rew_subst t₀ p (zero_le k)

lemma tr_app (k : ℕ) (p : formula (L + sing)) : tr k p = fun_formula k p := rfl

instance tr_conservative : (tr : L + sing ↝ L).conservative :=
{ ax := tr_theory tr,
  ax_ss := by { intros, refl },
  specialize := λ k p t T i, by simp[tr, ←fun_formula_rew_subst0],
  eq_reflexivity := by simp[tr],
  eq_symmetry := by simp[tr],
  eq_transitive := λ _ _ _, by simp[tr, translation.shift, show ∀ l, 2 < l + 1 + 1 + 1, by omega], 
  function_ext := λ k n f T i, by { cases f; simp[tr, eq_axiom4],
    { have : ∀ j : fin n, ↑j < k + i + 2 * n, { rintros ⟨j, hj⟩, simp, omega },
      have : ∀ j : fin n, n + ↑j < k + i + 2 * n, { rintros ⟨j, hj⟩, simp, omega },
      simp*, exact provable.function_ext f },
    { cases n; simp, { rcases f } } },
  predicate_ext := λ k n r T i, by { cases r; simp[tr, eq_axiom5],
    { have : ∀ j : fin n, ↑j < k + i + 2 * n, { rintros ⟨j, hj⟩, simp, omega },
      have : ∀ j : fin n, n + ↑j < k + i + 2 * n, { rintros ⟨j, hj⟩, simp, omega },
      simp*, exact provable.predicate_ext r },
    { cases n; simp, { rcases r } } } }


@[simp] lemma fun_term_const (k : ℕ) : fun_term k (●ᴿ : term (L + sing)) = #k := rfl

@[simp] lemma fun_term_coe : ∀ (t : term L) (k : ℕ),
  fun_term k ↑t = t.rew ı-{k}
| (#n) k := by { simp, by_cases C : n < k; simp[C], have : k ≤ n, exact not_lt.mp C, simp* }
| (@term.app _ n f v) k := by { simp, have : (f : (L + sing).fn n) = sum.inl f, from rfl, rw this, simp,
    funext i, exact fun_term_coe (v i) k }

@[simp] lemma fun_formula_coe : ∀ (p : formula L) (k : ℕ),
  fun_formula k ↑p = p.rew ı-{k}
| ⊤                      k := by simp
| (@formula.app _ n r v) k := by { simp, have : (r : (L + sing).pr n) = sum.inl r, from rfl, rw this }
| ((t : term L) ≃ u)     k := by simp
| (p ⟶ q)                k := by { simp, exact ⟨fun_formula_coe p k, fun_formula_coe q k⟩ }
| (⁻p)                   k := by { simp, exact fun_formula_coe p k }
| (∏ p)                  k := by { simp[id_discard_pow], exact fun_formula_coe p (k + 1) }

lemma ax_app (k : ℕ) (T : theory L) : conservative.ax (tr : L + sing ↝ L) k ↑T = (λ p, rew ı-{k} p) '' T :=
begin
  have : conservative.ax tr k (↑T : theory (L+sing)) = tr_theory tr k ↑T, { refl},
  rw this,
  ext p,
  simp[tr, tr_theory], refine ⟨λ h, _, λ h, _⟩,
  { rcases h with ⟨p, ⟨p, hp, rfl⟩, rfl⟩,
    refine ⟨p, hp, _⟩, simp[language_translation_coe.app_formula_extention_eq_coe] },
  { rcases h with ⟨p, hp, rfl⟩,
    refine ⟨p, ⟨p, hp, rfl⟩, by simp⟩ }
end

@[simp] lemma ax_app_0 (T : theory L) : conservative.ax (tr : L + sing ↝ L) 0 ↑T = T^1 :=
by { simp[ax_app], simp[discard_0_eq_add_one, ←formula.pow_eq, pow_eq_image] }

open classical_logic axiomatic_classical_logic axiomatic_classical_logic' Herbrand Lindenbaum

theorem provable_iff (T : theory L) (p : formula L) :
  (↑T : theory (L + sing)) ⊢ rew ı[0 ⇝ ●ᴿ] p ↔ T ⊢ ∏ p :=
⟨λ h, begin
  have : T^1 ⊢ p,
  { have := translation.provability tr _ _ 0 h,
    simp[tr_app, ←fun_formula_rew_subst0, tr] at this,
    have eq_id : (λ x, rew ı[0 ⇝ #0] (ı-{1} x) : ℕ → term L) = ı,
    { funext x, cases x; simp[show ∀ x, 1 ≤ x + 1, from λ x, le_add_self] },
    simp[formula.nested_rew, eq_id] at this, exact this },
  exact provable.generalize this
end, λ h, begin
  have : (↑T : theory (L + sing)) ⊢ ↑∏ p, from language_translation_coe.provability h,
  simp at this, exact this ⊚ ●ᴿ
end⟩ 

lemma consistency_iff (T : theory L) (p : formula L) (k : ℕ) :
  theory.consistent (T +{∐ p}) ↔ theory.consistent (↑T +{rew ı[0 ⇝ ●ᴿ] p} : theory (L + sing)) :=
begin
  simp[theory.consistent_iff_bot], simp[deduction],
  have lmm₁ : (↑T : theory (L + sing)) ⊢ rew ı[0 ⇝ ●ᴿ] ↑p ⟶ ⊥ ↔ (↑T : theory (L + sing)) ⊢ rew ı[0 ⇝ ●ᴿ] ↑(⁻p),
  { simp[eq_top_of_provable_0] },
  have lmm₂ : T ⊢ ∐ p ⟶ ⊥ ↔ T ⊢ ∏ (⁻p),
  { simp[eq_top_of_provable_0, ←prenex_ex_neg] },
  rw[lmm₁, lmm₂, provable_iff]
end

end add_sing

namespace completeness 

@[reducible] def henkin_lang (L : language.{u}) : language.{u} := L + sum (λ i : formula L, singleton_fn.{u} 0)

def henkin_axiom (p : formula L) : formula (henkin_lang L) :=
(∐ p) ⟶ rew ı[0 ⇝ ●ᴿ[p]] ↑p

lemma consistence_of_con (T : theory L) (con : T.consistent) :
  theory.consistent ((↑T : theory (henkin_lang L)) ∪ (set.range henkin_axiom)) :=
begin
  
end

def henkin_language_aux (L : language.{u}) : ℕ → language.{u}
| 0       := L
| (n + 1) := sum (λ i : formula (henkin_language_aux n), singleton_fn.{u} 0)

def henkin_language (L : language.{u}) := sum (henkin_language_aux L)

end completeness

#check 0/--
def to_predicate (L : language.{u}) : language.{u} :=
{ fn := λ _, pempty, pr := λ n, match n with | 0 := L.pr 0 | (n + 1) := L.pr (n + 1) ⊕ L.fn n end }

instance (L : language.{u}) : predicate L.to_predicate :=
{ fun_empty := λ n, ⟨λ f, by cases f⟩ }

def pr.to_predicate : Π {n : ℕ} (p : L.pr n), L.to_predicate.pr n
| 0       p := p
| (n + 1) p := sum.inl p

def fn.to_predicate {n} (f : L.fn n) : L.to_predicate.pr (n + 1) := sum.inr f

namespace predicate
local infix ` ≃ₚ `:50 := ((≃) : term L.to_predicate → term L.to_predicate → formula L.to_predicate)

@[simp] def term_to_pformula : ℕ → term L → ℕ → formula L.to_predicate
| X (#x)                k := #X ≃ₚ #(x + k)
| X (@term.app _ n f v) k :=
    ∏[n] ((⋀ i, term_to_pformula i (v i) (n + k)) ⟶ formula.app f.to_predicate (#(X + n) ::ᶠ ##))

@[simp] def formula_to_pformula : formula L → formula L.to_predicate
| ⊤                      := ⊤
| (@formula.app _ n p v) := ∏[n] ((⋀ i, term_to_pformula i (v i) n) ⟶ formula.app p.to_predicate ##)
| (t ≃₀ u)               := ∏ ∏ (term_to_pformula 0 t 2 ⊓ term_to_pformula 1 t 2 ⟶ (#0 ≃ₚ #1))
| (p ⟶ q)                := formula_to_pformula p ⟶ formula_to_pformula q
| (⁻p)                    := ⁻formula_to_pformula p
| (∏ p)                  := ∏ formula_to_pformula p

lemma term_to_pformula_rew_var : ∀ (t : term L) (k) (X) (lt : X < k) (s : ℕ → ℕ),
  (term_to_pformula X t k).rew ((λ x, #(s x))^k) = term_to_pformula X (t.rew (λ x, #(s x))) k
| (#n)                k X h s := by simp[h]
| (@term.app _ n f v) k X h s := by { simp[h],
  rw[rewriting_sf_itr.pow_add, show k + n = n + k, from add_comm _ _],
  congr, funext i,
  exact term_to_pformula_rew_var (v i) (n + k) i (nat.lt_add_right _ n k i.property) s }

lemma formula_to_pformula_rew_var : ∀ (p : formula L) (s : ℕ → ℕ),
  (formula_to_pformula p).rew (λ x, #(s x)) = formula_to_pformula (p.rew (λ x, #(s x)))
| ⊤                      s := by simp
| (@formula.app _ n r v) s := by simp[term_to_pformula_rew_var]
| (t ≃₀ u)               s := by simp[rewriting_sf_itr.pow_add, term_to_pformula_rew_var]
| (p ⟶ q)                s := by simp[formula_to_pformula_rew_var p, formula_to_pformula_rew_var q]
| (⁻p)                   s := by simp[formula_to_pformula_rew_var p]
| (∏ p)                  s := by { simp,
    have eqn₁ : ((λ x, #(s x))^1 : ℕ → term L) = (λ x, #(if x = 0 then 0 else s (x - 1) + 1)),
    { funext x, cases x; simp },
    have eqn₂ : ((λ x, #(s x))^1 : ℕ → term L.to_predicate) = (λ x, #(if x = 0 then 0 else s (x - 1) + 1)),
    { funext x, cases x; simp },
    simp[fal_pow, eqn₁, eqn₂, formula_to_pformula_rew_var p] }

inductive axm : theory L.to_predicate
| trans : ∀ k X Y t, axm (term_to_pformula X t k ⟶ term_to_pformula Y t k ⟶ (#X ≃ₚ #Y))

lemma term_to_pformula_rew : ∀
  (t : term L) (k) (X) (lt : X < k) {n} (s : finitary (term L) n)
  (T : theory L.to_predicate),
  T ⊢ term_to_pformula X (t.rew (λ x, if h : x < n then s ⟨x, h⟩ else #x)) k ⟷
      (∏[n] (⋀ i, term_to_pformula i (s i) n) ⟶ term_to_pformula (X + n) t k)
| (#x)                k X h n s T := by { simp[h],
    by_cases C : x < n; simp[C],
    {  }
     }
| (@term.app _ m f v) k X h n s T := by { simp[h],
  rw[rewriting_sf_itr.pow_add, show k + n = n + k, from add_comm _ _],
  congr, funext i,
  exact term_to_pformula_rew_var (v i) (n + k) i (nat.lt_add_right _ n k i.property) s }

lemma formula_to_pformula_rew_var : ∀ (p : formula L) (s : ℕ → ℕ),
  (formula_to_pformula p).rew (λ x, #(s x)) = formula_to_pformula (p.rew (λ x, #(s x)))
| ⊤                      s := by simp
| (@formula.app _ n r v) s := by simp[term_to_pformula_rew_var]
| (t ≃₀ u)               s := by simp[rewriting_sf_itr.pow_add, term_to_pformula_rew_var]
| (p ⟶ q)                s := by simp[formula_to_pformula_rew_var p, formula_to_pformula_rew_var q]
| (⁻p)                   s := by simp[formula_to_pformula_rew_var p]
| (∏ p)                  s := by { simp,
    have eqn₁ : ((λ x, #(s x))^1 : ℕ → term L) = (λ x, #(if x = 0 then 0 else s (x - 1) + 1)),
    { funext x, cases x; simp },
    have eqn₂ : ((λ x, #(s x))^1 : ℕ → term L.to_predicate) = (λ x, #(if x = 0 then 0 else s (x - 1) + 1)),
    { funext x, cases x; simp },
    simp[fal_pow, eqn₁, eqn₂, formula_to_pformula_rew_var p] }

variables (L)

def predicatize : translation L L.to_predicate :=
{ to_fun := λ _, formula_to_pformula,
  map_verum := by simp,
  map_imply := by simp,
  map_neg   := by simp,
  map_univ  := by simp,
  map_pow   := λ p k, eq.symm (formula_to_pformula_rew_var p (λ x, x + 1)) }

instance predicatize_conservative : (predicatize L).conservative :=
{ ax := λ k T, tr_theory (predicatize L) k T,
  ax_ss := by { intros, refl },
  specialize := λ k p t T, by { simp, } }


end predicate
end language

end fopl
