import deduction lindenbaum

universes u v

namespace fopl
open formula term

variables {L L₁ L₂ L₃ : language.{u}}
local infix ` ≃₀ `:50 := ((≃) : term L → term L → formula L)
local infix ` ≃₁ `:50 := ((≃) : term L₁ → term L₁ → formula L₁)
local infix ` ≃₂ `:50 := ((≃) : term L₂ → term L₂ → formula L₂)

namespace language

protected def pempty : language.{u} := ⟨λ n, pempty, λ n, pempty⟩

instance : has_emptyc (language.{u}) := ⟨fopl.language.pempty⟩

@[simp] lemma pempty_fn_def (n) : (∅ : language.{u}).fn n = pempty := rfl

@[simp] lemma pempty_pr_def (n) : (∅ : language.{u}).pr n = pempty := rfl

structure language_translation (L₁ : language) (L₂ : language) :=
(fn : Π n, L₁.fn n → L₂.fn n)
(pr : Π n, L₁.pr n → L₂.pr n)

infix ` ↝ᴸ `:25 := language_translation

structure language_equiv (L₁ : language) (L₂ : language) :=
(ltr : L₁ ↝ᴸ L₂)
(inv : L₂ ↝ᴸ L₁)
(left_inv_fn : ∀ n, function.left_inverse (inv.fn n) (ltr.fn n))
(left_inv_pr : ∀ n, function.left_inverse (inv.pr n) (ltr.pr n))
(right_inv_fn : ∀ n, function.left_inverse (inv.fn n) (ltr.fn n))
(right_inv_pr : ∀ n, function.left_inverse (inv.pr n) (ltr.pr n))

infix ` ↭ᴸ `:25 := language_equiv

class language_translation_coe (L₁ : language) (L₂ : language) :=
(ltr : L₁ ↝ᴸ L₂)
(fn_inj : ∀ {n} (f g : L₁.fn n), ltr.fn n f = ltr.fn n g → f = g)
(pr_inj : ∀ {n} (p q : L₁.pr n), ltr.pr n p = ltr.pr n q → p = q)

class synonym (L₁ L₂ : language) 
(leq : L₁ ↭ᴸ L₂)

structure formula_homomorphism (L₁ : language) (L₂ : language.{v}) :=
(to_fun : ℕ → formula L₁ → formula L₂)
(map_verum : ∀ i, to_fun i ⊤ = ⊤)
(map_imply : ∀ (p q : formula L₁) (i : ℕ), to_fun i (p ⟶ q) = to_fun i p ⟶ to_fun i q)
(map_neg : ∀ (p : formula L₁) (i), to_fun i (⁻p) = ⁻to_fun i p)
(map_univ : ∀ (p : formula L₁) (i), to_fun i (∏ p) = ∏ to_fun (i + 1) p)

structure translation (L₁ : language) (L₂ : language.{v}) extends formula_homomorphism L₁ L₂ :=
(map_pow : ∀ (p : formula L₁) (i), to_fun (i + 1) (p^1) = (to_fun i p)^1)

infix ` ↝ `:25 := translation

instance {L₁ L₂ : language} : has_coe_to_fun (formula_homomorphism L₁ L₂) (λ _, ℕ → formula L₁ → formula L₂) :=
⟨@formula_homomorphism.to_fun L₁ L₂⟩

instance {L₁ L₂ : language} : has_coe_to_fun (translation L₁ L₂) (λ _, ℕ → formula L₁ → formula L₂) :=
⟨λ τ, @formula_homomorphism.to_fun L₁ L₂ τ.to_formula_homomorphism⟩

structure term_homomorphism (L₁ : language) (L₂ : language) :=
(to_fun_chr : ℕ → Π {n}, L₁.fn n → finitary (term L₂) n → term L₂)
(to_fun : ℕ → term L₁ → term L₂)
(map_fn : Π (k : ℕ) {n} (f : L₁.fn n) (v : finitary (term L₁) n),
  to_fun k (term.app f v) = to_fun_chr k f (λ i, to_fun k (v i)))

infix ` ↝ᵀ `:25 := term_homomorphism

instance {L₁ L₂ : language} : has_coe_to_fun (term_homomorphism L₁ L₂) (λ _, ℕ → term L₁ → term L₂) :=
⟨λ τ, τ.to_fun⟩

structure term_formula_translation (L₁ : language) (L₂ : language) :=
(p : translation L₁ L₂)
(t : ℕ → term L₁ → term L₂)
(chr : Π {n} (r : L₁.pr n), L₂.pr n)
(equal : ∀ (t₁ t₂ : term L₁) (k), p k (t₁ ≃ t₂ : formula L₁) = (t k t₁ ≃ t k t₂))
(app : ∀ (k) {n} (r : L₁.pr n) (v), p k (app r v) = app (chr r) (λ i, t k (v i)))
(map_pow : ∀ u s, t (s + 1) (u^1) = (t s u)^1)

def tr_theory {L₁ L₂ : language} (τ : translation L₁ L₂) (i) (T : theory L₁) : theory L₂ := τ i '' T

@[simp] lemma mem_theory_tr_of_mem {L₁ L₂ : language} {τ : translation L₁ L₂} {i}
  {T : theory L₁} {p} (mem : p ∈ T) : τ i p ∈ tr_theory τ i T :=
⟨p, mem, rfl⟩

class translation.conservative (τ : translation L₁ L₂) :=
(ax : ℕ → theory L₁ → theory L₂ := tr_theory τ)
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

namespace formula_homonorphism
variables (τ : formula_homomorphism L₁ L₂) (i : ℕ)

@[simp] lemma map_verum' :
  τ i ⊤ = ⊤ := τ.map_verum i

@[simp] lemma map_imply' (p q : formula L₁) :
  τ i (p ⟶ q) = τ i p ⟶ τ i q := τ.map_imply p q i

@[simp] lemma map_neg' (p : formula L₁) :
  τ i (⁻p) = ⁻τ i p := τ.map_neg p i

@[simp] lemma map_univ' (p : formula L₁) :
  τ i (∏ p) = ∏ τ (i + 1) p := τ.map_univ p i

lemma map_pow'_aux
  (H_pr : ∀ {n} (r : L₁.pr n) (v) (i s k : ℕ) (le : s ≤ i),
    τ (i + k) ((app r v).rew ((λ x, #(x + k))^s)) = (τ i (app r v)).rew ((λ x, #(x + k))^s))
  (H_eq : ∀ (t u : term L₁) (i s k : ℕ) (le : s ≤ i),
    τ (i + k) ((t ≃₁ u).rew ((λ x, #(x + k))^s)) = (τ i (t ≃₁ u)).rew ((λ x, #(x + k))^s))
  (p : formula L₁) (i s k : ℕ) (hs : s ≤ i) :
  τ (i + k) (p.rew ((λ x, #(x + k))^s)) = (τ i p).rew ((λ x, #(x + k))^s) :=
begin
  induction p generalizing i s k,
  case app : n r v { exact H_pr r v i s k hs },
  case equal : t u i s k { exact H_eq t u i s k hs },
  case verum { simp },  
  case imply : p q IH_p IH_q { simp, exact ⟨IH_p i s k hs, IH_q i s k hs⟩ },
  case neg : p IH { simp, exact IH i s k hs},
  case fal : p IH { simp[rewriting_sf_itr.pow_add, show i + k + 1 = i + 1 + k, by omega],
  exact IH (i + 1) (s + 1) k (by simp[hs]) }
end

def mk_translation
  (H_pr : ∀ {n} (r : L₁.pr n) (v) (i s k : ℕ) (le : s ≤ i),
    τ (i + k) ((app r v).rew ((λ x, #(x + k))^s)) = (τ i (app r v)).rew ((λ x, #(x + k))^s))
  (H_eq : ∀ (t u : term L₁) (i s k : ℕ) (le : s ≤ i),
    τ (i + k) ((t ≃₁ u).rew ((λ x, #(x + k))^s)) = (τ i (t ≃₁ u)).rew ((λ x, #(x + k))^s)) : translation L₁ L₂ :=
{  map_pow := λ p i, by { simp,
    have : τ (i + 1) (p.rew (λ x, #(x + 1))) = rew (λ x, #(x + 1)) (τ i p),
    { have := map_pow'_aux τ (@H_pr) (@H_eq) p i 0 1 (by simp), simp at this, exact this },
    simp[formula.pow_eq], exact this },  ..τ }

end formula_homonorphism

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

def comp : translation L₂ L₃ → translation L₁ L₂ → translation L₁ L₃ := λ τ₂₃ τ₁₂,
{ to_fun := λ i, τ₂₃ i ∘ τ₁₂ i,
  map_verum := by simp, map_imply := by simp, map_neg := by simp,
  map_univ := by simp, map_pow := by simp[map_pow'] }

end translation


namespace term_homomorphism

@[simp] lemma translation.map_imply' (τ : term_homomorphism L₁ L₂) {n} (f : L₁.fn n) (v : finitary (term L₁) n) (k) :
  τ k (term.app f v) = τ.to_fun_chr k f (λ i, τ k (v i)) := τ.map_fn k f v

@[simp] lemma app_eq (fc) (f) (map_fn) (t : term L₁) (i) :
  ({to_fun_chr := fc, to_fun := f, map_fn := map_fn} : term_homomorphism L₁ L₂) i t = f i t := rfl

@[simp] def mk_fun_of_atom {L₁ L₂ : language} 
  (to_fun_chr : ℕ → Π {n}, L₁.fn n → finitary (term L₂) n → term L₂) : ℕ → term L₁ → term L₂
| _ #n        := #n
| k (app f v) := to_fun_chr k f (λ i, mk_fun_of_atom k (v i))

@[simp] def mk_of_atom {L₁ L₂ : language}
  (to_fun_chr : ℕ → Π {n}, L₁.fn n → finitary (term L₂) n → term L₂) : term_homomorphism L₁ L₂ :=
{ to_fun_chr := @to_fun_chr,
  to_fun := mk_fun_of_atom @to_fun_chr,
  map_fn := by simp }

end term_homomorphism

namespace term_formula_translation
open translation
variables (τ : term_formula_translation L₁ L₂) (k : ℕ)

@[simp] lemma map_equal (t₁ t₂ : term L₁) : τ.p k (t₁ ≃ t₂ : formula L₁) = (τ.t k t₁ ≃ τ.t k t₂) := τ.equal t₁ t₂ k

@[simp] lemma map_app {n} (r : L₁.pr n) (v) :
  τ.p k (formula.app r v) = formula.app (τ.chr r) (λ i, τ.t k (v i)) := τ.app k r v

lemma map_pow' (t : term L₁) (k s : ℕ) :
  τ.t (k + s) (t^s) = (τ.t k t)^s := 
by { induction s with s IH; simp[←nat.add_one, ←add_assoc],
     have : τ.t (k + s + 1) ((t ^ s) ^ 1) = τ.t (k + s) (t ^ s) ^ 1, from map_pow τ (t^s) (k + s), 
     simp[IH, term.pow_add] at this, exact this }

lemma tr_subst_of_subst
  (H : ∀ (t u : term L₁) (s m : ℕ) (le : m ≤ s), τ.t s (t.rew ı[m ⇝ u]) = (τ.t (s + 1) t).rew ı[m ⇝ τ.t s u])
  (p : formula L₁) (t : term L₁) (s m : ℕ) (le : m ≤ s) :
  τ.p s (p.rew ı[m ⇝ t]) = (τ.p (s + 1) p).rew ı[m ⇝ τ.t s t] :=
begin
  induction p generalizing t s m,
  case app : n r v { simp, funext i, exact H (v i) t s m le },
  case equal : u₁ u₂ { simp, exact ⟨H u₁ t s m le, H u₂ t s m le⟩ },
  case verum { simp },
  case imply : p q IH_p IH_q { simp, exact ⟨IH_p t s m le, IH_q t s m le⟩ },
  case neg : p IH { simp, exact IH t s m le },
  case fal : p IH { simp[subst_pow, ←map_pow'], exact IH (t^1) (s + 1) (m + 1) (by simp[le]) },
end

open provable axiomatic_classical_logic axiomatic_classical_logic'

def conservative_of
  (H : ∀ (t u : term L₁) (s m) (le : m ≤ s), τ.t s (t.rew ı[m ⇝ u]) = (τ.t (s + 1) t).rew ı[m ⇝ τ.t s u])
  (function_ext : ∀ (s) {n} (f : L₁.fn n) (T : theory L₁) (k : ℕ),
    (tr_theory τ.p s T)^k ⊢ τ.p (s + k) (eq_axiom4 f))
  (predicate_ext : ∀ (s) {n} (r : L₁.pr n) (T : theory L₁) (k : ℕ),
    (tr_theory τ.p s T)^k ⊢ τ.p (s + k) (eq_axiom5 r))
   : conservative τ.p :=
{ ax_ss := λ _ _, by refl,
  specialize := λ s p t T k, by simp[tr_subst_of_subst τ H],
  eq_reflexivity := λ s T k, by { simp, refine generalize (by simp) },
  eq_symmetry := λ s T k, by { simp, refine generalize (generalize _),
    have : ⤊⤊(tr_theory τ.p s T ^ k) ⊢ _, from eq_symmetry ⊚ (τ.t (s + k + 1 + 1) #1) ⊚ τ.t (s + k + 1 + 1) #0,
    simp at this, simp at this, exact this },
  eq_transitive := λ s T k,
   by { simp, refine generalize (generalize (generalize _)),
        have : ⤊⤊⤊(tr_theory τ.p s T ^ k) ⊢ _, from eq_transitivity ⊚ τ.t (s + k + 1 + 1 + 1) #2 ⊚ τ.t (s + k + 1 + 1 + 1) #1 ⊚ τ.t (s + k + 1 + 1 + 1) #0,
        simp at this, simp at this, exact this },
  function_ext := λ s n f T k, by { exact function_ext s f T k },
  predicate_ext := λ s n f T k, by { exact predicate_ext s f T k } }


end term_formula_translation

namespace language_translation

lemma mk.eta : Π (τ : L₁ ↝ᴸ L₂), ({fn := τ.fn, pr := τ.pr} : L₁ ↝ᴸ L₂) = τ
| ⟨fn, pr⟩ := rfl

lemma eq_iff {τ σ : L₁ ↝ᴸ L₂} : τ = σ ↔ (∀ n f, τ.fn n f = σ.fn n f) ∧ (∀ n r, τ.pr n r = σ.pr n r) :=
by { rw[←mk.eta τ, ←mk.eta σ], simp, split,
     { rintros ⟨eq_fn, eq_pr⟩, simp* }, { rintros ⟨hfn, hpr⟩, refine ⟨_, _⟩; { funext, simp* } } }

@[ext] lemma ext {τ σ : L₁ ↝ᴸ L₂} (eq_fn : ∀ n f, τ.fn n f = σ.fn n f) (eq_pr : ∀ n r, τ.pr n r = σ.pr n r) : τ = σ :=
by { simp[eq_iff], exact ⟨eq_fn, eq_pr⟩ }

def from_empty : ∅ ↝ᴸ L :=
{ fn := λ n f, by rcases f, pr := λ n r, by rcases r }

def one (L : language) : L ↝ᴸ L :=
{ fn := λ n, id, pr := λ n, id }

instance : has_one (L ↝ᴸ L) := ⟨one L⟩ 

def comp : L₂ ↝ᴸ L₃ → L₁ ↝ᴸ L₂ →  L₁ ↝ᴸ L₃ := λ τ₂₃ τ₁₂,
{ fn := λ n, (τ₂₃.fn n) ∘ (τ₁₂.fn n),
  pr := λ n, (τ₂₃.pr n) ∘ (τ₁₂.pr n) }

variables (τ : L₁ ↝ᴸ L₂)

@[simp] def fun_t : term L₁ → term L₂
| #n        := #n
| (app f v) := app (τ.fn _ f) (λ i, fun_t (v i))

def tr_term : term_homomorphism L₁ L₂ :=
{ to_fun_chr := λ k n f v, app (τ.fn _ f) v,
  to_fun     := λ k, τ.fun_t,
  map_fn     := λ k n f v, by simp }

@[simp] def fun_p : formula L₁ → formula L₂
| ⊤                    := ⊤
| (app p v)            := app (τ.pr _ p) (λ i, fun_t τ (v i))
| ((t : term L₁) ≃ u)  := fun_t τ t ≃ fun_t τ u
| (p ⟶ q)              := fun_p p ⟶ fun_p q
| (⁻p)                 := ⁻fun_p p
| (∏ (p : formula L₁)) := ∏ fun_p p

lemma fun_t_rew_var : ∀ (t : term L₁) (s : ℕ → ℕ),
  (fun_t τ t).rew (λ x, #(s x)) = fun_t τ (t.rew (λ x, #(s x)))
| (#n)                s := by simp
| (@term.app _ n f v) s := by { simp, funext i, exact @fun_t_rew_var (v i) _ }

lemma fun_p_rew_var : ∀ (p : formula L₁) (s : ℕ → ℕ),
  (fun_p τ p).rew (λ x, #(s x)) = fun_p τ (p.rew (λ x, #(s x)))
| ⊤                      _ := by simp
| (@formula.app _ n r v) s := by { simp, funext i, simp[fun_t_rew_var] }
| ((t : term L₁) ≃ u)    s := by simp[fun_t_rew_var]
| (p ⟶ q)                s := by simp[fun_p_rew_var p, fun_p_rew_var q]
| (⁻p)                   s := by simp[fun_p_rew_var p]
| (∏ (p : formula L₁))   s := by { 
    have eqn₁ : ((λ x, #(s x))^1 : ℕ → term L₁) = (λ x, #(if x = 0 then 0 else s (x - 1) + 1)),
    { funext x, cases x; simp },
    have eqn₂ : ((λ x, #(s x))^1 : ℕ → term L₂) = (λ x, #(if x = 0 then 0 else s (x - 1) + 1)),
    { funext x, cases x; simp },
    simp[fal_pow, eqn₁, eqn₂, fun_p_rew_var p] }

def tr : translation L₁ L₂ :=
{ to_fun := λ _, τ.fun_p,
  map_verum := by simp,
  map_imply := by simp,
  map_neg := by simp,
  map_univ := by simp,
  map_pow := λ p i, eq.symm (τ.fun_p_rew_var p (λ x, x + 1)) }

lemma tr_term_app_eq (k) (t) : 
  τ.tr_term k t = τ.fun_t t := by refl

lemma tr_app_eq (k) (p) : 
  τ.tr k p = τ.fun_p p := by refl

@[simp] lemma tr_term_to_fun_chr_app_eq (k) {n} (f : L₁.fn n) (v : finitary (term L₂) n) :
  τ.tr_term.to_fun_chr k f v = app (τ.fn _ f) v := rfl

@[simp] lemma fun_t_pow (t : term L₁) (i : ℕ) :
  (τ.fun_t (t^i) : term L₂) = (τ.fun_t t)^i :=
eq.symm (τ.fun_t_rew_var t (λ x, x + i))

@[simp] lemma fun_p_pow (p : formula L₁) (i : ℕ) :
  (τ.fun_p (p^i) : formula L₂) = (τ.fun_p p)^i := 
eq.symm (τ.fun_p_rew_var p (λ x, x + i))

lemma fun_t_rew : ∀ (t : term L₁) (s : ℕ → term L₁),
  τ.fun_t (t.rew s) = (τ.fun_t t).rew (λ x, τ.fun_t (s x))
| (#x)           s := by simp
| (term.app p v) s := by simp[λ i, fun_t_rew (v i)]

lemma fun_p_rew : ∀ (p : formula L₁) (s : ℕ → term L₁),
  τ.fun_p (p.rew s) = (τ.fun_p p).rew (λ x, τ.fun_t (s x))
| ⊤                 s := by simp
| (formula.app f v) s := by simp[fun_t_rew]
| (t ≃₁ u)          s := by simp[fun_t_rew]
| (p ⟶ q)           s := by simp[fun_p_rew p, fun_p_rew q]
| (⁻p)              s := by simp[fun_p_rew p]
| (∏ p)             s := by
    { simp[fun_p_rew p, rewriting_sf_itr.pow_eq'], congr, funext x, cases x; simp }

lemma fun_t_inversion_of_le {t₁ : term L₁} {u₂ : term L₂} (le : u₂ ≤ τ.fun_t t₁) :
  ∃ (u₁ : term L₁) (le : u₁ ≤ t₁), u₂ = τ.fun_t u₁ :=
begin
  induction t₁ generalizing u₂,
  case var : n { simp at le, refine ⟨#n, by simp[le]⟩ },
  case app : n f v IH
  { rcases le_iff_lt_or_eq.mp le with (lt | rfl),
    { simp at lt, rcases lt with ⟨i, le⟩, rcases IH i le with ⟨t, t_le', rfl⟩, refine ⟨t, le_trans t_le' (by simp), rfl⟩ },
    { refine ⟨app f v, by refl, rfl⟩ } }
end

lemma fun_p_inversion_of_le {p₁ : formula L₁} {q₂ : formula L₂} (le : q₂ ≤ τ.fun_p p₁) :
  ∃ (q₁ : formula L₁) (le : q₁ ≤ p₁), q₂ = τ.fun_p q₁ :=
begin
  induction p₁ generalizing q₂,
  case app : n r v { simp at le, refine ⟨app r v, by simp[le]⟩ },
  case equal : t u { simp at le, refine ⟨t ≃₁ u, by simp[le]⟩ },
  case verum { simp at le, refine ⟨⊤, by simp[le]⟩ },
  case imply : p q IH_p IH_q
  { rcases le_iff_lt_or_eq.mp le with (lt | rfl),
    { simp at lt, rcases lt with (le | le),
      { rcases IH_p le with ⟨q₁, le', rfl⟩, refine ⟨q₁, le_trans le' (le_of_lt (by simp)), rfl⟩ },
      { rcases IH_q le with ⟨q₁, le', rfl⟩, refine ⟨q₁, le_trans le' (le_of_lt (by simp)), rfl⟩ } },
    { refine ⟨p ⟶ q, by simp⟩ } },
  case neg : p IH
  { rcases le_iff_lt_or_eq.mp le with (lt | rfl),
    { simp at lt, rcases IH lt with ⟨q₁, le', rfl⟩, refine ⟨q₁, le_trans le' (le_of_lt (by simp)), rfl⟩ },
    { refine ⟨⁻p, by simp⟩ } },
  case fal : p IH
  { rcases le_iff_lt_or_eq.mp le with (lt | rfl),
    { simp at lt, rcases IH lt with ⟨q₁, le', rfl⟩, refine ⟨q₁, le_trans le' (le_of_lt (by simp)), rfl⟩ },
    { refine ⟨∏ p, by simp⟩ } },
end

lemma fun_p_inversion_of_mem {p₁ : formula L₁} {t₂ : term L₂} (mem : t₂ ∈ τ.fun_p p₁) :
  ∃ (t₁ : term L₁) (mem : t₁ ∈ p₁), t₂ = τ.fun_t t₁ :=
begin
  induction p₁ generalizing t₂,
  case app : n r v
  { simp at mem, rcases mem with ⟨i, le⟩,
    rcases fun_t_inversion_of_le τ le with ⟨t₁, le', rfl⟩, refine ⟨t₁, by simp; exact ⟨i, le'⟩, rfl⟩ },
  case equal : t u
  { simp at mem, rcases mem with (le | le),
    { rcases fun_t_inversion_of_le τ le with ⟨t₁, le', rfl⟩, refine ⟨t₁, by simp[le'], rfl⟩ },
    { rcases fun_t_inversion_of_le τ le with ⟨t₁, le', rfl⟩, refine ⟨t₁, by simp[le'], rfl⟩ } },
  case verum { simp at mem, contradiction },
  case imply : p q IH_p IH_q
  { simp at mem, rcases mem with (mem | mem),
    { rcases IH_p mem with ⟨t', mem', rfl⟩, refine ⟨t', by simp[mem'], rfl⟩ },
    { rcases IH_q mem with ⟨t', mem', rfl⟩, refine ⟨t', by simp[mem'], rfl⟩ } },
  case neg : p IH { simp at mem ⊢, rcases IH mem with ⟨t', mem', rfl⟩, refine ⟨t', mem', rfl⟩ },
  case fal : p IH { simp at mem ⊢, rcases IH mem with ⟨t', mem', rfl⟩, refine ⟨t', mem', rfl⟩ }
end

variables (τ₁₂ σ₁₂ : L₁ ↝ᴸ L₂) (τ₂₃ : L₂ ↝ᴸ L₃) {L₄ : language.{u}} (τ₃₄ : L₃ ↝ᴸ L₄)

@[simp] lemma one_fn {n} (f : L.fn n) : fn 1 n f = f := rfl

@[simp] lemma one_pr {n} (r : L.pr n) : pr 1 n r = r := rfl

@[simp] lemma comp_fn {n} (f : L₁.fn n) : (τ₂₃.comp τ₁₂).fn n f = τ₂₃.fn n (τ₁₂.fn n f) := rfl

@[simp] lemma comp_pr {n} (r : L₁.pr n) : (τ₂₃.comp τ₁₂).pr n r = τ₂₃.pr n (τ₁₂.pr n r) := rfl

@[simp] lemma one_fun_t (t : term L) : fun_t 1 t = t :=
by induction t; simp*

@[simp] lemma one_fun_p (p : formula L) : fun_p 1 p = p :=
by induction p; simp*

lemma comp_fun_t : (τ₂₃.comp τ₁₂).fun_t = τ₂₃.fun_t ∘ τ₁₂.fun_t :=
by funext t; induction t; simp*

lemma comp_fun_p  : (τ₂₃.comp τ₁₂).fun_p = τ₂₃.fun_p ∘ τ₁₂.fun_p :=
by funext p; induction p; simp[*, comp_fun_t]

@[simp] lemma comp_one : τ.comp 1 = τ := by ext; simp

@[simp] lemma one_comp : comp 1 τ = τ := by ext; simp

@[simp] lemma comp_assoc : (τ₃₄.comp τ₂₃).comp τ₁₂ = τ₃₄.comp (τ₂₃.comp τ₁₂) := by ext; simp

end language_translation

namespace language_translation_coe
open language_translation

instance : language_translation_coe ∅ L :=
{ltr := from_empty, fn_inj := λ n f g, by rcases f, pr_inj := λ n r s, by rcases r }

variables [σ : language_translation_coe L₁ L₂]
include σ

instance {n} : has_coe (L₁.fn n) (L₂.fn n) := ⟨λ n, σ.ltr.fn _ n⟩

instance {n} : has_coe (L₁.pr n) (L₂.pr n) := ⟨λ n, σ.ltr.pr _ n⟩

instance : has_coe (term L₁) (term L₂) := ⟨σ.ltr.fun_t⟩

lemma app_term_extension_eq (t : term L₁) (i : ℕ) :
  (σ.ltr.tr_term i t : term L₂) = ↑t := rfl

instance : has_coe (formula L₁) (formula L₂) := ⟨σ.ltr.fun_p⟩

lemma app_formula_extension_eq (p : formula L₁) (i : ℕ) :
  (σ.ltr.tr i p : formula L₂) = ↑p := rfl

instance : has_coe (theory L₁) (theory L₂) := ⟨tr_theory σ.ltr.tr 0⟩

instance [has_zero_symbol L₁] : has_zero_symbol L₂ := ⟨σ.ltr.fn _ has_zero_symbol.zero⟩

instance [has_succ_symbol L₁] : has_succ_symbol L₂ := ⟨σ.ltr.fn _ has_succ_symbol.succ⟩

instance [has_add_symbol L₁] : has_add_symbol L₂ := ⟨σ.ltr.fn _ has_add_symbol.add⟩

instance [has_mul_symbol L₁] : has_mul_symbol L₂ := ⟨σ.ltr.fn _ has_mul_symbol.mul⟩

instance [has_le_symbol L₁] : has_le_symbol L₂ := ⟨σ.ltr.pr _ has_le_symbol.le⟩

instance [has_mem_symbol L₁] : has_mem_symbol L₂ := ⟨σ.ltr.pr _ has_mem_symbol.mem⟩

lemma app_formula_extension_eq_coe (k) (p : formula L₁) :
  (σ.ltr.tr : translation L₁ L₂) k p = ↑p := rfl

lemma app_term_extension_eq_coe (k) (t : term L₁) :
  (σ.ltr.tr_term : term_homomorphism L₁ L₂) k t = ↑t := rfl

@[simp] lemma add_tr_v1_var (n) : ((#n : term L₁) : term L₂) = #n := rfl

lemma add_tr_v1_app {n} (f : L₁.fn n) (v : finitary (term L₁) n) :
  ((❨f❩ v : term L₁) : term L₂) = ❨σ.ltr.fn _ f❩ (λ i, (v i)) := by refl

@[simp] lemma coe_tr_v1_zero [has_zero_symbol L₁] :
  ((0 : term L₁) : term L₂) = 0 := by { unfold has_zero.zero has_zero_symbol.zero,
   simp [←app_term_extension_eq_coe 0] }

@[simp] lemma coe_tr_v1_succ [has_succ_symbol L₁] (t : term L₁) :
  ((Succ t : term L₁) : term L₂) = Succ t :=
by { unfold has_succ.succ, simp [←app_term_extension_eq_coe 0],
     split, { refl }, { ext; simp } }

@[simp] lemma coe_tr_v1_numeral [has_zero_symbol L₁] [has_succ_symbol L₁] (n : ℕ) :
  ((n˙ : term L₁) : term L₂) = n˙ :=
by induction n; simp[*, numeral]

@[simp] lemma coe_tr_v1_add [has_add_symbol L₁] (t u : term L₁) :
  ((t + u : term L₁) : term L₂) = t + u :=
by { unfold has_add.add, simp [←app_term_extension_eq_coe 0],
     split, { refl }, { ext; simp } }

@[simp] lemma coe_tr_v1_mul [has_mul_symbol L₁] (t u : term L₁) :
  ((t * u : term L₁) : term L₂) = t * u :=
by { unfold has_mul.mul, simp [←app_term_extension_eq_coe 0],
     split, { refl }, { ext; simp } }

@[simp] lemma coe_tr_v1_le [has_le_symbol L₁] (t u : term L₁) :
  ((t ≼ u : formula L₁) : formula L₂) = ((t : term L₂) ≼ u) :=
by { unfold has_preceq.preceq, simp [←app_formula_extension_eq_coe 0, tr_app_eq], 
     split, { refl }, { ext; simp; refl } }

@[simp] lemma coe_tr_v1_mem [has_mem_symbol L₁] (t u : term L₁) :
  ((t ∊ u : formula L₁) : formula L₂) = ((t : term L₂) ∊ u) :=
by { unfold has_elem.elem, simp [←app_formula_extension_eq_coe 0, tr_app_eq],
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
by simp [tr_term_app_eq, ←app_term_extension_eq_coe 0]

@[simp] lemma coe_pow_formula (p : formula L₁) (i : ℕ) :
  (↑(p^i) : formula L₂) = (↑p)^i := 
by simp [tr_app_eq, ←app_formula_extension_eq_coe 0]

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

@[simp] lemma theory_coe_empty : (↑(∅ : theory L₁) : theory L₂) = ∅ :=
set.ext (λ p, by unfold_coes; simp[tr_theory])

@[simp] lemma theory_coe_union (T U : theory L₁) : (↑(T ∪ U) : theory L₂) = ↑T ∪ ↑U :=
set.ext (λ p, by { unfold_coes, simp[tr_theory], split,
  { rintros ⟨p, (mem_p | mem_p), rfl⟩,
    refine or.inl ⟨p, mem_p, rfl⟩,
    refine or.inr ⟨p, mem_p, rfl⟩ },
  { rintros (⟨p, mem_p, rfl⟩ | ⟨p, mem_p, rfl⟩),
    refine ⟨p, or.inl mem_p, rfl⟩,
    refine ⟨p, or.inr mem_p, rfl⟩ } })

@[simp] lemma theory_coe_sf (T : theory L₁) : (↑⤊T : theory L₂) = ⤊(↑T : theory L₂) :=
set.ext (λ p, by { unfold_coes,simp[tr_theory, theory.sf], refine ⟨_, _⟩,
  { rintros ⟨_, ⟨q₁, mem_q₁, rfl⟩, rfl⟩, refine ⟨q₁, mem_q₁, by simp[app_formula_extension_eq_coe]⟩ },
  { rintros ⟨p₁, mem_p₁, rfl⟩, refine ⟨p₁^1, ⟨p₁, mem_p₁, rfl⟩, by simp[app_formula_extension_eq_coe]⟩ } })

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

lemma theory_mem_coe_pow_iff {p : formula L₂} {T : theory L₁} {i : ℕ} :
  p ∈ (↑(T^i) : theory L₂) ↔ ∃ p' ∈ T, p = (↑p' : formula L₂)^i :=
begin
  rw [←theory_coe_pow, theory_sf_itr_eq], simp, split,
  { rintros ⟨q, q_mem, rfl⟩, rcases q_mem with ⟨q, q_mem, rfl⟩, refine ⟨q, q_mem, rfl⟩ },
  { rintros ⟨q, q_mem, rfl⟩, refine ⟨↑q, by simp[q_mem]⟩ }
end 

lemma destruct_of_eq_imply {p : formula L₁} {q r : formula L₂} (h : ↑p = q ⟶ r) :
  ∃ p₁ p₂, p = p₁ ⟶ p₂ :=
begin
  rcases p; try { simp at h, contradiction },
  { simp at h, rcases h with ⟨rfl, rfl⟩, simp }
end

lemma destruct_of_eq_neg {p : formula L₁} {q : formula L₂} (h : ↑p = ⁻q) :
  ∃ p₁, p = ⁻p₁ :=
begin
  rcases p; try { simp at h, contradiction },
  { simp at h, rcases h with ⟨rfl, rfl⟩, simp }
end

lemma fun_t_inversion_of_le {t₁ : term L₁} {u₂ : term L₂} (le : u₂ ≤ ↑t₁) :
  ∃ (u₁ : term L₁) (le : u₁ ≤ t₁), u₂ = ↑u₁ := fun_t_inversion_of_le _ le

lemma fun_p_inversion_of_le {p₁ : formula L₁} {q₂ : formula L₂} (le : q₂ ≤ ↑p₁) :
  ∃ (q₁ : formula L₁) (le : q₁ ≤ p₁), q₂ = ↑q₁ := fun_p_inversion_of_le _ le

lemma fun_p_inversion_of_mem {p₁ : formula L₁} {t₂ : term L₂} (mem : t₂ ∈ (↑p₁ : formula L₂)) :
  ∃ (t₁ : term L₁) (mem : t₁ ∈ p₁), t₂ = ↑t₁ := fun_p_inversion_of_mem _ mem

end language_translation_coe

namespace language_translation
variables (τ : L₁ ↝ᴸ L₂)

instance conservative : τ.tr.conservative :=
{ ax := λ k T, tr_theory τ.tr k T,
  ax_ss := by { intros, refl },
  specialize := λ k p t T i, by {
    have : (λ (x : ℕ), τ.fun_t (ı[0 ⇝ t] x)) = ı[0 ⇝ τ.fun_t t],
    { funext x, cases x; simp },
    simp[tr_app_eq, fun_p_rew, this] },
  eq_reflexivity := by simp[tr_app_eq],
  eq_symmetry := by simp[tr_app_eq],
  eq_transitive := by simp[tr_app_eq],
  function_ext := λ k n f T i, by { simp[eq_axiom4], simp[tr_app_eq],
    exact (show _ ⊢ eq_axiom4 (τ.fn _ f), by simp) },
  predicate_ext := λ k n f T i, by { simp[eq_axiom5], simp[tr_app_eq],
    exact (show _ ⊢ eq_axiom5 (τ.pr _ f), by simp) } }

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
  refine provable.rec'_on h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
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

namespace language_translation
open language_translation
variables (τ : L₁ ↝ᴸ L₂)

lemma provability_pow {T : theory L₁} {p : formula L₁} {i : ℕ} :
  T^i ⊢ p → (τ.fun_p '' T)^i ⊢ τ.fun_p p :=
translation.provability_pow τ.tr T p i 0

lemma provability {T : theory L₁} {p : formula L₁} :
  T ⊢ p → τ.fun_p '' T ⊢ τ.fun_p p :=
translation.provability τ.tr T p 0

lemma consistency (T : theory L₁) : 
  theory.consistent (τ.fun_p '' T) → T.consistent :=
translation.consistency τ.tr T 0

end language_translation

namespace language_translation_coe
open language_translation
variables [σ : language_translation_coe L₁ L₂]
include σ

lemma provability_pow {T : theory L₁} {p : formula L₁} {i : ℕ} :
  T^i ⊢ p → (↑T : theory L₂)^i ⊢ ↑p :=
translation.provability_pow σ.ltr.tr T p i 0

lemma provability {T : theory L₁} {p : formula L₁} :
  T ⊢ p → (↑T : theory L₂) ⊢ ↑p :=
translation.provability σ.ltr.tr T p 0

lemma consistency (T : theory L₁) : 
  theory.consistent (↑T : theory L₂) → T.consistent :=
translation.consistency σ.ltr.tr T 0

end language_translation_coe

--------------------------------------------------------------------------------

instance : has_add language := ⟨λ L₁ L₂ : language.{u}, ⟨λ n, L₁.fn n ⊕ L₂.fn n, λ n, L₁.pr n ⊕ L₂.pr n⟩⟩ 

def direct_sum {ι : Type*} (l : ι → language) : language := ⟨λ n, Σ i, (l i).fn n, λ n, Σ i, (l i).pr n⟩

def consts (α : Type u) : language.{u} := ⟨λ n, match n with | 0 := α | (n + 1) := pempty end, λ n, pempty⟩

namespace consts
variables {α : Type u}

def c (a : α) : (consts α).fn 0 := a

instance : has_coe α (term (consts α)) := ⟨λ a, term.app (consts.c a) finitary.nil⟩

lemma coe_def (a : α) : (a : term (consts α)) = term.app (consts.c a) finitary.nil := rfl

@[simp] lemma arity_eq_0 (a : α) : (a : term (consts α)).arity = 0 := by simp[coe_def]

end consts

@[simp] lemma sum_fn_def {ι : Type*} (l : ι → language) (n : ℕ) : (direct_sum l).fn n = Σ i, (l i).fn n := rfl

@[simp] lemma sum_pr_def {ι : Type*} (l : ι → language) (n : ℕ) : (direct_sum l).pr n = Σ i, (l i).pr n := rfl

namespace extension
open language_translation language_translation_coe

def add_left : L₁ ↝ᴸ L₁ + L₂ := ⟨λ n f, sum.inl f, λ n p, sum.inl p⟩

instance ltr₁ : language_translation_coe L₁ (L₁ + L₂) :=
{ ltr := add_left,
  fn_inj := λ n f g, sum.inl.inj,
  pr_inj := λ n f g, sum.inl.inj }

lemma coe_fn₁ {n} (f : L₁.fn n) : (↑f : (L₁ + L₂).fn n) = sum.inl f:= rfl

lemma coe_pr₁ {n} (r : L₁.pr n) : (↑r : (L₁ + L₂).pr n) = sum.inl r:= rfl

lemma add_left_fn_to_coe {n} (f : L₁.fn n) : (add_left.fn _ f : (L₁ + L₂).fn n) = f := rfl

lemma add_left_pr_to_coe {n} (r : L₁.pr n) : (add_left.pr _ r : (L₁ + L₂).pr n) = r := rfl

def add_right : L₂ ↝ᴸ L₁ + L₂ := ⟨λ n f, sum.inr f, λ n p, sum.inr p⟩

instance ltr₂ : language_translation_coe L₂ (L₁ + L₂) :=
{ ltr := add_right,
  fn_inj := λ n f g, sum.inr.inj,
  pr_inj := λ n f g, sum.inr.inj }

lemma coe_fn₂ {n} (f : L₂.fn n) : (↑f : (L₁ + L₂).fn n) = sum.inr f:= rfl

lemma coe_pr₂ {n} (r : L₂.pr n) : (↑r : (L₁ + L₂).pr n) = sum.inr r:= rfl

lemma add_right_fn_to_coe {n} (f : L₂.fn n) : (add_right.fn _ f : (L₁ + L₂).fn n) = f := rfl

lemma add_right_pr_to_coe {n} (r : L₂.pr n) : (add_right.pr _ r : (L₁ + L₂).pr n) = r := rfl

class sublanguage (L₀ : language.{u}) (L : language.{u}) :=
(map_fn : Π {n}, L.fn n → L₀.fn n)
(map_pr : Π {n}, L.pr n → L₀.pr n)

variables {ι : Type*} (l : ι → language)

def to_extension (i : ι) : l i ↝ᴸ direct_sum l :=
⟨λ n f, ⟨i, f⟩, λ n r, ⟨i, r⟩⟩

instance ltr (i : ι) : language_translation_coe (l i) (direct_sum l) :=
{ ltr := to_extension l i,
  fn_inj := λ n f g, by simp[to_extension],
  pr_inj := λ n f g, by simp[to_extension] }

def ext_ss {s t : set ι} (ss : s ⊆ t) : direct_sum (λ i : s, l i) ↝ᴸ direct_sum (λ i : t, l i) :=
⟨λ n ⟨⟨i, hi⟩, f⟩, ⟨⟨i, ss hi⟩, f⟩, λ n ⟨⟨i, hi⟩, f⟩, ⟨⟨i, ss hi⟩, f⟩⟩

def ltr_ss {s t : set ι} (ss : s ⊆ t) : language_translation_coe (direct_sum (λ i : s, l i)) (direct_sum (λ i : t, l i)) :=
{ ltr := ext_ss l ss,
  fn_inj := λ n ⟨⟨i, pi⟩, f⟩ ⟨⟨j, pj⟩, g⟩, by { simp[ext_ss], rintros rfl, simp },
  pr_inj := λ n ⟨⟨i, pi⟩, f⟩ ⟨⟨j, pj⟩, g⟩, by { simp[ext_ss], rintros rfl, simp } }

def to_extension_subtype (s : set ι) : direct_sum (λ i : s, l i) ↝ᴸ direct_sum l :=
⟨λ n ⟨i, f⟩, ⟨i, f⟩, λ n ⟨i, r⟩, ⟨i, r⟩⟩

instance ltr_subtype (s : set ι) : language_translation_coe (direct_sum (λ i : s, l i)) (direct_sum l) :=
{ ltr := to_extension_subtype l s,
  fn_inj := λ n ⟨⟨i, pi⟩, f⟩ ⟨⟨j, pj⟩, g⟩, by { simp[to_extension_subtype], rintros rfl, simp },
  pr_inj := λ n ⟨⟨i, pi⟩, f⟩ ⟨⟨j, pj⟩, g⟩, by { simp[to_extension_subtype], rintros rfl, simp } }

@[simp] lemma ext_ss_subtype_consistence_term {s t : set ι} (ss : s ⊆ t) : ∀ (u : term (direct_sum (λ i : s, l i))),
  ((ext_ss l ss).fun_t u : term (direct_sum l)) = u
| #n                  := by simp
| (@term.app _ n f v) :=
  by { rcases f with ⟨⟨i, hi⟩, f⟩, simp[ext_ss],
       refine ⟨rfl, funext (λ i, ext_ss_subtype_consistence_term (v i))⟩}

@[simp] lemma ext_ss_subtype_consistence {s t : set ι} (ss : s ⊆ t) :
  ∀ (p : formula (direct_sum (λ i : s, l i))), ((ext_ss l ss).fun_p p : formula (direct_sum l)) = p
| ⊤                                       := by simp
| (app r v)                               := by { simp, rcases r with ⟨⟨i, hi⟩, r⟩, simp[ext_ss], refl }
| ((t : term (direct_sum (λ (i : s), l i))) ≃ u) := by simp
| (p ⟶ q)                                 := by simp[ext_ss_subtype_consistence p, ext_ss_subtype_consistence q]
| (⁻p)                                    := by simp[ext_ss_subtype_consistence p]
| (∏ p)                                   := by simp[ext_ss_subtype_consistence p]

@[simp] lemma theory_ext_ss_subtype_consistence {s t : set ι} (ss : s ⊆ t)
  (T : theory (direct_sum (λ i : s, l i))) :
  (↑((ext_ss l ss).fun_p '' T) : theory (direct_sum l)) = ↑T :=
set.ext (λ p, by { unfold_coes, simp[tr_theory, app_formula_extension_eq_coe] })

end extension

namespace language_translation

variables {L₁} {L₂} {L₃} {L₄ : language.{u}}

def add (τ : L₁ ↝ᴸ L₂) (σ : L₃ ↝ᴸ L₄) : L₁ + L₃ ↝ᴸ L₂ + L₄ :=
{ fn := λ n f, by { rcases f, { exact sum.inl (τ.fn _ f) }, { exact sum.inr (σ.fn _ f) } },
  pr := λ n r, by { rcases r, { exact sum.inl (τ.pr _ r) }, { exact sum.inr (σ.pr _ r) } } }

section
variables (τ : L₁ ↝ᴸ L₂) (σ : L₃ ↝ᴸ L₄)

@[simp] lemma add_fnl {n} (f : L₁.fn n) : (τ.add σ).fn n ↑f = ↑(τ.fn n f) := rfl
@[simp] lemma add_prl {n} (r : L₁.pr n) : (τ.add σ).pr n ↑r = ↑(τ.pr n r) := rfl
@[simp] lemma add_fnr {n} (f : L₃.fn n) : (τ.add σ).fn n ↑f = ↑(σ.fn n f) := rfl
@[simp] lemma add_prr {n} (r : L₃.pr n) : (τ.add σ).pr n ↑r = ↑(σ.pr n r) := rfl

end

def sum (τ : L₁ ↝ᴸ L₂) (σ : L₃ ↝ᴸ L₂) : L₁ + L₃ ↝ᴸ L₂ :=
{ fn := λ n f, by { rcases f, { refine τ.fn n f }, { refine σ.fn n f } },
  pr := λ n r, by { rcases r, { refine τ.pr n r }, { refine σ.pr n r } } }

section
variables (τ : L₁ ↝ᴸ L₂) (σ : L₃ ↝ᴸ L₂)

@[simp] lemma sum_fnl {n} (f : L₁.fn n) : (τ.sum σ).fn n ↑f = (τ.fn n f) := rfl
@[simp] lemma sum_prl {n} (r : L₁.pr n) : (τ.sum σ).pr n ↑r = (τ.pr n r) := rfl
@[simp] lemma sum_fnr {n} (f : L₃.fn n) : (τ.sum σ).fn n ↑f = (σ.fn n f) := rfl
@[simp] lemma sum_prr {n} (r : L₃.pr n) : (τ.sum σ).pr n ↑r = (σ.pr n r) := rfl

end

variables (L₁ L₂ L₃)

def add_comm' : L₁ + L₂ ↝ᴸ L₂ + L₁ :=
{ fn := λ n f, by { rcases f, { refine sum.inr f }, { refine sum.inl f } },
  pr := λ n r, by { rcases r, { refine sum.inr r }, { refine sum.inl r } } }

@[simp] lemma add_comm'_fnl {n} (f : L₁.fn n) : (add_comm' L₁ L₂).fn n ↑f = f := rfl
@[simp] lemma add_comm'_prl {n} (r : L₁.pr n) : (add_comm' L₁ L₂).pr n ↑r = r := rfl
@[simp] lemma add_comm'_fnr {n} (f : L₂.fn n) : (add_comm' L₁ L₂).fn n ↑f = f := rfl
@[simp] lemma add_comm'_prr {n} (r : L₂.pr n) : (add_comm' L₁ L₂).pr n ↑r = r := rfl

def add_assoc' : L₁ + L₂ + L₃ ↝ᴸ L₁ + (L₂ + L₃) :=
{ fn := λ n f, by { rcases f, { rcases f, { refine sum.inl f }, { refine sum.inr (sum.inl f) } }, { refine sum.inr (sum.inr f) } },
  pr := λ n r, by { rcases r, { rcases r, { refine sum.inl r }, { refine sum.inr (sum.inl r) } }, { refine sum.inr (sum.inr r) } }   }

@[simp] lemma add_assoc'_fn₁ {n} (f : L₁.fn n) : (add_assoc' L₁ L₂ L₃).fn n (↑(↑f : (L₁ + L₂).fn n)) = (↑f : (L₁ + (L₂ + L₃)).fn n) := rfl
@[simp] lemma add_assoc'_fn₂ {n} (f : L₂.fn n) : (add_assoc' L₁ L₂ L₃).fn n (↑(↑f : (L₁ + L₂).fn n)) = ↑(↑f : (L₂ + L₃).fn n) := rfl
@[simp] lemma add_assoc'_fn₃ {n} (f : L₃.fn n) : (add_assoc' L₁ L₂ L₃).fn n (↑f : (L₁ + L₂ + L₃).fn n) = ↑(↑f : (L₂ + L₃).fn n) := rfl
@[simp] lemma add_assoc'_pr₁ {n} (r : L₁.pr n) : (add_assoc' L₁ L₂ L₃).pr n (↑(↑r : (L₁ + L₂).pr n)) = (↑r : (L₁ + (L₂ + L₃)).pr n) := rfl
@[simp] lemma add_assoc'_pr₂ {n} (r : L₂.pr n) : (add_assoc' L₁ L₂ L₃).pr n (↑(↑r : (L₁ + L₂).pr n)) = ↑(↑r : (L₂ + L₃).pr n) := rfl
@[simp] lemma add_assoc'_pr₃ {n} (r : L₃.pr n) : (add_assoc' L₁ L₂ L₃).pr n (↑r : (L₁ + L₂ + L₃).pr n) = ↑(↑r : (L₂ + L₃).pr n) := rfl

def add_assoc'_inv : L₁ + (L₂ + L₃) ↝ᴸ L₁ + L₂ + L₃ :=
{ fn := λ n f, by { rcases f, { refine sum.inl f }, { rcases f, { refine sum.inl (sum.inr f) }, { refine sum.inr f } } },
  pr := λ n r, by { rcases r, { refine sum.inl r }, { rcases r, { refine sum.inl (sum.inr r) }, { refine sum.inr r } } } }

@[simp] lemma add_assoc'_inv_fn₁ {n} (f : L₁.fn n) : (add_assoc'_inv L₁ L₂ L₃).fn n (↑f : (L₁ + (L₂ + L₃)).fn n) = ↑(↑f : (L₁ + L₂).fn n) := rfl
@[simp] lemma add_assoc'_inv_fn₂ {n} (f : L₂.fn n) : (add_assoc'_inv L₁ L₂ L₃).fn n (↑(↑f : (L₂ + L₃).fn n)) = ↑(↑f : (L₁ + L₂).fn n) := rfl
@[simp] lemma add_assoc'_inv_fn₃ {n} (f : L₃.fn n) : (add_assoc'_inv L₁ L₂ L₃).fn n ↑(↑f : (L₂ + L₃).fn n) = (↑f : (L₁ + L₂ + L₃).fn n) := rfl
@[simp] lemma add_assoc'_inv_pr₁ {n} (r : L₁.pr n) : (add_assoc'_inv L₁ L₂ L₃).pr n (↑r : (L₁ + (L₂ + L₃)).pr n) = (↑(↑r : (L₁ + L₂).pr n)) := rfl
@[simp] lemma add_assoc'_inv_pr₂ {n} (r : L₂.pr n) : (add_assoc'_inv L₁ L₂ L₃).pr n ↑(↑r : (L₂ + L₃).pr n) = (↑(↑r : (L₁ + L₂).pr n)) := rfl
@[simp] lemma add_assoc'_inv_pr₃ {n} (r : L₃.pr n) : (add_assoc'_inv L₁ L₂ L₃).pr n ↑(↑r : (L₂ + L₃).pr n) = (↑r : (L₁ + L₂ + L₃).pr n) := rfl

variables {α β : Type*}

def consts_of_fun (f : α → β) : consts α ↝ᴸ consts β :=
{ fn := λ n c, by { rcases n, { exact f c }, { rcases c } },
  pr := λ n r, by { rcases r } }

@[simp] lemma consts_fn (f : α → β) (c : (consts α).fn 0) : (consts_of_fun f).fn 0 c = f c := rfl

end language_translation

namespace language_equiv
open language_translation extension
variables (L₁ L₂ L₃)

def add_comm' : L₁ + L₂ ↭ᴸ L₂ + L₁ :=
{ ltr := add_comm' L₁ L₂, inv := add_comm' L₂ L₁,
  left_inv_fn := λ n f, by rcases f; simp[←coe_fn₁, ←coe_fn₂],
  left_inv_pr := λ n r, by rcases r; simp[←coe_pr₁, ←coe_pr₂],
  right_inv_fn := λ n f, by rcases f; simp[←coe_fn₁, ←coe_fn₂],
  right_inv_pr := λ n r, by rcases r; simp[←coe_pr₁, ←coe_pr₂] }

def add_assoc' : L₁ + L₂ + L₃ ↭ᴸ L₁ + (L₂ + L₃) :=
{ ltr := add_assoc' L₁ L₂ L₃, inv := add_assoc'_inv L₁ L₂ L₃,
  left_inv_fn := λ n f, by { rcases f; simp[←coe_fn₁, ←coe_fn₂], rcases f; simp[←coe_fn₁, ←coe_fn₂] },
  left_inv_pr := λ n r, by { rcases r; simp[←coe_pr₁, ←coe_pr₂], rcases r; simp[←coe_pr₁, ←coe_pr₂] },
  right_inv_fn := λ n f, by { rcases f; simp[←coe_fn₁, ←coe_fn₂], rcases f; simp[←coe_fn₁, ←coe_fn₂] },
  right_inv_pr := λ n r, by { rcases r; simp[←coe_pr₁, ←coe_pr₂], rcases r; simp[←coe_pr₁, ←coe_pr₂] } }

end language_equiv

namespace language_translation
open extension

def seq (l : ℕ → language.{u}) := Π n, l n ↝ᴸ l (n + 1)

variables {l : ℕ → language.{u}}


structure seq_limit (l : ℕ → language.{u}) (L : language):=
(seq : seq l)
(to_limit : Π n, l n ↝ᴸ L)
(commutes : ∀ n, (to_limit (n + 1)).comp (seq n) = to_limit n)
(rank_fn : Π {n} (f : L.fn n), ℕ)
(rank_pr : Π {n} (r : L.pr n), ℕ)
(fn : Π {n} (f : L.fn n), (l $ rank_fn f).fn n)
(pr : Π {n} (r : L.pr n), (l $ rank_pr r).pr n)
(fn_spec : ∀ {n} (f : L.fn n), (to_limit _).fn _ (fn f) = f)
(pr_spec : ∀ {n} (r : L.pr n), (to_limit _).pr _ (pr r) = r)

namespace seq_limit
variables {L} (s : seq_limit l L)
include s

def seqs : Π n m, l n ↝ᴸ l (n + m)
| n 0       := (1 : l n ↝ᴸ l n)
| n (m + 1) := (s.seq (n + m)).comp (seqs n m)

def seqs_le {n m} (h : n ≤ m) : l n ↝ᴸ l m :=
by { rw [show m = n + (m - n), by omega], exact s.seqs n (m - n) }

@[simp] lemma to_limit_seq_commutes' (n : ℕ) : (s.to_limit (n + 1)).comp (s.seq n) = s.to_limit n := s.commutes n

@[simp] lemma to_limit_seqs_commuts (n m : ℕ) : (s.to_limit (n + m)).comp (s.seqs n m) = s.to_limit n :=
by { induction m with m IH; simp[seqs], { refl },
  { suffices : (s.to_limit (n + m + 1)).comp ((s.seq (n + m)).comp (s.seqs n m)) = s.to_limit n, by simpa,
    rw ← comp_assoc, simp[IH] } }

lemma seqs_le_commuts {n m : ℕ} (le : n ≤ m) : (s.to_limit m).comp (s.seqs_le le) = s.to_limit n :=
by { have := s.to_limit_seqs_commuts n (m - n), rw ←this, congr; simp[show n + (m - n) = m, by omega, seqs_le] }

@[simp] lemma seqs_le_commuts'_fn {n m : ℕ} (le : n ≤ m) {k} (f : (l n).fn k) :
  (s.to_limit m).fn _ ((s.seqs_le le).fn _ f) = (s.to_limit n).fn _ f :=
by { rw[←s.seqs_le_commuts le], simp }

@[simp] lemma seqs_le_commuts'_pr {n m : ℕ} (le : n ≤ m) {k} (r : (l n).pr k) :
  (s.to_limit m).pr _ ((s.seqs_le le).pr _ r) = (s.to_limit n).pr _ r :=
by { rw[←s.seqs_le_commuts le], simp }

@[simp] lemma seqs_le_commuts'_t {n m : ℕ} (le : n ≤ m) (t : term (l n)) :
  (s.to_limit m).fun_t ((s.seqs_le le).fun_t t) = (s.to_limit n).fun_t t :=
by { rw[←s.seqs_le_commuts le], simp[comp_fun_t] }

@[simp] lemma seqs_le_commuts'_p {n m : ℕ} (le : n ≤ m) (p : formula (l n)) :
  (s.to_limit m).fun_p ((s.seqs_le le).fun_p p) = (s.to_limit n).fun_p p :=
by { rw[←s.seqs_le_commuts le], simp[comp_fun_p] }

@[simp] def rank_t : term L → ℕ
| #n        := 0
| (app f v) := max (s.rank_fn f) (⨆ᶠ i, rank_t (v i))

@[simp, reducible] def retruct_t : Π t : term L, term (l $ s.rank_t t)
| #n := #n
| (@term.app L m f v) :=
    let n := max (s.rank_fn f) (⨆ᶠ i, s.rank_t (v i)),
        tr₀ : l (s.rank_fn f) ↝ᴸ l n := s.seqs_le (by simp[n]),
        tr : Π i, l (s.rank_t $ v i) ↝ᴸ l n := λ i, s.seqs_le (by { simp[n], refine or.inr (le_fintype_sup _ i)}) in
    app (tr₀.fn _ (s.fn f)) (λ i, (tr i).fun_t (retruct_t (v i)))

@[simp] def rank_p : formula L → ℕ
| (app r v)   := max (s.rank_pr r) (⨆ᶠ i, s.rank_t (v i))
| (t ≃₀ u) := max (s.rank_t t) (s.rank_t u)
| ⊤           := 0
| (p ⟶ q)     := max (rank_p p) (rank_p q)
| (⁻p)        := rank_p p
| (∏ p)       := rank_p p

@[simp, reducible] def retruct_p : Π p : formula L, formula (l $ s.rank_p p)
| (app r v)   :=
  let tr₀ : l (s.rank_pr r) ↝ᴸ l (s.rank_p (app r v)) := s.seqs_le (by simp),
      tr : Π i, l (s.rank_t $ v i) ↝ᴸ l (s.rank_p (app r v)) := λ i, s.seqs_le (by { simp, refine or.inr (le_fintype_sup _ i)}) in
    app (tr₀.pr _ (s.pr r)) (λ i, (tr i).fun_t (s.retruct_t (v i)))
| (equal t u) :=
    let tr₁ : l (s.rank_t t) ↝ᴸ l (s.rank_p (equal t u)) := s.seqs_le (by simp),
        tr₂ : l (s.rank_t u) ↝ᴸ l (s.rank_p (equal t u)) := s.seqs_le (by simp) in
    (tr₁.fun_t $ s.retruct_t t) ≃ (tr₂.fun_t $ s.retruct_t u)
| ⊤           := ⊤
| (p ⟶ q)     :=
   let tr₁ : l (s.rank_p p) ↝ᴸ l (s.rank_p (p ⟶ q)) := s.seqs_le (by simp),
       tr₂ : l (s.rank_p q) ↝ᴸ l (s.rank_p (p ⟶ q)) := s.seqs_le (by simp) in
    (tr₁.fun_p $ retruct_p p) ⟶ (tr₂.fun_p $ retruct_p q)
| (⁻p)        :=
    let tr₁ : l (s.rank_p p) ↝ᴸ l (s.rank_p (⁻p)) := s.seqs_le (by simp) in
    ⁻(tr₁.fun_p $ retruct_p p)
| (∏ p)       :=
    let tr₁ : l (s.rank_p p) ↝ᴸ l (s.rank_p (∏ p)) := s.seqs_le (by simp) in
    ∏ (tr₁.fun_p $ retruct_p p)

lemma reduct_t_spec (t : term L) : (s.to_limit (s.rank_t t)).fun_t (s.retruct_t t) = t :=
by induction t; simp[s.fn_spec]; case app : n f v IH { funext i, exact IH i }

lemma reduct_p_spec (p : formula L) : (s.to_limit (s.rank_p p)).fun_p (s.retruct_p p) = p :=
by induction p; simp[s.pr_spec, reduct_t_spec, *]

end seq_limit

end language_translation


end language

end fopl
