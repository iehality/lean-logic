import QL.FOL.semantics QL.FOL.pnf QL.FOL.language

universe u

namespace fol
variables (L : language.{u})
open_locale logic_symbol
open subformula logic logic.Theory

namespace language

@[reducible] def skolem : language :=
{ fn := λ m, pnf L m 1, pr := λ _, pempty }

def skolem' := skolem L + L

namespace skolem

instance [∀ n, has_to_string (L.fn n)] [∀ n, has_to_string (L.pr n)] (n) : has_to_string (L.skolem.fn n) :=
pnf.has_to_string

instance [∀ n, has_to_string (L.fn n)] [∀ n, has_to_string (L.pr n)] (n) : has_to_string (L.skolem.pr n) :=
⟨by rintros ⟨⟩⟩

end skolem


end language

variables {L}

namespace pnf
variables {m n : ℕ}

def skolem_term (φ : pnf L m 1) : subterm L.skolem m 0 := subterm.function φ subterm.metavar

@[simp] def skolemize : Π {m}, pnf L m 0 → pnf (L + L.skolem) m 0
| n (openformula p hp) := openformula p.left (by simpa[left] using hp)
| n (fal φ)            := ∀' pnf.pull (push φ).skolemize
| n (ex φ)             := pnf.msubst (skolem_term φ).right (push φ).skolemize
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.rank)⟩]}

end pnf

namespace skolem
open language pnf
variables {m n : ℕ} (Sₛₖ : Structure (L + L.skolem)) (T : preTheory L m)

lemma val_open_formula (me) (p : formula L m) (hp : p.is_open) : Sₛₖ ⊧[me] p.left ↔ Sₛₖ.translation add_left ⊧[me] p :=
(Structure.of_lfin.formula_val_iff Sₛₖ add_left me p hp).symm

lemma Sₛₖ_val : ∀ {m} (me) (φ : pnf L m 0),
  Sₛₖ ⊧[me] φ.skolemize.to_formula → Sₛₖ.translation add_left ⊧[me] φ.to_formula
| m me (openformula p hp) := by simpa using (val_open_formula Sₛₖ me p hp).mp
| m me (fal φ)            :=
    begin
      simp, intros h x,
      have IH : Sₛₖ ⊧[x *> me] φ.push.skolemize.to_formula → formula.val (Sₛₖ.translation add_left) (x *> me) φ.push.to_formula,
      from Sₛₖ_val (x *> me) φ.push,
      simpa[formula.val] using IH (h x)
    end
| m me (ex φ)            :=
    begin
      simp, intros h,
      let z := subterm.val Sₛₖ me fin.nil (subterm.right φ.skolem_term),
      have h : Sₛₖ ⊧[z *> me] φ.push.skolemize.to_formula, by simpa using h,
      refine ⟨z, by simpa using Sₛₖ_val (z *> me) φ.push h⟩
    end
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.2.rank)⟩]}

variables (S : Structure L) 

@[reducible] noncomputable def Skolemize : Structure (L + L.skolem) :=
{ dom := S,
  inhabited := S.inhabited,
  fn := λ m f, sum.cases_on f S.fn (λ φ me, classical.epsilon (λ z, val S me (fin.nil <* z) φ.to_formula)),
  pr := λ n r, sum.cases_on r S.pr (by rintros ⟨⟩) }

def to_Skolemize : S →ₛ[add_left] Skolemize S :=
{ to_fun := id,
  injective := function.injective_id,
  map_fn' := by intros; refl,
  map_pr' := by intros; refl }

variables {S}

lemma Str_sk_val_open_formula (me) (p : formula L m) (hp : p.is_open) : S ⊧[me] p ↔ Skolemize S ⊧[me] p.left :=
by simpa using Structure.hom.val_iff (to_Skolemize S) me fin.nil p hp

noncomputable def sk_value (me) (φ : pnf L m 1) := subterm.val (Skolemize S) me fin.nil φ.skolem_term.right

lemma sk_value_spec (me) (φ : pnf L m 1) (z) (h : val S me (fin.nil <* z) φ.to_formula) :
  val S me (fin.nil <* sk_value me φ) φ.to_formula:=
classical.epsilon_spec ⟨z, h⟩

lemma Skolemize_val : ∀ {m} (me) (φ : pnf L m 0),
  S ⊧[me] φ.to_formula → Skolemize S ⊧[me] φ.skolemize.to_formula
| m me (openformula p hp) := by simpa using (Str_sk_val_open_formula me p hp).mp
| m me (fal φ)            :=
    begin
      simp, intros h x,
      have : val S me ((fin.nil : fin 0 → S) <* x) φ.to_formula → Skolemize S ⊧[x *> me] φ.push.skolemize.to_formula,
      by simpa using Skolemize_val (x *> me) φ.push,
      exact this (h x)
    end
| m me (ex φ)            :=
    begin
      simp, intros z h,
      show Skolemize S ⊧[sk_value me φ *> me] φ.push.skolemize.to_formula,
      have : val S me (fin.nil <* sk_value me φ) φ.to_formula → Skolemize S ⊧[sk_value me φ *> me] φ.push.skolemize.to_formula,
        by simpa using Skolemize_val (sk_value me φ *> me) φ.push,
      exact this (sk_value_spec me φ z h)
    end
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.2.rank)⟩]}

lemma satisfiability (p : sentence L) : satisfiable p ↔ satisfiable p.to_pnf.skolemize.to_formula :=
⟨ begin
    rintros ⟨S, hS⟩, use Skolemize S,
    have lmm₁ : S ⊧ p.normalize,
    { have : S ⊧ normalize p ↔ S ⊧ p, by simpa using logic.tautology_of_tautology S (p.normalize ⟷ p) (equiv_normalize ∅ p),
      exact this.mpr hS },
    have lmm₂ : S ⊧ p.normalize → Skolemize S ⊧ (to_pnf p).skolemize.to_formula,
    { simp[sentence_models_def], exact Skolemize_val fin.nil p.to_pnf },
    exact lmm₂ lmm₁
  end,
  begin
    rintros ⟨S, hS⟩, use S.translation add_left,
    have lmm₁ : S.translation add_left ⊧ p.normalize ↔ S.translation add_left ⊧ p,
    by simpa using logic.tautology_of_tautology (S.translation add_left) (p.normalize ⟷ p) (equiv_normalize ∅ p),    
    have lmm₂ : S.translation add_left ⊧ p.normalize,
    { simp[sentence_models_def] at hS ⊢, exact Sₛₖ_val S fin.nil p.to_pnf hS },
    exact lmm₁.mp lmm₂
  end⟩

end skolem

private def s : subformula language.empty 0 0 := ∀' ∃' ∀' ∃'((#0 =' #1) ⟶ (#2 =' #3))

#eval to_string s
#eval to_string s.to_pnf
#eval to_string s.to_pnf.skolemize

end fol

