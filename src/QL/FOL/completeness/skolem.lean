import QL.FOL.semantics QL.FOL.pnf QL.FOL.language

universe u

namespace fol
variables (L : language.{u})
open_locale logic_symbol
open subformula logic logic.Theory

namespace language

@[reducible] def skolem : language :=
{ fn := λ m, pnf L m 1, pr := λ _, pempty }

instance : inhabited ((L + L.skolem).fn 0) := ⟨sum.inr default⟩

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
| n (fal φ)            := ∀'pnf.pull (push φ).skolemize
| n (ex φ)             := pnf.msubst (skolem_term φ).right (push φ).skolemize
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.rank)⟩]}

@[simp] lemma forall_pnf_skolemize : ∀ {m} (φ : pnf L m 0), φ.skolemize.forall_pnf
| m (openformula p hp) := by simp
| m (fal φ)            := by simp; exact forall_pnf_skolemize (push φ)
| m (ex φ)             := by simp; exact forall_pnf_skolemize (push φ)
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.rank)⟩]}

end pnf

namespace subformula
variables {m n : ℕ} (Sₛₖ : Structure (L + L.skolem)) (T : preTheory L m)

def to_snf (p : formula L m) : formula (L + L.skolem) m := p.to_pnf.skolemize.to_formula

end subformula

namespace skolem
open language pnf
variables {m n : ℕ} (Sₛₖ : Structure (L + L.skolem)) (T : preTheory L m)

lemma val_open_formula (me) (p : formula L m) : Sₛₖ ⊧[me] p.left ↔ Sₛₖ.restrict add_left ⊧[me] p :=
(Structure.of_lfin.formula_val_iff Sₛₖ add_left me p).symm

lemma restrict_val : ∀ {m} (me) (φ : pnf L m 0),
  Sₛₖ ⊧[me] φ.skolemize.to_formula → Sₛₖ.restrict add_left ⊧[me] φ.to_formula
| m me (openformula p hp) := by simpa using (val_open_formula Sₛₖ me p).mp
| m me (fal φ)            :=
    begin
      simp, intros h x,
      have IH : Sₛₖ ⊧[x *> me] φ.push.skolemize.to_formula → formula.val (Sₛₖ.restrict add_left) (x *> me) φ.push.to_formula,
      from restrict_val (x *> me) φ.push,
      simpa[formula.val] using IH (h x)
    end
| m me (ex φ)            :=
    begin
      simp, intros h,
      let z := subterm.val Sₛₖ me fin.nil φ.skolem_term.right,
      have h : Sₛₖ ⊧[z *> me] φ.push.skolemize.to_formula, by simpa using h,
      refine ⟨z, by simpa using restrict_val (z *> me) φ.push h⟩
    end
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.2.rank)⟩]}

variables {Sₛₖ}

lemma restrict_models (p : formula L m) :
  Sₛₖ ⊧ p.to_snf → Sₛₖ.restrict add_left ⊧ p := λ h me,
begin
  have iff : ∀ me, Sₛₖ.restrict add_left ⊧[me] p.normalize ↔ Sₛₖ.restrict add_left ⊧[me] p,
  by simpa[models_def] using logic.sound.tautology_of_tautology (Sₛₖ.restrict add_left) (p.normalize ⟷ p) (equiv_normalize ∅ p),
  have : Sₛₖ.restrict add_left ⊧[me] p.normalize, from restrict_val Sₛₖ me p.to_pnf (h me),
  exact (iff me).mp this
end

variables (S : Structure L) 

@[reducible] noncomputable def Skolemize : Structure (L + L.skolem) :=
{ dom := S,
  dom_inhabited := S.dom_inhabited,
  fn := λ m f, sum.cases_on f S.fn (λ φ me, classical.epsilon (λ z, val S me (fin.nil <* z) φ.to_formula)),
  pr := λ n r, sum.cases_on r S.pr (by rintros ⟨⟩) }

def to_Skolemize : S →ₛ[add_left] Skolemize S :=
{ to_fun := id,
  injective := function.injective_id,
  map_fn' := by intros; refl,
  map_pr' := by intros; refl }

variables {S}

lemma Str_sk_val_open_formula (me) (p : formula L m) : S ⊧[me] p ↔ Skolemize S ⊧[me] p.left :=
by simpa using Structure.hom.val_iff_of_surjective (to_Skolemize S) function.surjective_id me fin.nil p

noncomputable def sk_value (me) (φ : pnf L m 1) := subterm.val (Skolemize S) me fin.nil φ.skolem_term.right

lemma sk_value_spec (me) (φ : pnf L m 1) (z) (h : val S me (fin.nil <* z) φ.to_formula) :
  val S me (fin.nil <* sk_value me φ) φ.to_formula:=
classical.epsilon_spec ⟨z, h⟩

variables (S)

lemma Skolemize_val : ∀ {m} (me) (φ : pnf L m 0),
  S ⊧[me] φ.to_formula → Skolemize S ⊧[me] φ.skolemize.to_formula
| m me (openformula p hp) := by simpa using (Str_sk_val_open_formula me p).mp
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

variables {S}

lemma Skolemize_models (p : formula L m) :
  S ⊧ p → Skolemize S ⊧ p.to_snf := λ h me,
begin
  have iff : ∀ me, S ⊧[me] p.normalize ↔ S ⊧[me] p,
  by simpa[models_def] using logic.sound.tautology_of_tautology S (p.normalize ⟷ p) (equiv_normalize ∅ p),
  exact Skolemize_val S me p.to_pnf ((iff me).mpr (h me))
end

lemma satisfiability (p : formula L m) : satisfiable p.to_snf ↔ satisfiable p :=
⟨by { rintros ⟨Sₛₖ, hSₛₖ⟩, refine ⟨Sₛₖ.restrict add_left, restrict_models p hSₛₖ⟩ },
 by { rintros ⟨S, hS⟩, refine ⟨Skolemize S, Skolemize_models p hS⟩ }⟩

lemma Satisfiability {T : preTheory L m} : Satisfiable (subformula.to_snf '' T) ↔ Satisfiable T :=
⟨by { rintros ⟨Sₛₖ, hSₛₖ⟩,
      refine ⟨Sₛₖ.restrict add_left,
        by { simp[logic.semantics.Models_def], intros p hp,
             have : Sₛₖ ⊧ p.to_snf, from hSₛₖ (by simp; refine ⟨p, by simp[hp]⟩),
             exact restrict_models p this }⟩ },
 by { rintros ⟨S, hS⟩,
      refine ⟨Skolemize S, by { simp[logic.semantics.Models_def], intros p hp, exact Skolemize_models p (hS hp) }⟩ }⟩

end skolem

private def s : subformula language.empty 0 0 := ∀' ∃' ∀' ∃'((#0 =' #1) ⟶ (#2 =' #3))

#eval to_string s
#eval to_string s.to_pnf
#eval to_string s.to_snf

end fol

