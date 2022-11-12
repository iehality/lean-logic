import QL.FOL.semantics QL.FOL.pnf QL.FOL.language

universe u

namespace fol
variables (L : language.{u})
open_locale logic_symbol
open subformula logic logic.Theory

namespace language

def skolem : language :=
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

@[simp] def to_skolem : Π {m}, pnf L m 0 → pnf (L + L.skolem) m 0
| n (openformula p hp) := openformula p.left (by simpa[left] using hp)
| n (fal φ)            := ∀' pnf.pull (push φ).to_skolem
| n (ex φ)             := pnf.msubst (skolem_term φ).right (push φ).to_skolem
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.rank)⟩]}

end pnf

namespace skolem
open language pnf
variables {m n : ℕ} (S : Structure (L + L.skolem))

lemma val_open_formula (me) (p : formula L m) (hp : p.is_open) : S ⊧[me] p.left ↔ S.translation add_left ⊧[me] p :=
(Structure.of_lfin.formula_val_iff S add_left me p hp).symm

lemma val_to_skolem : ∀ {m} (me) (φ : pnf L m 0), S ⊧[me] φ.to_skolem.to_formula → S.translation add_left ⊧[me] φ.to_formula
| m me (openformula p hp) := by simpa using (val_open_formula S me p hp).mp
| m me (fal φ)            :=
    begin
      simp, intros h x,
      have IH : S ⊧[x *> me] φ.push.to_skolem.to_formula → formula.val (S.translation add_left) (x *> me) φ.push.to_formula,
      from val_to_skolem (x *> me) φ.push,
      simpa[formula.val] using IH (h x)
    end
| m me (ex φ)            :=
    begin
      simp, intros h,
      let z := subterm.val S me fin_zero_elim (subterm.right φ.skolem_term),
      have h : S ⊧[z *> me] φ.push.to_skolem.to_formula, by simpa using h,
      refine ⟨z, by simpa using val_to_skolem (z *> me) φ.push h⟩
    end
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.2.rank)⟩]}

end skolem

private def s : subformula language.empty 0 0 := ∀' ∃' ∀' ∃'((#0 =' #1) ⟶ (#2 =' #3))

#eval to_string s
#eval to_string s.to_pnf
#eval to_string s.to_pnf.to_skolem

end fol

