import QL.FOL.Tait.tait provability QL.FOL.coding consistency

universes u v

namespace fol
open_locale logic_symbol
variables {L : language.{u}} {m n : ℕ}

namespace Tait

namespace subformula
variables {L m n}

def uniform : bounded_subformula L m n →ₗ subformula L ℕ n := map coe

@[simp] lemma uniform_inj (p q : bounded_subformula L m n) :
  p.uniform = q.uniform ↔ p = q :=
⟨λ h, map_inj_of_inj coe fin.coe_injective h, λ e, by simp[e]⟩

@[simp] lemma uniform_relation {k} (r : L.pr k) (v : fin k → bounded_subterm L m n) :
  uniform (relation r v) = relation r (λ i, subterm.uniform (v i)) := by simp[uniform, subterm.uniform]

@[simp] lemma uniform_neg_relation {k} (r : L.pr k) (v : fin k → bounded_subterm L m n) :
  uniform (neg_relation r v) = neg_relation r (λ i, subterm.uniform (v i)) := by simp[uniform, subterm.uniform]

@[simp] lemma uniform_fal (p : bounded_subformula L m (n + 1)) :
  uniform (∀'p) = ∀'uniform p := by simp[uniform]; unfold has_univ_quantifier'.univ; simp; refl

@[simp] lemma uniform_ex (p : bounded_subformula L m (n + 1)) :
  uniform (∃'p) = ∃'uniform p := by simp[uniform]; unfold has_exists_quantifier'.ex; simp; refl

@[simp] lemma uniform_mlift (p : bounded_subformula L m n) : p.mlift.uniform = p.uniform :=
by simp[mlift, uniform]; congr

@[simp] lemma uniform_cast_le {m₁ m₂ : ℕ} (h : m₁ ≤ m₂) (p : bounded_subformula L m₁ n) :
  (cast_le h p).uniform = p.uniform :=
by simp[cast_le, uniform]; congr

@[simp] lemma uniform_to_subterm (p : bounded_subformula L m n) (h) : to_bform p.uniform h = p :=
by induction p using fol.Tait.subformula.ind_on; simp*

@[simp] lemma to_subterm_uniform (p : subformula L ℕ n) (h : p.arity ≤ m) : (p.to_bform h).uniform = p :=
by induction p using fol.Tait.subformula.ind_on; simp*

@[simp] lemma subformula_arity (p : bounded_subformula L m n) : p.uniform.arity ≤ m :=
by induction p using fol.Tait.subformula.ind_on; simp*

section encode
open encodable nat
variables {L n} [∀ k, encodable (L.pr k)] [∀ k, encodable (L.fn k)]

@[simp] def to_nat : Π {n}, subformula L ℕ n → ℕ
| n verum                       := 0
| n falsum                      := 1
| n (@relation L _ _ k r v)     := (bit0 $ bit0 $ mkpair k $ mkpair (encode r) (encode v)) + 2
| n (@neg_relation L _ _ k r v) := (bit0 $ bit1 $ mkpair k $ mkpair (encode r) (encode v)) + 2
| n (and p q)                   := (bit1 $ bit0 $ bit0 $ mkpair p.to_nat q.to_nat) + 2
| n (or p q)                    := (bit1 $ bit0 $ bit1 $ mkpair p.to_nat q.to_nat) + 2
| n (fal p)                     := (bit1 $ bit1 $ bit0 p.to_nat) + 2
| n (ex p)                      := (bit1 $ bit1 $ bit1 p.to_nat) + 2

variables (L n)

@[simp] def of_nat : Π n, ℕ → option (subformula L ℕ n)
| n 0 := some verum
| n 1 := some falsum
| n (e + 2) :=
    let i := e.div2.div2.div2 in
    have div8 : i ≤ e := by simp[i, nat.div2_val]; 
      exact le_trans (nat.div_le_self (e / 2 / 2) 2) (le_trans (nat.div_le_self (e/2) 2) (nat.div_le_self e 2)),
    have hi : i < e + 2, from lt.step (lt_succ_iff.mpr div8),
    have hi1 : i.unpair.1 < e + 2, from (lt.step $ nat.lt_succ_iff.mpr (le_trans (nat.unpair_left_le _) div8)),
    have hi2 : i.unpair.2 < e + 2, from (lt.step $ nat.lt_succ_iff.mpr (le_trans (nat.unpair_right_le _) div8)),
    match e.bodd with
    | ff :=
      match e.div2.bodd with
      | ff :=
        let x := e.div2.div2,
            k := x.unpair.1,
            r := decode₂ (L.pr k) x.unpair.2.unpair.1,
            v := decode₂ (fin k → subterm L ℕ n) x.unpair.2.unpair.2 in
        r.bind (λ r, v.map (relation r))
      | tt :=
        let x := e.div2.div2,
            k := x.unpair.1,
            r := decode₂ (L.pr k) x.unpair.2.unpair.1,
            v := decode₂ (fin k → subterm L ℕ n) x.unpair.2.unpair.2 in
        r.bind (λ r, v.map (neg_relation r))
      end
    | tt :=
      match e.div2.bodd, e.div2.div2.bodd with
      | ff, ff := (of_nat n i.unpair.1).bind (λ p, (of_nat n i.unpair.2).map (and p))
      | ff, tt := (of_nat n i.unpair.1).bind (λ p, (of_nat n i.unpair.2).map (or p))
      | tt, ff := (of_nat (n + 1) i).map fal
      | tt, tt := (of_nat (n + 1) i).map ex
      end
    end
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2)⟩]}

@[simp] lemma of_nat_to_nat : ∀ {n} (p : subformula L ℕ n), of_nat L n p.to_nat = some p
| n verum                       := by simp
| n falsum                      := by simp
| n (@relation L _ _ k r v)     :=
    begin
      simp only [to_nat, of_nat, nat.bodd_bit0, nat.div2_bit0, nat.unpair_mkpair],
      rw[show (unpair (bit0 (bit0 (mkpair k (mkpair (encode r) (encode v))))).div2.div2).fst = k, by simp],
      simp only [decode₂_encode, option.some_bind', option.map_some', heq.refl], simp
    end
| n (@neg_relation L _ _ k r v) :=
    begin
      simp only [to_nat, of_nat, nat.bodd_bit0, nat.bodd_bit1, nat.div2_bit0, nat.div2_bit1, nat.unpair_mkpair],
      rw[show (unpair (bit0 (bit1 (mkpair k (mkpair (encode r) (encode v))))).div2.div2).fst = k, by simp],
      simp only [decode₂_encode, option.some_bind', option.map_some', heq.refl], simp
    end
| n (and p q)                   := by simp; refine ⟨of_nat_to_nat p, of_nat_to_nat q⟩
| n (or p q)                    := by simp; refine ⟨of_nat_to_nat p, of_nat_to_nat q⟩
| n (fal p)                     := by simp; refine (of_nat_to_nat p)
| n (ex p)                      := by simp; refine (of_nat_to_nat p)

instance (n) : encodable (subformula L ℕ n) :=
{ encode := to_nat,
  decode := of_nat L n,
  encodek := by simp }

variables {L m n}

def index : bounded_subformula L m n → ℕ := λ p, encodable.encode p.uniform

variables (L m n)

def of_index : ℕ → option (bounded_subformula L m n) := λ i,
  let p := encodable.decode₂ (subformula L ℕ n) i in
  p.bind (λ p, if h : p.arity ≤ m then some (p.to_bform h) else none)

variables {L m n}

@[simp] lemma of_index_index (p : bounded_subformula L m n) : of_index L m n p.index = some p :=
by simp[index, of_index]

@[simp] lemma mlift_index (p : bounded_subformula L m n) : p.mlift.index = p.index :=
by simp[index]

@[simp] lemma cast_le_index {m₁ m₂ : ℕ} (h : m₁ ≤ m₂) (p : bounded_subformula L m₁ n) :
  (cast_le h p).index = p.index :=
by simp[index]

@[simp] lemma of_nat_uniform (p : bounded_subformula L m n) : encodable.decode₂ (subformula L ℕ n) p.index = p.uniform :=
by simp[index]; refl

@[simp] lemma index_eq_some {e} {p : bounded_subformula L m n} : of_index L m n e = some p ↔ p.index = e :=
by { simp[of_index, index, encodable.decode₂_eq_some, dite_eq_iff], split,
  { simp, rintros _ rfl h rfl, simp },
  { rintros rfl, refine ⟨p.uniform, rfl, by simp⟩ } }

lemma of_index_eq_some {m₁ m₂} {p : bounded_subformula L m₁ n} {q : bounded_subformula L m₂ n} :
  p.index = q.index ↔ p.uniform = q.uniform :=
by simp[index]

@[simp] lemma index_inj {p q : bounded_subformula L m n} : p.index = q.index ↔ p = q :=
by simp[index]

end encode

end subformula

end Tait

end fol