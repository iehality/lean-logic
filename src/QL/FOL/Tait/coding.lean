import QL.FOL.Tait.tait provability QL.FOL.coding consistency

universes u v

namespace fol
open_locale logic_symbol
variables {L : language.{u}} {m n : ℕ}

namespace Tait

namespace uniform_subformula
variables {L n}

section encode
open encodable nat
variables {L n} [∀ k, encodable (L.pr k)] [∀ k, encodable (L.fn k)]

@[simp] def to_nat : Π {n}, uniform_subformula L n → ℕ
| n verum                     := 0
| n falsum                    := 1
| n (@relation L _ k r v)     := (bit0 $ bit0 $ mkpair k $ mkpair (encode r) (encode v)) + 2
| n (@neg_relation L _ k r v) := (bit0 $ bit1 $ mkpair k $ mkpair (encode r) (encode v)) + 2
| n (and p q)                 := (bit1 $ bit0 $ bit0 $ mkpair p.to_nat q.to_nat) + 2
| n (or p q)                  := (bit1 $ bit0 $ bit1 $ mkpair p.to_nat q.to_nat) + 2
| n (fal p)                   := (bit1 $ bit1 $ bit0 p.to_nat) + 2
| n (ex p)                    := (bit1 $ bit1 $ bit1 p.to_nat) + 2

variables (L n)

@[simp] def of_nat : Π n, ℕ → option (uniform_subformula L n)
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
            v := decode₂ (fin k → uniform_subterm L n) x.unpair.2.unpair.2 in
        r.bind (λ r, v.map (relation r))
      | tt :=
        let x := e.div2.div2,
            k := x.unpair.1,
            r := decode₂ (L.pr k) x.unpair.2.unpair.1,
            v := decode₂ (fin k → uniform_subterm L n) x.unpair.2.unpair.2 in
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

@[simp] lemma of_nat_to_nat : ∀ {n} (p : uniform_subformula L n), of_nat L n p.to_nat = some p
| n verum                     := by simp
| n falsum                    := by simp
| n (@relation L _ k r v)     :=
    begin
      simp only [to_nat, of_nat, nat.bodd_bit0, nat.div2_bit0, nat.unpair_mkpair],
      rw[show (unpair (bit0 (bit0 (mkpair k (mkpair (encode r) (encode v))))).div2.div2).fst = k, by simp],
      simp only [decode₂_encode, option.some_bind', option.map_some', heq.refl], simp
    end
| n (@neg_relation L _ k r v) :=
    begin
      simp only [to_nat, of_nat, nat.bodd_bit0, nat.bodd_bit1, nat.div2_bit0, nat.div2_bit1, nat.unpair_mkpair],
      rw[show (unpair (bit0 (bit1 (mkpair k (mkpair (encode r) (encode v))))).div2.div2).fst = k, by simp],
      simp only [decode₂_encode, option.some_bind', option.map_some', heq.refl], simp
    end
| n (and p q)                 := by simp; refine ⟨of_nat_to_nat p, of_nat_to_nat q⟩
| n (or p q)                  := by simp; refine ⟨of_nat_to_nat p, of_nat_to_nat q⟩
| n (fal p)                   := by simp; refine (of_nat_to_nat p)
| n (ex p)                    := by simp; refine (of_nat_to_nat p)

instance (n) : encodable (uniform_subformula L n) :=
{ encode := to_nat,
  decode := of_nat L n,
  encodek := by simp }

end encode

end uniform_subformula

namespace subformula
open uniform_subformula
variables {L m n}

section encode

variables [∀ k, encodable (L.fn k)] [∀ k, encodable (L.pr k)]

def to_nat : subformula L m n → ℕ := λ p, encodable.encode p.uniform

variables (L m n)

def of_nat : ℕ → option (subformula L m n) := λ i,
  let p := encodable.decode₂ (uniform_subformula L n) i in
  p.bind (λ p, if h : p.arity ≤ m then some (p.to_subformula h) else none)

variables {L m n}

@[simp] lemma to_nat_of_nat (p : subformula L m n) : of_nat L m n p.to_nat = some p :=
by simp[to_nat, of_nat]

@[simp] lemma of_nat_to_nat (p : subformula L m n) : to_nat p.mlift = to_nat p :=
by simp[to_nat]

@[simp] lemma of_nat_uniform (p : subformula L m n) : encodable.decode₂ (uniform_subformula L n) p.to_nat = p.uniform :=
by simp[to_nat]; refl

lemma of_nat_eq_some {e} {p : subformula L m n} : of_nat L m n e = some p ↔ p.to_nat = e :=
by { simp[of_nat, to_nat, encodable.decode₂_eq_some, dite_eq_iff], split,
  { simp, rintros _ rfl h rfl, simp },
  { rintros rfl, refine ⟨p.uniform, rfl, by simp⟩ } }

lemma of_nat_eq_som {m₁ m₂} {p : subformula L m₁ n} {q : subformula L m₂ n} : p.to_nat = q.to_nat ↔ p.uniform = q.uniform :=
by simp[to_nat]

@[simp] lemma to_nat_inj {p q : subformula L m n} : p.to_nat = q.to_nat ↔ p = q :=
by { have : q = p ↔ p.to_nat = q.to_nat, by simpa using @of_nat_eq_some _ _ _ _ _ q.to_nat p,
     simp[←this], exact comm }

end encode

section subst

@[simp] lemma uniform_subst : ∀ {n} (u : subterm L m n) (p : Tait.subformula L m (n + 1)),
  (subst u p).uniform = Tait.uniform_subformula.subst u.uniform p.uniform
| n u verum              := by simp[verum_eq]
| n u falsum             := by simp[falsum_eq]
| n u (relation r v)     := by simp[(∘)]
| n u (neg_relation r v) := by simp[(∘)]
| n u (and p q)          := by simp[and_eq]; exact ⟨uniform_subst u p, uniform_subst u q⟩
| n u (or p q)           := by simp[or_eq]; exact ⟨uniform_subst u p, uniform_subst u q⟩
| n u (fal p)            := by simp[fal_eq, ←subterm.uniform_lift]; exact uniform_subst u.lift p
| n u (ex p)             := by simp[ex_eq, ←subterm.uniform_lift]; exact uniform_subst u.lift p
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.2.complexity)⟩]}

@[simp] lemma uniform_push : ∀ {n} (p : Tait.subformula L m (n + 1)),
  (push p).uniform = Tait.uniform_subformula.subst (&&m) p.uniform
| n verum              := by simp[verum_eq]
| n falsum             := by simp[falsum_eq]
| n (relation r v)     := by simp[(∘)]
| n (neg_relation r v) := by simp[(∘)]
| n (and p q)          := by simp[and_eq]; exact ⟨uniform_push p, uniform_push q⟩
| n (or p q)           := by simp[or_eq];  exact ⟨uniform_push p, uniform_push q⟩
| n (fal p)            := by simp[fal_eq, ←subterm.uniform_lift]; exact uniform_push p
| n (ex p)             := by simp[ex_eq, ←subterm.uniform_lift]; exact uniform_push p
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.complexity)⟩]}

end subst

end subformula

end Tait
end fol