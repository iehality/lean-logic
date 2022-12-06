import QL.FOL.Tait.tait provability QL.FOL.coding consistency

universes u v

namespace fol
open_locale logic_symbol
variables {L : language.{u}} {m n : ℕ}

namespace Tait
variables (L)

inductive uniform_subformula : ℕ → Type u
| verum        {n} : uniform_subformula n
| falsum       {n} : uniform_subformula n
| relation     {n} : ∀ {p}, L.pr p → (fin p → uniform_subterm L n) → uniform_subformula n
| neg_relation {n} : ∀ {p}, L.pr p → (fin p → uniform_subterm L n) → uniform_subformula n
| and          {n} : uniform_subformula n → uniform_subformula n → uniform_subformula n
| or           {n} : uniform_subformula n → uniform_subformula n → uniform_subformula n
| fal          {n} : uniform_subformula (n + 1) → uniform_subformula n
| ex           {n} : uniform_subformula (n + 1) → uniform_subformula n

namespace uniform_subformula
variables {L n}

@[simp] def uvars : Π {n}, Tait.uniform_subformula L n → ℕ
| n verum              := 0
| n falsum             := 0
| n (relation r v)     := ⨆ᶠ i, (v i).uvars
| n (neg_relation r v) := ⨆ᶠ i, (v i).uvars
| n (and p q)          := max p.uvars q.uvars
| n (or p q)           := max p.uvars q.uvars
| n (fal p)            := p.uvars
| n (ex p)             := p.uvars

@[simp] def to_subformula : ∀ {n} (p : uniform_subformula L n), p.uvars ≤ m → subformula L m n
| n verum              h := ⊤
| n falsum             h := ⊥
| n (relation r v)     h := subformula.relation r (λ i, (v i).to_subterm (by show (v i).uvars ≤ m; simp at h; exact h i))
| n (neg_relation r v) h := subformula.neg_relation r (λ i, (v i).to_subterm (by show (v i).uvars ≤ m; simp at h; exact h i))
| n (and p q)          h := have h : p.uvars ≤ m ∧ q.uvars ≤ m, by simpa using h, p.to_subformula h.1 ⊓ q.to_subformula h.2
| n (or p q)           h := have h : p.uvars ≤ m ∧ q.uvars ≤ m, by simpa using h, p.to_subformula h.1 ⊔ q.to_subformula h.2
| n (fal p)            h := ∀'p.to_subformula (by simpa using h)
| n (ex p)             h := ∃'p.to_subformula (by simpa using h)

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

@[simp] def to_uniform : Π {n}, subformula L m n → uniform_subformula L n
| n verum              := uniform_subformula.verum
| n falsum             := uniform_subformula.falsum
| n (relation r v)     := uniform_subformula.relation r (subterm.to_uniform ∘ v)
| n (neg_relation r v) := uniform_subformula.neg_relation r (subterm.to_uniform ∘ v)
| n (and p q)          := uniform_subformula.and p.to_uniform q.to_uniform
| n (or p q)           := uniform_subformula.or p.to_uniform q.to_uniform
| n (fal p)            := uniform_subformula.fal p.to_uniform
| n (ex p)             := uniform_subformula.ex p.to_uniform

@[simp] lemma to_uniform_mlift (p : subformula L m n) : p.mlift.to_uniform = p.to_uniform :=
by simp[mlift]; induction p; simp[mlift', ←fal_eq, ←verum_eq, ←falsum_eq, ←and_eq, ←or_eq, ←fal_eq, ←ex_eq, (∘), *]

@[simp] lemma to_uniform_to_subterm (p : subformula L m n) (h) : p.to_uniform.to_subformula h = p :=
by induction p; simp*; refl

@[simp] lemma to_subterm_to_uniform (p : uniform_subformula L n) (h : p.uvars ≤ m) : (p.to_subformula h).to_uniform = p :=
by induction p; simp[←fal_eq, ←verum_eq, ←falsum_eq, ←and_eq, ←or_eq, ←fal_eq, ←ex_eq, (∘), *]

section encode

variables [∀ k, encodable (L.fn k)] [∀ k, encodable (L.pr k)]

def to_nat : subformula L m n → ℕ := λ p, encodable.encode p.to_uniform

variables (L m n)

def of_nat : ℕ → option (subformula L m n) := λ i,
  let p := encodable.decode₂ (uniform_subformula L n) i in
  p.bind (λ p, if h : p.uvars ≤ m then some (p.to_subformula h) else none)

variables {L m n}

@[simp] lemma subformula_uvars (p : subformula L m n) : p.to_uniform.uvars ≤ m :=
by induction p; simp*

@[simp] lemma sentence_uvars (σ : subformula L 0 n) : σ.to_uniform.uvars ≤ m :=
le_trans (subformula_uvars σ) (by simp)

@[simp] lemma to_nat_of_nat (p : subformula L m n) : of_nat L m n p.to_nat = some p :=
by simp[to_nat, of_nat]

@[simp] lemma of_nat_to_nat (p : subformula L m n) : to_nat p.mlift = to_nat p :=
by simp[to_nat]

@[simp] lemma of_nat_to_uniform (p : subformula L m n) : encodable.decode₂ (uniform_subformula L n) p.to_nat = p.to_uniform :=
by simp[to_nat]; refl

lemma of_nat_eq_some {e} {p : subformula L m n} : of_nat L m n e = some p ↔ p.to_nat = e :=
by { simp[of_nat, to_nat, encodable.decode₂_eq_some, dite_eq_iff], split,
  { simp, rintros _ rfl h rfl, simp },
  { rintros rfl, refine ⟨p.to_uniform, rfl, by simp⟩ } }

lemma of_nat_eq_som {m₁ m₂} {p : subformula L m₁ n} {q : subformula L m₂ n} : p.to_nat = q.to_nat ↔ p.to_uniform = q.to_uniform :=
by simp[to_nat]


@[simp] lemma to_nat_inj {p q : subformula L m n} : p.to_nat = q.to_nat ↔ p = q :=
by { have : q = p ↔ p.to_nat = q.to_nat, by simpa using @of_nat_eq_some _ _ _ _ _ q.to_nat p,
     simp[←this], exact comm }

end encode

end subformula

end Tait
end fol