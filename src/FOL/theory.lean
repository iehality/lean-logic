import FOL.fol

universe u

namespace fol
open term formula
variables {L : language.{u}}

def Theory.sf (T : Theory L) : Theory L := {p | ∃ q : formula L, q ∈ T ∧ p = q^1}

prefix `⤊`:max := Theory.sf

@[reducible] def Theory.sf_itr (T : Theory L) : ℕ → Theory L
| 0     := T
| (n+1) := ⤊(Theory.sf_itr n)

instance sf_itr_pow : has_pow (Theory L) ℕ := ⟨Theory.sf_itr⟩

@[simp] lemma Theory.sf_itr_0 (T : Theory L) : T^0 = T := rfl

lemma Theory.sf_itr_succ (T : Theory L) (n) : T^(n+1) = ⤊(T^n) := rfl

lemma Theory.pow_add (T : Theory L) (i j : ℕ) : (T^i)^j = T^(i + j) :=
by { induction j with j IH; simp[Theory.sf_itr_succ, ←nat.add_one, ←add_assoc], simp[IH] }

class closed_Theory (T : Theory L) := (cl : ∀ {p}, p ∈ T → is_sentence p)

attribute [simp] closed_Theory.cl

def proper_at (n : ℕ) (T : Theory L) : Prop := ∀ (p : formula L) (s), p ∈ T → p.rew (s^n) ∈ T

def proper_Theory'_at (n : ℕ) (T : Theory L) : Prop := ∀ (p : formula L) (s : ℕ → term L),
  p ∈ T → p.rew (λ x, if x < n then #x else s (x - n)) ∈ T

def ordered_p (T : Theory L) : Prop := ∀ (p : formula L), p ∈ T → p^1 ∈ T

class ordered (T : Theory L) := (ordered : ordered_p T)

lemma oedered_p_Theory_sf (T : Theory L) : ordered_p T → ordered_p ⤊T := λ h p hyp,
by { rcases hyp with ⟨p', hyp_p, rfl⟩, refine ⟨p'^1, _, rfl⟩, exact h _ hyp_p }

instance ordered_Theory_sf {T : Theory L} [od : ordered T] :
  ordered ⤊T := ⟨oedered_p_Theory_sf _ od.ordered⟩

instance ordered_Theory_sf_itr {T : Theory L} [od : ordered T] : ∀ n : ℕ, ordered (T^n)
| 0 := od
| (n+1) := @fol.ordered_Theory_sf _ _  (ordered_Theory_sf_itr n)

-- 自由変項の書き換えによって変化しない論理式の集合
class proper_Theory (T : Theory L) := (proper : ∀ (p : formula L) (s), p ∈ T → p.rew s ∈ T)

@[simp] lemma proper_Theory.rew_mem {T : Theory L} [proper_Theory T] {p : formula L} (h : p ∈ T) {s} :
  p.rew s ∈ T := proper_Theory.proper p s h

instance ordered_proper {T : Theory L} [proper_Theory T] : ordered T :=
⟨λ p h, proper_Theory.proper _ (λ x, #(x+1)) h⟩

lemma proper_Theory.proper0 {T : Theory L} [proper_Theory T] :
  ∀ {p : formula L} {s}, p ∈ T → p.rew s ∈ T := @proper_Theory.proper _ T _

instance : closed_Theory (∅ : Theory L) := ⟨λ _ h, by exfalso; exact h⟩

instance : proper_Theory (∅ : Theory L) := ⟨λ _ _ h, by exfalso; exact h⟩

instance : proper_Theory (set.univ : Theory L) := ⟨λ p s h, by simp⟩

def openform : Theory L := {p | p.is_open = tt}

instance : proper_Theory (openform : Theory L) :=
⟨λ p s h, by { induction p; simp[openform] at*; simp* at* }⟩

lemma Theory_sf_def {T : Theory L} :
  ⤊T = {p | ∃ q : formula L, q ∈ T ∧ p = q^1} :=
by { simp[Theory.sf] }

lemma Theory_sf_itr_eq {T : Theory L} : ∀ {i : ℕ},
  T^i = {p | ∃ q : formula L, q ∈ T ∧ p = q^i}
| 0      := by simp
| (i+1)  := by { simp[Theory.sf_itr_succ, @Theory_sf_itr_eq i, Theory.sf], ext p,
  simp, refine ⟨λ h, _, λ h, _⟩,
  { rcases h with ⟨q1, ⟨q2, h, rfl⟩, rfl⟩, refine ⟨q2, h, by simp[formula.pow_add]⟩ },
  { rcases h with ⟨q, h, rfl⟩, refine ⟨q^i, ⟨q, h, rfl⟩, by simp[formula.pow_add]⟩ } }

lemma sf_eq_image {T : Theory L} :
  ⤊T = (λ p, p^1) '' T :=
by { ext p, simp[Theory_sf_def], tauto }

lemma pow_eq_image {T : Theory L} {i : ℕ} :
  T^i = (λ p, p^i) '' T :=
by { ext p, simp[Theory_sf_itr_eq], tauto }

lemma is_sentence_mem_Theory_sf_itr {T : Theory L} {p : formula L} (a : is_sentence p) (n : ℕ) :
  p ∈ T → p ∈ T^n := λ h,
by { have : p.rew (λ x, #(x+n)) = p, exact formula.is_sentence_rew a _, rw ←this,
     simp[Theory_sf_itr_eq], refine ⟨p, h, rfl⟩ }

lemma proper_sf_inclusion (T : Theory L) [proper_Theory T] : ∀ {n m : ℕ} (h : n ≤ m),
  T^m ⊆ T^n :=
begin
  suffices : ∀ {n m : ℕ}, T^(n+m) ⊆ T^n,
  { intros n m eqn p hyp, have e : m = n + (m - n), exact (nat.add_sub_of_le eqn).symm, 
    rw e at hyp,
    exact this hyp },
  intros n m p h,
  induction m with m IH, { exact h },
  { suffices : p ∈ T^(n + m), from IH this, simp[Theory_sf_itr_eq] at h ⊢, rcases h with ⟨q, h, rfl⟩,
    have : q^1 ∈ T, from @proper_Theory.proper _ T _ _ (λ x, #(x + 1)) h,
    refine ⟨q^1, this, _⟩,
    simp[formula.pow_add, formula.nested_rew, nat.succ_add_eq_succ_add, ←add_assoc] }
end

lemma ordered_inclusion (T : Theory L) [ordered T] : ⤊T ⊆ T := λ p h,
by { rcases h with ⟨p, hyp, rfl⟩, exact ordered.ordered _ hyp }

lemma proper_Theory_sf_itr {n : ℕ} {T : Theory L} (pp : proper_at n T) : ∀ m,
  proper_at (n+m) (T^m)
| 0     := by { simp, exact @pp }
| (m+1) := λ p s h, by { rcases h with ⟨p, hyp_p, rfl⟩, rw ←add_assoc,
     show (p^1).rew ((s^(n + m))^1) ∈ ⤊(T^m), simp[←formula.pow_rew_distrib],
     refine ⟨p.rew (s^(n+m)), proper_Theory_sf_itr m _ s hyp_p, rfl⟩ }

lemma properc_Theory_sf_itr {T : Theory L} [proper_Theory T] {n} :
  proper_at n (T^n) :=
by { have := proper_Theory_sf_itr (show proper_at 0 T, from proper_Theory.proper) n, simp at this, exact this}

lemma closed_proper {T : Theory L} [cl : closed_Theory T] : proper_at 0 T :=
λ p s h, by { simp[@closed_Theory.cl _ _ cl _ h], exact h }

@[simp] lemma closed_Theory_sf_eq {T : Theory L} [cl : closed_Theory T] : ⤊T = T :=
by { ext p, refine ⟨λ hyp, _, λ hyp, _⟩, rcases hyp with ⟨p, hyp_p, rfl⟩,
     simp[closed_Theory.cl hyp_p, hyp_p],
     rw ← (formula.is_sentence_sf (closed_Theory.cl hyp)), refine ⟨p, hyp, rfl⟩ }

@[simp] lemma closed_Theory_pow_eq (T : Theory L) [cl : closed_Theory T] (i : ℕ) : T^i = T :=
by { ext p, simp[Theory_sf_itr_eq], refine ⟨λ hyp, _, λ hyp, _⟩, rcases hyp with ⟨p, hyp_p, rfl⟩,
     simp[closed_Theory.cl hyp_p, hyp_p],
     rw ← (formula.is_sentence_sf (closed_Theory.cl hyp)), refine ⟨p, hyp, rfl⟩ }

lemma sf_dsb (T : Theory L) (p : formula L) : ⤊T +{ p^1 } = ⤊(T +{ p }) :=
begin
  ext x, split; intros h,
  { cases h with hx, refine ⟨p, by simp, hx⟩,
    rcases h with ⟨p', hp, rfl⟩, refine ⟨p', by simp[hp], rfl⟩ },
  { rcases h with ⟨q, hq, rfl⟩, rcases hq with (rfl | hq); simp,
    refine or.inr ⟨q, hq, rfl⟩ }
end

lemma pow_dsb (T : Theory L) (p : formula L) (k : ℕ) : (T +{ p })^k = (T^k) +{ p^k } :=
by induction k with k IH; simp[Theory.sf_itr_succ, ←sf_dsb, formula.pow_add, *]

lemma sf_union (T U : Theory L) : ⤊(T ∪ U) = ⤊T ∪ ⤊U :=
begin
  ext p, split,
  { rintros ⟨p, (mem | mem), rfl⟩,
    { refine or.inl _, refine ⟨p, mem, rfl⟩ },
    { refine or.inr _, refine ⟨p, mem, rfl⟩ } },
  { rintros (⟨p, mem, rfl⟩ | ⟨p, mem, rfl⟩),
    { refine ⟨p, or.inl mem, rfl⟩ },
    { refine ⟨p, or.inr mem, rfl⟩ } }
end

lemma pow_union (T U : Theory L) (k : ℕ) : (T ∪ U)^k = T^k ∪ U^k :=
by induction k with k IH; simp[←nat.add_one, Theory.sf_itr_succ, sf_union, *]

@[simp] lemma sf_ss {T U : Theory L} : ⤊T ⊆ ⤊U ↔ T ⊆ U :=
⟨λ h p mem, by {
  have : p^1 ∈ ⤊T, from ⟨p, mem, rfl⟩,
  rcases h this with ⟨q, h, eqn⟩, simp at eqn,
  simp[eqn, h] },
 λ h p, by { rintros ⟨p, mem, rfl⟩,
  refine ⟨p, h mem, rfl⟩ }⟩

@[simp] lemma pow_ss {T U : Theory L} {i : ℕ} : T^i ⊆ U^i ↔ T ⊆ U :=
by induction i with i; simp[←nat.add_one, Theory.sf_itr_succ, *]

instance union_closed (T U : Theory L) [closed_Theory T] [closed_Theory U] : closed_Theory (T ∪ U) :=
⟨λ p, by { simp, rintros (mem | mem), { exact closed_Theory.cl mem }, {  exact closed_Theory.cl mem } }⟩

end fol