import fopl

universe u

namespace fopl
variables {L : language.{u}}

def theory.sf (T : theory L) : theory L := {p | ∃ q : formula L, q ∈ T ∧ p = q^1}

prefix `⤊`:max := theory.sf

@[reducible] def theory.sf_itr (T : theory L) : ℕ → theory L
| 0     := T
| (n+1) := ⤊(theory.sf_itr n)

instance sf_itr_pow : has_pow (theory L) ℕ := ⟨theory.sf_itr⟩

@[simp] lemma theory.sf_itr_0 (T : theory L) : T^0 = T := rfl
lemma theory.sf_itr_succ (T : theory L) (n) : T^(n+1) = ⤊(T^n) := rfl

lemma theory.pow_add (T : theory L) (i j : ℕ) : (T^i)^j = T^(i + j) :=
by { induction j with j IH; simp[theory.sf_itr_succ, ←nat.add_one, ←add_assoc], simp[IH] }

class closed_theory (T : theory L) := (cl : ∀ {p}, p ∈ T → sentence p)

def proper_at (n : ℕ) (T : theory L) : Prop := ∀ (p : formula L) (s), p ∈ T → p.rew (s^n) ∈ T

def proper_theory'_at (n : ℕ) (T : theory L) : Prop := ∀ (p : formula L) (s : ℕ → term L),
  p ∈ T → p.rew (λ x, if x < n then #x else s (x - n)) ∈ T

def ordered_p (T : theory L) : Prop := ∀ (p : formula L), p ∈ T → p^1 ∈ T

class ordered (T : theory L) := (ordered : ordered_p T)

lemma oedered_p_theory_sf (T : theory L) : ordered_p T → ordered_p ⤊T := λ h p hyp,
by { rcases hyp with ⟨p', hyp_p, rfl⟩, refine ⟨p'^1, _, rfl⟩, exact h _ hyp_p }

instance ordered_theory_sf {T : theory L} [od : ordered T] :
  ordered ⤊T := ⟨oedered_p_theory_sf _ od.ordered⟩

instance ordered_theory_sf_itr {T : theory L} [od : ordered T] : ∀ n : ℕ, ordered (T^n)
| 0 := od
| (n+1) := @fopl.ordered_theory_sf _ _  (ordered_theory_sf_itr n)

class proper_theory (T : theory L) := (proper : proper_at 0 T)

instance ordered_proper {T : theory L} [proper_theory T] : ordered T :=
⟨λ p h, proper_theory.proper _ (λ x, #(x+1)) h⟩

lemma proper_theory.proper0 {T : theory L} [proper_theory T] :
  ∀ {p : formula L} {s}, p ∈ T → p.rew s ∈ T := @proper_theory.proper _ T _

instance : closed_theory (∅ : theory L) := ⟨λ _ h, by exfalso; exact h⟩

instance : proper_theory (∅ : theory L) := ⟨λ _ _ h, by exfalso; exact h⟩

instance : proper_theory (set.univ : theory L) := ⟨λ p s h, by simp⟩

def openform : theory L := {p | p.Open = tt}

instance : proper_theory (openform : theory L) :=
⟨λ p s h, by { induction p; simp[openform] at*; simp* at* }⟩

lemma theory_sf_itr_eq {T : theory L} : ∀ {i : ℕ},
  T^i = {p | ∃ q : formula L, q ∈ T ∧ p = q^i}
| 0      := by simp
| (i+1)  := by { simp[theory.sf_itr_succ, @theory_sf_itr_eq i, theory.sf], ext p,
  simp, refine ⟨λ h, _, λ h, _⟩,
  { rcases h with ⟨q1, ⟨q2, h, rfl⟩, rfl⟩, refine ⟨q2, h, by simp[formula.pow_add]⟩ },
  { rcases h with ⟨q, h, rfl⟩, refine ⟨q^i, ⟨q, h, rfl⟩, by simp[formula.pow_add]⟩ } }

lemma sentence_mem_theory_sf_itr {T : theory L} {p : formula L} (a : sentence p) (n : ℕ) :
  p ∈ T → p ∈ T^n := λ h,
by { have : p.rew (λ x, #(x+n)) = p, exact formula.sentence_rew a _, rw ←this,
     simp[theory_sf_itr_eq], refine ⟨p, h, rfl⟩ }

lemma proper_sf_inclusion (T : theory L) [proper_theory T] : ∀ {n m : ℕ} (h : n ≤ m),
  T^m ⊆ T^n :=
begin
  suffices : ∀ {n m : ℕ}, T^(n+m) ⊆ T^n,
  { intros n m eqn p hyp, have e : m = n + (m - n), exact (nat.add_sub_of_le eqn).symm, 
    rw e at hyp,
    exact this hyp },
  intros n m p h,
  induction m with m IH, { exact h },
  { suffices : p ∈ T^(n + m), from IH this, simp[theory_sf_itr_eq] at h ⊢, rcases h with ⟨q, h, rfl⟩,
    have : q^1 ∈ T, from @proper_theory.proper _ T _ _ (λ x, #(x + 1)) h,
    refine ⟨q^1, this, _⟩,
    simp[formula.pow_add, formula.nested_rew, nat.succ_add_eq_succ_add, ←add_assoc] }
end

lemma ordered_inclusion (T : theory L) [ordered T] : ⤊T ⊆ T := λ p h,
by { rcases h with ⟨p, hyp, rfl⟩, exact ordered.ordered _ hyp }

lemma proper_theory_sf_itr {n : ℕ} {T : theory L} (pp : proper_at n T) : ∀ m,
  proper_at (n+m) (T^m)
| 0     := by { simp, exact @pp }
| (m+1) := λ p s h, by { rcases h with ⟨p, hyp_p, rfl⟩, rw ←add_assoc,
     show (p^1).rew ((s^(n + m))^1) ∈ ⤊(T^m), simp[←formula.pow_rew_distrib],
     refine ⟨p.rew (s^(n+m)), proper_theory_sf_itr m _ s hyp_p, rfl⟩ }

lemma properc_theory_sf_itr {T : theory L} [pp : proper_theory T] {n} :
  proper_at n (T^n) := by { have := proper_theory_sf_itr pp.proper n, simp at this, exact this, }

lemma closed_proper {T : theory L} [cl : closed_theory T] : proper_at 0 T :=
λ p s h, by { simp[@closed_theory.cl _ _ cl _ h], exact h }

@[simp] lemma closed_theory_sf_eq {T : theory L} [cl : closed_theory T] : ⤊T = T :=
by { ext p, refine ⟨λ hyp, _, λ hyp, _⟩, rcases hyp with ⟨p, hyp_p, rfl⟩,
     simp[closed_theory.cl hyp_p, hyp_p],
     rw ← (formula.sentence_sf (closed_theory.cl hyp)), refine ⟨p, hyp, rfl⟩ }

@[simp] lemma closed_pow_eq (T : theory L) [cl : closed_theory T] (i : ℕ) : T^i = T :=
by { ext p, simp[theory_sf_itr_eq], refine ⟨λ hyp, _, λ hyp, _⟩, rcases hyp with ⟨p, hyp_p, rfl⟩,
     simp[closed_theory.cl hyp_p, hyp_p],
     rw ← (formula.sentence_sf (closed_theory.cl hyp)), refine ⟨p, hyp, rfl⟩ }

lemma sf_dsb (T : theory L) (p : formula L) : ⤊T +{ p^1 } = ⤊(T +{ p }) :=
begin
  ext x, split; intros h,
  { cases h with hx, refine ⟨p, by simp, hx⟩,
    rcases h with ⟨p', hp, rfl⟩, refine ⟨p', by simp[hp], rfl⟩ },
  { rcases h with ⟨q, hq, rfl⟩, rcases hq with (rfl | hq); simp,
    refine or.inr ⟨q, hq, rfl⟩ }
end

end fopl