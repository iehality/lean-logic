import fopl

universe u

namespace fopl
variables {L : language.{u}}

def theory (L : language) := set (formula L)

notation `theory `L:max := set (formula L)

def theory.sf (T : theory L) : theory L := {p | ∃ q : formula L, q ∈ T ∧ p = q.sf}

prefix `⇑`:max := theory.sf

@[simp, reducible] def theory.sf_itr (T : theory L) : ℕ → theory L
| 0     := T
| (n+1) := ⇑(theory.sf_itr n)

instance sf_itr_pow : has_pow (theory L) ℕ := ⟨theory.sf_itr⟩

@[simp] lemma theory.sf_itr_0 (T : theory L) : T^0 = T := rfl
@[simp] lemma theory.sf_itr_succ (T : theory L) (n) : T^(n+1) = ⇑(T^n) := rfl

lemma theory.sf_itr_add (T : theory L) (i j : ℕ) : (T^i)^j = T^(i + j) :=
by { induction j with j IH; simp[←nat.add_one, ←add_assoc], simp[IH] }

inductive theory.add (T : theory L) (p : formula L) : theory L 
| new : theory.add p
| old : ∀ {q}, q ∈ T → theory.add q

notation T`+{`:max p`}` := theory.add T p

class closed_theory (T : theory L) := (cl : ∀ {p}, p ∈ T → sentence p)

class extend (T₀ T : theory L) := (ss : T₀ ⊆ T)

def proper_at (n : ℕ) (T : theory L) : Prop := ∀ (p : formula L) (s), p ∈ T → p.rew (s^n) ∈ T

def ordered_p (T : theory L) : Prop := ∀ (p : formula L), p ∈ T → p.sf ∈ T

class ordered (T : theory L) := (ordered : ordered_p T)

lemma oedered_p_theory_sf (T : theory L) : ordered_p T → ordered_p ⇑T := λ h p hyp,
by { rcases hyp with ⟨p', hyp_p, rfl⟩, refine ⟨p'.sf, _, rfl⟩, exact h _ hyp_p }

instance ordered_theory_sf {T : theory L} [od : ordered T] :
  ordered ⇑T := ⟨oedered_p_theory_sf _ od.ordered⟩

instance ordered_theory_sf_itr {T : theory L} [od : ordered T] : ∀ n : ℕ, ordered (T^n)
| 0 := od
| (n+1) := @fopl.ordered_theory_sf _ _  (ordered_theory_sf_itr n)

class proper (n : ℕ) (T : theory L) := (proper : proper_at n T)

instance ordered_proper {T : theory L} [pp : proper 0 T] : ordered T :=
⟨λ p h, by { have := pp.proper, exact this _ (λ x, #(x+1)) h }⟩

lemma proper.proper0 {T : theory L} [proper 0 T] :
  ∀ {p : formula L} {s}, p ∈ T → p.rew s ∈ T := @proper.proper _ 0 T _

instance : closed_theory (∅ : theory L) := ⟨λ _ h, by exfalso; exact h⟩

instance (n) : proper n (∅ : theory L) := ⟨λ _ _ h, by exfalso; exact h⟩

instance (n) : proper n (set.univ : theory L) := ⟨λ p s h, by simp⟩

def openform : theory L := {p | p.Open = tt}

instance (n) : proper n (openform : theory L) :=
⟨λ p s h, by { induction p; simp[openform] at*; simp* at* }⟩

lemma theory_sf_itr_eq {T : theory L} : ∀ {n},
  T^n = {p | ∃ q : formula L, q ∈ T ∧ p = q.sf_itr n}
| 0      := by simp[formula.sf_itr]
| (n+1)  := by { simp[@theory_sf_itr_eq n, theory.sf, formula.sf_itr], ext p,
  simp, refine ⟨λ h, _, λ h, _⟩,
  { rcases h with ⟨q1, ⟨q2, h, rfl⟩, rfl⟩, refine ⟨q2, h, _⟩,
    simp[formula.sf, formula.nested_rew, add_assoc] },
  { rcases h with ⟨q, h, rfl⟩, refine ⟨q.rew (λ x, #(x + n)), ⟨q, h, rfl⟩, _⟩,
    simp[formula.sf, formula.nested_rew, add_assoc] } }

lemma sentence_mem_theory_sf_itr {T : theory L} {p : formula L} (a : sentence p) (n : ℕ) :
  p ∈ T → p ∈ T^n := λ h,
by { have : p.rew (λ x, #(x+n)) = p, exact formula.sentence_rew a _, rw ←this,
     simp[theory_sf_itr_eq], refine ⟨p, h, rfl⟩ }

lemma proper_sf_inclusion (T : theory L) [proper 0 T] : ∀ {n m : ℕ} (h : n ≤ m),
  T^m ⊆ T^n :=
begin
  suffices : ∀ {n m : ℕ}, T^(n+m) ⊆ T^n,
  { intros n m eqn p hyp, have e : m = n + (m - n), exact (nat.add_sub_of_le eqn).symm, 
    rw e at hyp,
    exact this hyp },
  intros n m p h,
  induction m with m IH, { exact h },
  { suffices : p ∈ T^(n + m), from IH this, simp[theory_sf_itr_eq] at h ⊢, rcases h with ⟨q, h, rfl⟩,
    have := @proper.proper _ 0 T _ _ shift h,
    refine ⟨q.sf, this, _⟩,
    simp[formula.sf_itr, formula.sf, formula.nested_rew, nat.succ_add_eq_succ_add, ←add_assoc] }
end

lemma ordered_inclusion (T : theory L) [ordered T] : ⇑T ⊆ T := λ p h,
by { rcases h with ⟨p, hyp, rfl⟩, exact ordered.ordered _ hyp }

lemma formula.sf_rew_sf_eq (s) (p : formula L) : p.sf.rew (s^1) = (p.rew s).sf :=
by { simp[formula.sf, formula.nested_rew] }

lemma proper_theory_sf_itr {n : ℕ} {T : theory L} (pp : proper_at n T) : ∀ m,
  proper_at (n+m) (T^m)
| 0     := by { simp, exact @pp }
| (m+1) := λ p s h, by { rcases h with ⟨p, hyp_p, rfl⟩, rw ←add_assoc,
     show p.sf.rew ((s^(n + m))^1) ∈ ⇑(T^m), simp[formula.sf_rew_sf_eq],
     refine ⟨p.rew (s^(n+m)), proper_theory_sf_itr m _ s hyp_p, rfl⟩ }

instance properc_theory_sf_itr {T : theory L} [pp : proper 0 T] {n} :
  proper n (T^n) := ⟨by { have := proper_theory_sf_itr pp.proper n, simp* at* }⟩ 

lemma closed_proper {T : theory L} [cl : closed_theory T] : proper_at 0 T :=
λ p s h, by { simp[@closed_theory.cl _ _ cl _ h], exact h }

@[simp] lemma closed_theory_sf_eq {T : theory L} [cl : closed_theory T] : ⇑T = T :=
by { ext p, refine ⟨λ hyp, _, λ hyp, _⟩, rcases hyp with ⟨p, hyp_p, rfl⟩,
     simp[formula.sf, formula.sentence_rew (closed_theory.cl hyp_p), hyp_p],
     rw ← (formula.sentence_sf (closed_theory.cl hyp)), refine ⟨p, hyp, rfl⟩ }

lemma sf_dsb (T : theory L) (p : formula L) : ⇑T+{p.sf} = ⇑(T+{p}) :=
begin
  ext x, split; intros h,
  { cases h with h hx, refine ⟨p, theory.add.new, rfl⟩,
    rcases hx with ⟨p, hp, rfl⟩, refine ⟨p, theory.add.old hp, rfl⟩ },
  { rcases h with ⟨q, hq, rfl⟩, cases hq with hq hq, refine theory.add.new,
    refine theory.add.old ⟨q, hq, rfl⟩ }
end

end fopl