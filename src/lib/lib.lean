import
  tactic
  computability.primrec
  computability.partrec
  computability.partrec_code
  computability.halting
  data.pfun
  order
  init.data.list
  init.data.subtype
  data.list.dedup
  data.W.basic

import lib.notation

universes u v

attribute [instance, priority 0] classical.prop_decidable

namespace nat

lemma mkpair_eq_iff {n m l : ℕ} : n.mkpair m = l ↔ n = l.unpair.1 ∧ m = l.unpair.2 :=
by { split,
  { intros e, rw ←e, simp },
  { intros h, simp[h], } }

@[simp] lemma unpair0 : (1 : ℕ).unpair = (0, 1) :=
by { have h : nat.mkpair 0 1 = 1, { simpa },
     suffices : nat.unpair (nat.mkpair 0 1) = (0, 1), simp[h] at this, exact this,
     simp }

lemma pos_succ {n : ℕ} (h : 0 < n) : n = (n - 1) + 1 :=
(succ_pred_eq_of_pos h).symm

lemma pos_pred_add {n m : ℕ} (h : m ≤ n) (l) : n - m + l = n + l - m :=
by { omega }

@[simp] lemma lt_max_add_one_left (m n : ℕ) : m < max m n + 1 := lt_succ_iff.mpr (le_max_left m n)

@[simp] lemma lt_max_add_one_right (m n : ℕ) : n < max m n + 1 := lt_succ_iff.mpr (le_max_right m n)


end nat

namespace function
variables {α : Type*}

def fun_pow (f : α → α) : ℕ → α → α
| 0     a := a
| (n+1) a := f (fun_pow n a)
infix ` ^ᶠ `:60 := fun_pow

end function

namespace vector
variables {α : Type*} {n : ℕ}

lemma tail_nth : ∀ (v : vector α (n + 1)) (i : fin n), v.tail.nth i = v.nth ⟨i + 1, by simp; exact i.property⟩
| ⟨ [], h ⟩ i := by simp[tail, nth]
| ⟨ (a :: v), h ⟩ p := by { simp[tail, nth], refl }

@[simp] lemma succ_nth (v : vector α n) (a : α) (i : ℕ) (h : i + 1 < n + 1) :
  (a ::ᵥ v).nth ⟨i + 1, h⟩ = v.nth ⟨i, nat.succ_lt_succ_iff.mp h⟩ :=
by { have := vector.nth_tail (a ::ᵥ v) ⟨i, nat.succ_lt_succ_iff.mp h⟩, simp at this, simp[this] }

@[simp] lemma succ_nth' (v : vector α n) (a : α) (i : fin n)  :
  (a ::ᵥ v).nth i.succ = v.nth i := by simp[show i.succ = ⟨i + 1, nat.succ_lt_succ i.property⟩, from fin.ext (by simp)]

@[simp] lemma succ_nth_1 (v : vector α (n + 1)) (a : α) :
  (a ::ᵥ v).nth 1 = v.nth 0 := succ_nth' v a 0

@[simp] lemma cons_inj (a₁ a₂ : α) (v₁ v₂ : vector α n) :
  (a₁ ::ᵥ v₁) = (a₂ ::ᵥ v₂) ↔ a₁ = a₂ ∧ v₁ = v₂ :=
⟨by intros h; refine ⟨by simpa using congr_arg head h, by simpa using congr_arg tail h⟩,
 by rintros ⟨rfl, rfl⟩; refl⟩

end vector

def finitary (α : Type*) (n : ℕ) := fin n → α

namespace fin

def add' {n} (i : fin n) : fin (n + 1) := ⟨i, nat.lt.step i.property⟩

lemma cases_inv {n} (i : fin (n + 1)) : (∃ i' : fin n, i = add' i') ∨ i = ⟨n, lt_add_one n⟩ :=
by { have : ↑i < n ∨ ↑i = n, exact nat.lt_succ_iff_lt_or_eq.mp i.property, cases this,
     { left, refine ⟨⟨i, this⟩, fin.eq_of_veq _⟩, simp[add'] },
     { right, apply fin.eq_of_veq, simp[this] } }

@[simp] lemma fin_le {n} (i : fin n) : ↑i < n := i.property

@[simp] lemma fin_le_succ {n} (i : fin n) : ↑i < n + 1 := nat.lt.step i.property

def psucc {n} (m : ℕ) : fin n → fin (n + 1) :=
λ i, if ↑i < m then i.cast_succ else i.succ

section psucc
variables {n : ℕ}

@[simp] lemma psucc_zero : (psucc 0 : fin n → fin (n + 1)) = fin.succ :=
funext (λ j, by simp[psucc])

lemma succ_fix_zero_of_lt {i : fin n} {m : ℕ} (h : ↑i < m) : psucc m i = i.cast_succ := by simp[psucc, h]

lemma succ_fix_zero_of_ge {i : fin n} {m : ℕ} (h : ↑i ≥ m) : psucc m i = i.succ := by simp[psucc, not_lt.mpr h]

end psucc

lemma eq_last_or_eq_cast_succ {n : ℕ} : ∀ (i : fin (n + 1)),
i = last n ∨ ∃ (j : fin n), i = j.cast_succ :=
@last_cases n (λ i, i = last n ∨ ∃ (j : fin n), i = j.cast_succ) (by simp) (by simp)

lemma eq_zero_or_eq_last_or_interval {n : ℕ} (i : fin (n + 1 + 1)) :
i = 0 ∨ i = last (n + 1) ∨ ∃ (j: fin n), i = j.cast_succ.succ :=
begin
  rcases fin.eq_zero_or_eq_succ i with (eqn | ⟨j₁, h₁⟩),
  { exact or.inl eqn },
  { rcases eq_last_or_eq_cast_succ i with (eqn | ⟨j₂, h₂⟩),
    { refine (or.inr $ or.inl eqn) },
    { refine (or.inr $ or.inr _),
      rcases eq_last_or_eq_cast_succ j₁ with (rfl | ⟨j, rfl⟩),
      { exfalso,
        have : j₂.cast_succ = last n.succ, by simpa[←h₂] using h₁,
        have e : j₂.val = n.succ, simpa using congr_arg fin.val this,
        have : j₂.val < n + 1, from j₂.property,
        simp[e] at this, contradiction },
      { exact ⟨j, h₁⟩ } } }
end

section cases
variables {n : ℕ} {C : Sort*} {a b : C} {s : fin n → C}

-- finitary.cons の書き換え
@[elab_as_eliminator] def left_concat {C : Sort*} (hzero : C) (hsucc : fin n → C) : fin (n + 1) → C := @cases n (λ _, C) hzero hsucc

infixr (name:= left_concat) ` *> `:70 := left_concat

@[simp] lemma left_concat_zero : (a *> s) 0 = a := by simp[left_concat]

@[simp] lemma left_concat_succ (i : fin n) : (a *> s) i.succ = s i := by simp[left_concat]

@[simp] lemma left_concat_comp_succ : (a *> s) ∘ fin.succ = s := funext(by simp)

@[elab_as_eliminator, elab_strategy]
def right_concat (hcast : fin n → C) (hlast : C) : fin (n + 1) → C := @last_cases n (λ _, C) hlast hcast

infixl (name:= right_concat) ` <* `:70 := right_concat

@[simp] lemma right_concat_last : (s <* a) (last n) = a := by simp[right_concat]

@[simp] lemma right_concat_cast_succ (i : fin n) : (s <* a) i.cast_succ = s i := by simp[right_concat]

@[simp] lemma left_concat_comp_cast : (s <* a) ∘ fin.cast_succ = s := funext(by simp)

@[simp] lemma cases_one
  {a : C} {s : fin 0 → C} (x : fin 1) : (a *> s) x = a :=
by rw [show x = 0, by simp]; simp

@[simp] lemma last_cases_one
  {a : C} {s : fin 0 → C} (x : fin 1) : (s <* a) x = a :=
by rw [show x = last 0, by simp]; simp

lemma left_right_concat_assoc :
  a *> (s <* b) = (a *> s) <* b :=
funext (by { intros x, rcases eq_zero_or_eq_last_or_interval x with (rfl | h | ⟨x', rfl⟩),
  { show (a *> (s <* b)) 0 = ((a *> s) <* b) (cast_succ 0),
    simp only [left_concat_zero, right_concat_cast_succ] },
  { suffices : (a *> (s <* b)) (last n).succ = ((a *> s) <* b) (last $ n + 1),
    by simpa only [←h, succ_last] using this,
    simp only [left_concat_succ, right_concat_last] },
  { suffices : (a *> (s <* b)) x'.cast_succ.succ = ((a *> s) <* b) x'.succ.cast_succ,
    by simpa only [succ_cast_succ] using this,
    simp } })

lemma comp_left_concat {α : Sort*} (f : C → α) (a : C) (s : fin n → C) : f ∘ (a *> s) = f a *> f ∘ s :=
funext (λ i, cases (by simp) (by simp) i)

lemma comp_right_concat {α : Sort*} (f : C → α) (a : C) (s : fin n → C) : f ∘ (s <* a) = f ∘ s <* f a :=
funext (λ i, by refine last_cases _ _ i; simp)

lemma left_concat_eq {α} {n} (f : fin (n + 1) → α) : f 0 *> f ∘ fin.succ = f :=
funext (λ i, by refine cases _ _ i; simp)

lemma right_concat_eq {α} {n} (f : fin (n + 1) → α) : f ∘ fin.cast_succ <* f (last n) = f :=
funext (λ i, by refine last_cases _ _ i; simp)

protected def nil : fin 0 → C := fin_zero_elim

lemma concat_zero {α} {x : α} : x *> fin.nil = fin.nil <* x :=
by funext; simp

@[simp] lemma left_concat_inj {a₁ a₂ : C} {s₁ s₂ : fin n → C} :
  a₁ *> s₁ = a₂ *> s₂ ↔ a₁ = a₂ ∧ s₁ = s₂ :=
⟨by { intros h, refine ⟨by simpa using congr_fun h 0, _⟩,
      simpa using congr_arg2 (∘) h (@rfl _ fin.succ) },
 by { rintros ⟨rfl, rfl⟩, refl }⟩

@[simp] lemma right_concat_inj {a₁ a₂ : C} {s₁ s₂ : fin n → C} :
  s₁ <* a₁ = s₂ <* a₂ ↔ a₁ = a₂ ∧ s₁ = s₂ :=
⟨by { intros h, refine ⟨by simpa using congr_fun h (last n), _⟩,
      simpa using congr_arg (λ s, s ∘ fin.cast_succ) h },
 by { rintros ⟨rfl, rfl⟩, refl }⟩

@[simp] lemma zero_concat_succ : (0 *> fin.succ : fin (n + 1) → fin (n + 1)) = id :=
by simpa using left_concat_eq id

@[simp] lemma cast_concat_last : (fin.cast_succ <* fin.last n) = id :=
by simpa using right_concat_eq id

end cases

end fin

namespace finitary
variables {α : Type*} {β : Type*}
open vector

def of_vec_of_fn : Π {n}, (fin n → α) → vector α n
| 0 f := nil
| (n+1) f := cons (f 0) (of_fn (λi, f i.succ))

def Max [linear_order α] (d : α) : ∀ {n}, finitary α n → α
| 0     _ := d
| (n+1) f := max (f ⟨n, lt_add_one n⟩) (@Max n (λ i, f i.add'))

@[elab_as_eliminator]
lemma finitary_induction (p : Π {n}, finitary α n → Prop)
  (nil : ∀ f : finitary α 0, p f)
  (cons : ∀ {n} (a : α) (f : finitary α n), p f → @p (n + 1) (λ i, if h : ↑i < n then f ⟨↑i, h⟩ else a)) :
  ∀ {n} (f : finitary α n), p f :=
by { intros n, induction n with n IH, refine nil, intros f,
      let f' : finitary α n := λ i, f ⟨↑i, nat.lt.step i.property⟩,
      have : f = (λ i, if h : ↑i < n then f' ⟨↑i, h⟩ else f n),
      { funext i,
        have : ↑i < n ∨ ↑i = n, exact nat.lt_succ_iff_lt_or_eq.mp i.property,
        cases this; simp [this], { simp[f'], unfold_coes, simp },
        { simp[←this] } },
      rw [this], refine cons _ _ (IH _) }

def Max_le [linear_order α] (d : α) {n} (v : finitary α n) (i) : v i ≤ Max d v :=
begin
  induction n with n IH; rcases i with ⟨i, i_p⟩,
  { exfalso, exact nat.not_lt_zero i i_p },
  simp[Max],
  have : i < n ∨ i = n, exact nat.lt_succ_iff_lt_or_eq.mp i_p,
  cases this,
  { right, have := IH (λ i, v ↑i) ⟨i, this⟩, simp at this, exact this },
  { left, simp[this] }
end

@[simp] def Max_0 [linear_order α] (d : α) (v : finitary α 0) : Max d v = d :=
by simp[Max]

protected def mem : ∀ {n}, α → finitary α n → Prop
| 0     a _ := false
| (n+1) a f := a = f ⟨n, lt_add_one n⟩ ∨ @mem n a (λ i, f ⟨i.val, nat.lt.step i.property⟩)

instance {n} : has_mem α (finitary α n) := ⟨finitary.mem⟩

@[simp] lemma index_mem {n} (f : finitary α n) (i) :  f i ∈ f :=
by { induction n with n IH; simp[has_mem.mem, finitary.mem],
     { exact i.val.not_lt_zero i.property },
     have := nat.lt_succ_iff_lt_or_eq.mp i.property, cases this,
     {right, have := IH (λ (i : fin n), f ⟨i.val, nat.lt.step i.property⟩) ⟨i, this⟩, simp at*, refine this },
     simp[←this] }

protected def subset {n₁ n₂} (f₁ : finitary α n₁) (f₂ : finitary α n₂) := ∀ ⦃a : α⦄, a ∈ f₁ → a ∈ f₂

def cons_inv {n} (f : finitary α n) (a : α) : finitary α (n + 1) := λ i, if h : ↑i < n then f ⟨i, h⟩ else a

@[simp] def cons {n} (a : α) (f : finitary α n) : finitary α n.succ
| ⟨0, h⟩ := a
| ⟨i + 1, h⟩ := f ⟨i, nat.succ_lt_succ_iff.mp h⟩

infixl ` ᶠ:: `:60  := finitary.cons_inv

infixr ` ::ᶠ `:60  := finitary.cons

@[simp] lemma cons_inv_app0 {n} (f : finitary α n) (a : α) : (f ᶠ:: a) ⟨n, lt_add_one n⟩ = a := by simp[finitary.cons_inv]

@[simp] lemma cons_inv_app1 {n} (f : finitary α n) (a : α) (i : fin n) : (f ᶠ:: a) i.add' = f i :=
by { simp[finitary.cons_inv, fin.add'] }

@[simp] lemma cons_app_0 {n} (f : finitary α n) (a : α) : (a ::ᶠ f) 0 = a := rfl

@[simp] lemma cons_app_succ {n} (f : finitary α n) (a : α) (i : fin n) {h} : (a ::ᶠ f) ⟨i + 1, h⟩ = f i :=
by simp

@[simp] lemma cons_app_eq_succ (a : α) {n} (f : finitary α n) (i : fin n) :
  (a ::ᶠ f) i.succ = f i := by simp[show i.succ = ⟨i + 1, nat.succ_lt_succ i.property⟩, from fin.ext (by simp)]

@[simp] lemma cons_app_eq_1 (a : α) {n} (f : finitary α (n + 1)) :
  (a ::ᶠ f) 1 = f 0 := cons_app_eq_succ a f 0

def nil : finitary α 0 := λ i, by { exfalso, exact i.val.not_lt_zero i.property }

instance : has_emptyc (finitary α 0) := ⟨nil⟩

notation `‹` l:(foldr `, ` (t h, finitary.cons t h) finitary.nil `›`) := l

def tail_inv {n} (f : finitary α (n + 1)) : finitary α n := λ i, f ⟨i, nat.lt.step i.property⟩

def head_inv {n} (f : finitary α (n + 1)) : α := f ⟨n, lt_add_one n⟩

def tail {n} (f : finitary α (n + 1)) : finitary α n := λ i, f i.succ


lemma tail_inv_cons_inv_head {n} (f : finitary α (n + 1)) : f.tail_inv ᶠ:: f.head_inv = f :=
funext (λ i, by { simp[cons_inv, tail_inv, head_inv],
  intros h,
  congr, apply fin.eq_of_veq, simp,
  have : ↑i ≤ n, from fin.is_le i,
  exact le_antisymm h this })

@[simp] lemma zero_eq (f : finitary α 0) : f = ∅ :=
funext (λ i, by { have := i.property, exfalso, exact i.val.not_lt_zero this })

@[simp] lemma zero_eq' (f : fin 0 → α) : f = (∅ : finitary α 0) := zero_eq f

/-
lemma fin_2_eq (f : finitary α 1) : fin[f 0] = f :=
funext (λ i, by { rcases i with ⟨i, i_p⟩, cases i; simp[cons_inv], exfalso, simp[←nat.add_one] at*, exact i_p })


lemma fin1_eq (f : finitary α 1) : fin[f 0] = f :=
funext (λ i, by { rcases i with ⟨i, i_p⟩, cases i; simp[cons_inv], exfalso, simp[←nat.add_one] at*, exact i_p })

lemma fin2_eq (f : finitary α 2) : fin[f 0, f 1] = f :=
funext (λ i, by { rcases i with ⟨i, i_p⟩, cases i; simp[cons_inv], cases i, { simp },
  exfalso, simp[←nat.add_one] at i_p, exact i_p })
-/

@[ext] lemma fin_0_ext (f g : finitary α 0) : f = g :=
funext (λ i, by { rcases i with ⟨i, h⟩, exfalso, exact nat.not_lt_zero i h })

@[ext] lemma fin_1_ext {f g : finitary α 1} (h : f 0 = g 0) : f = g :=
funext (λ i, by { rcases i with ⟨i, hi⟩, rcases nat.lt_one_iff.mp hi with rfl, simp[h] })

@[ext] lemma fin_2_ext {f g : finitary α 2} (h0 : f 0 = g 0) (h1 : f 1 = g 1) : f = g :=
funext (λ i, by { rcases i with ⟨i, hi⟩,
  cases i, { simp[h0] }, cases i, { simp[h1] },
  { exfalso, simp[←nat.add_one, add_assoc] at hi, contradiction  } })

@[simp] lemma fin_1_app_eq (a : α) (i : fin 1) : ‹a› i = a :=
by { rcases i with ⟨i, h⟩, rcases nat.lt_one_iff.mp h with rfl, simp }

@[simp] lemma cons_inv_app_eq_0 (a : α) {n} (f : finitary α n) :
  (a ::ᶠ f) 0 = a := rfl

@[simp] lemma app_cons (a : α) {n} (f : finitary α n) (F : α → β) :
  (λ i : fin (n + 1), F $ (a ::ᶠ f) i) = (F a ::ᶠ λ i, F (f i)) :=
by { funext i, rcases i with ⟨i, h⟩, cases i; simp }

@[simp] lemma cons_tail (a : α) {n} (f : finitary α n) :
  (a ::ᶠ f).tail = f :=
by simp[tail]

lemma app_0_cons_tail_refl {n} (f : finitary α (n + 1)) : (f 0) ::ᶠ f.tail = f :=
funext (λ ⟨i, h⟩, by { rcases i; simp, refl })

@[simp] lemma of_fn_nil (f : finitary α 0) :
  of_fn f = vector.nil :=
by { ext i, exfalso, exact i.val.not_lt_zero i.property }

@[simp] lemma of_fn_cons (a : α) {n} (f : finitary α n) :
  of_fn (a ::ᶠ f) = a ::ᵥ (of_fn f) :=
by { ext i, rcases i with ⟨i, i_lt⟩, cases i; simp }

@[simp] lemma nth_cons (a : α) {n} (v : vector α n) :
  (a ::ᵥ v).nth = a ::ᶠ v.nth :=
by { ext i, rcases i with ⟨i, i_lt⟩, cases i; simp }

@[simp] lemma of_fn_nth_refl {n} (v : vector α n) :
  of_fn v.nth = v := by ext i; simp

@[simp] lemma nth_of_fn_refl {n} (f : finitary α n) :
  (of_fn f).nth = f := by ext i; simp

lemma app_0_nth_eq_head {n} (v : vector α (n + 1)) :
  v.nth 0 = v.head := by simp

@[simp] lemma head_eq_head {n} (f : finitary α (n + 1)) :
  (of_fn f).head = f 0 := by simp

lemma pi_fin0_eq_empty (f : fin 0 → α) : f = (∅ : finitary α 0) :=
zero_eq f

instance [primcodable α] (n : ℕ) : primcodable (finitary α n) :=
primcodable.fin_arrow

instance [has_to_string α] (n) : has_to_string (finitary α n) :=
⟨λ f, by { exact "(" ++ list.to_string_aux tt (of_fn f).val ++ ")" }⟩

@[simp, reducible] def to_total [inhabited α] {n} (f : finitary α n) : ℕ → α :=
λ x, if h : x < n then f ⟨x, h⟩ else default

@[simp, reducible] def of_total {n} (f : ℕ → α) : finitary α n := λ i, f i

@[simp] def of_option : Π {n}, finitary (option α) n → option (finitary α n)
| 0       f := some finitary.nil
| (n + 1) f := (f 0).bind (λ a, (@of_option n f.tail).map (λ v, a ::ᶠ v))

@[simp] lemma of_option_some : ∀ {n} (v : finitary α n), of_option (λ i, some (v i)) = some v
| 0       v := by { simp, ext }
| (n + 1) v := by { simp[@of_option_some n, tail], refine app_0_cons_tail_refl _ }

lemma of_option_eq_some_iff : ∀ {n} {v : finitary (option α) n} {v'},
  of_option v = some v' ↔ ∀ i, v i = some (v' i)
| 0       v v' := by simp[show v' = nil, by ext]
| (n + 1) v v' := by { simp[@of_option_eq_some_iff _ v.tail], split,
    { rintros ⟨a, v0_eq, v', h, rfl⟩ ⟨i, i_lt⟩, rw ←app_0_cons_tail_refl v, 
      cases i; simp* },
    { intros h, refine ⟨v' 0, by simp[h], v'.tail, by simp[tail, h], by simp[app_0_cons_tail_refl]⟩ } }

lemma of_option_eq_none_iff : ∀ {n} (v : finitary (option α) n),
  of_option v = none ↔ ∃ i, v i = none
| 0       v := by simp
| (n + 1) v := by { 
    have IH := of_option_eq_none_iff v.tail,
    simp, intros,
    split,
    { intros h, 
      cases C₁ : (v 0) with a, { refine ⟨0, C₁⟩ },
      cases C₂ : v.tail.of_option with v', { rcases IH.mp C₂ with ⟨i, h⟩, refine ⟨i.succ, h⟩ },
      have := h (a ::ᶠ v') a C₁ v' C₂ rfl, contradiction },
    { rintros ⟨⟨i, i_lt⟩, eqn⟩ w a eqn_a w' eqn_w' rfl, 
      cases i,
      { simp[eqn_a] at eqn, contradiction },
      { have :v.tail ⟨i, _⟩ = some (w' ⟨i, _⟩), 
        from of_option_eq_some_iff.mp eqn_w' ⟨i, (by { simp[←nat.add_one] at i_lt, exact i_lt })⟩,
        simp[tail, eqn] at this, contradiction } } }

end finitary

namespace encodable
variables {α : Type u} [encodable α] [inhabited α] 

def idecode (α : Type u) [encodable α] [inhabited α] : ℕ → α := λ n, (decode α n).iget 

lemma idecode_surj : function.surjective (idecode α) := surjective_decode_iget _

@[simp] lemma idecode_encodek : ∀ (a : α), idecode α (encode a) = a :=
by simp[idecode, encodek]

end encodable


namespace quotient
variables {α : Type u}

protected def lift_on_finitary {s : setoid α} {φ} : ∀ {n : ℕ} (v : finitary (quotient s) n) (f : finitary α n → φ)
  (h : ∀ v₁ v₂ : finitary α n, (∀ n, setoid.r (v₁ n) (v₂ n)) → f v₁ = f v₂), φ
| 0       v f h := f finitary.nil
| (n + 1) v f h :=
    let f' : α → finitary α n → φ := λ t v, f (λ i, if h : ↑i < n then (v ⟨i, h⟩) else t) in
    have h_0 : ∀ (a₁ a₂ : α) (eq : setoid.r a₁ a₂), f' a₁ = f' a₂,
    { intros t₁ t₂ eq, funext v, simp[f'], refine h _ _ (λ i, _),
      have : ↑i < n ∨ ↑i = n, exact nat.lt_succ_iff_lt_or_eq.mp i.property, cases this; simp[this],
      { exact quotient.eq'.mp rfl }, refine eq },
    have h_v : ∀ (a : α) (v₁ v₂ : finitary α n) (eqs : ∀ (n : fin n), setoid.r (v₁ n) (v₂ n)), f' a v₁ = f' a v₂,
    { intros t v₁ v₂ hyp, refine h _ _ (λ i, _), 
      have : ↑i < n ∨ ↑i = n, exact nat.lt_succ_iff_lt_or_eq.mp i.property, cases this; simp[this],
      refine hyp _, exact quotient.eq'.mp rfl },
    let f'_p : α → φ := λ t, lift_on_finitary (λ i, v ⟨i, nat.lt.step i.property⟩) (f' t) (h_v t) in
    quotient.lift_on (v ⟨n, lt_add_one n⟩) f'_p (λ a₁ a₂ h, by { simp[f'_p], funext _, simp[h_0 a₁ a₂ h] })

@[simp]
protected lemma lift_on_finitary_eq {s : setoid α} {φ} {n} (v : finitary α n) (f : finitary α n → φ)
  (h : ∀ v₁ v₂ : finitary α n, (∀ n, setoid.r (v₁ n) (v₂ n)) → f v₁ = f v₂) :
  quotient.lift_on_finitary (λ x, ⟦v x⟧) f h = f v :=
by { induction n with n IH; simp[quotient.lift_on_finitary],
     { simp [finitary.zero_eq v, show (finitary.nil : finitary α 0) = ∅, by refl] },
     simp[IH], congr, funext i,
     have : ↑i < n ∨ ↑i = n, exact nat.lt_succ_iff_lt_or_eq.mp i.property, cases this; simp[this], simp[←this] }

@[simp]
protected lemma lift_on_finitary_0_eq {s : setoid α} {φ} (f : finitary α 0 → φ)
  (h : ∀ v₁ v₂ : finitary α 0, (∀ n, setoid.r (v₁ n) (v₂ n)) → f v₁ = f v₂) (n : finitary (quotient s) 0) :
  quotient.lift_on_finitary n f h = f finitary.nil :=
by simp[quotient.lift_on_finitary]

@[simp]
protected lemma lift_on_finitary_1_eq {s : setoid α} {φ} (a : α) (f : finitary α 1 → φ)
  (h : ∀ v₁ v₂ : finitary α 1, (∀ n, setoid.r (v₁ n) (v₂ n)) → f v₁ = f v₂) :
  quotient.lift_on_finitary ‹⟦a⟧› f h = f ‹a› :=
by { rw[show ‹⟦a⟧› = (λ x : fin 1, ⟦a⟧), by { refine finitary.fin_1_ext _; simp }],
     refine quotient.lift_on_finitary_eq ‹a› f h}

@[simp]
protected lemma lift_on_finitary_2_eq {s : setoid α} {φ} (a b : α) (f : finitary α 2 → φ)
  (h : ∀ v₁ v₂ : finitary α 2, (∀ n, setoid.r (v₁ n) (v₂ n)) → f v₁ = f v₂) :
  quotient.lift_on_finitary ‹⟦a⟧, ⟦b⟧› f h = f ‹a, b› :=
by { rw[show ‹⟦a⟧, ⟦b⟧› = (λ x : fin 2, ⟦‹a, b› x⟧), by { refine finitary.fin_2_ext _ _; simp }],
     refine quotient.lift_on_finitary_eq ‹a, b› f h }

end quotient

#check is_empty_sigma
-- @[simp] lemma is_empty_sigma {α} {s : α → Sort*} : is_empty (Σ a, s a) ↔ ∀ a, is_empty (s a) :=
-- by simp only [← not_nonempty_iff, nonempty_sigma, not_exists]

notation T` +{ ` :max p ` }` := insert p T

@[simp] lemma set.insert_mem {α : Sort*} (T : set α) (a : α) : a ∈ T +{ a } :=
by simp[insert]

@[simp] lemma set.insert_mem_of_mem {α : Sort*} {T : set α} {b : α} (h : b ∈ T) (a : α) :
  b ∈ T +{ a } := by simp[insert, h]

@[simp] lemma set.insert_mem_iff {α : Sort*} {T : set α} {a b : α} :
  b ∈ T +{ a } ↔ b = a ∨ b ∈ T := by simp[insert]

@[simp] def finitary.conjunction {α : Type*} [has_top α] [has_inf α] : ∀ n, (fin n → α) → α
| 0 _        := ⊤
| (n + 1) f  := f (fin.last n) ⊓ finitary.conjunction n (f ∘ fin.cast_succ)

notation `⋀` binders `, ` r:(scoped p, finitary.conjunction _ p) := r

@[simp] def finitary.disjunction {α : Type*} [has_bot α] [has_sup α] : ∀ n, (fin n → α) → α
| 0 _        := ⊥
| (n + 1) f  := finitary.disjunction n (f ∘ fin.cast_succ) ⊔ f (fin.last n)

notation `⋁` binders `, ` r:(scoped p, finitary.disjunction _ p) := r

@[simp] def list.conjunction {α : Type*} [has_top α] [has_inf α] : list α → α
| []        := ⊤
| (a :: as) := a ⊓ as.conjunction

@[simp] def list.disjunction {α : Type*} [has_bot α] [has_sup α] : list α → α
| []        := ⊥
| (a :: as) := as.disjunction ⊔ a

def fintype_sup {ι : Type*} [fintype ι] {α : Type*} [semilattice_sup α] [order_bot α] (f : ι → α) : α :=
  (finset.univ : finset ι).sup f

notation `⨆ᶠ ` binders `, ` r:(scoped f, fintype_sup f) := r

@[simp] lemma le_fintype_sup {ι : Type*} [fintype ι] {α : Type*} [semilattice_sup α] [order_bot α]
  (f : ι → α) (i : ι) :
  f i ≤ ⨆ᶠ i, f i := finset.le_sup (by simp)

@[simp] lemma le_fintype_sup' {ι : Type*} [fintype ι] {α : Type*} [semilattice_sup α] [order_bot α]
  {a : α} {f : ι → α} (i : ι) (le : a ≤ f i) :
  a ≤ ⨆ᶠ i, f i := le_trans le (le_fintype_sup _ _)

lemma fintype_sup_le {ι : Type*} [fintype ι] {α : Type*} [semilattice_sup α] [order_bot α]
  {f : ι → α} {a : α} (h : ∀ i, f i ≤ a) : (⨆ᶠ i, f i) ≤ a :=
finset.sup_le (λ i _, h i)

namespace fintype_sup
variables {ι : Type*} [fintype ι] {α : Type*} [semilattice_sup α] [order_bot α]

@[simp] lemma finsup_eq_0_of_empty [is_empty ι] (f : ι → α) :
  (⨆ᶠ i, f i) = (⊥ : α) := by simp[fintype_sup]

@[simp] lemma finsup_eq_of_subsingleton [subsingleton ι] [inhabited ι] (f : ι → α) :
  (⨆ᶠ i, f i) = f default :=
begin
  suffices : (⨆ᶠ i, f i) ≤ f default ∧ f default ≤ (⨆ᶠ i, f i), from le_antisymm_iff.mpr this,
  split,
  { refine fintype_sup_le (λ i, by simp[subsingleton.elim i default]) },
  { refine le_fintype_sup _ _ }
end

@[simp] lemma finsup_eq_of_fin2 {α : Type*} [linear_order α] [order_bot α] (f : fin 2 → α) :
  (⨆ᶠ i, f i) = max (f 0) (f 1) :=
begin
  suffices : (⨆ᶠ i, f i) ≤ max (f 0) (f 1) ∧ max (f 0) (f 1) ≤ (⨆ᶠ i, f i), from le_antisymm_iff.mpr this,
  split,
  { refine fintype_sup_le (λ ⟨i, hi⟩, by { rcases i; simp; rcases i; simp[← nat.add_one, add_assoc] at hi ⊢, contradiction }) },
  { simp }
end

end fintype_sup

class wf_lt (α : Type*) :=
(prelt : α → α → Prop)
(wt : α → ℕ)
(mono' : ∀ {a b}, prelt a b → wt a < wt b)

namespace wf_lt
variables {α : Type*} [wf_lt α]

inductive le : α → α → Prop
| refl     : ∀ a, le a a
| of_prelt : ∀ {a b}, prelt a b → le a b
| trans    : ∀ a b c, le a b → le b c → le a c

instance : preorder α :=
{ le := le,
  le_refl := le.refl,
  le_trans := le.trans }

lemma mono {a b : α} (h : a ≤ b) : wt a ≤ wt b :=
by { induction h,
  case refl { simp },
  case of_prelt : a b prelt { exact le_of_lt (mono' prelt) },
  case trans : a b c _ _ le_ab le_bc { exact le_trans le_ab le_bc } }

instance : partial_order α :=
  { le_antisymm := λ p q h, by { 
      induction h; try { simp },
      case of_prelt : a b prelt { intros le, exfalso, exact nat.lt_le_antisymm (mono' prelt) (mono le) },
      case trans : a b c le_ab le_bc IH_ab IH_bc
      { intros le, rcases IH_bc (le_trans le le_ab) with rfl, exact IH_ab le } },
    ..wf_lt.preorder }

lemma lt_of_prelt {a b : α} (h : wf_lt.prelt a b) : a < b :=
by { have le : a ≤ b, from le.of_prelt h,
     have ne : a ≠ b, { rintros rfl, exact nat.lt_asymm (mono' h) (mono' h) },
     refine lt_iff_le_and_ne.mpr ⟨le, ne⟩ }

lemma lt_iff {a b : α} : a < b ↔ ∃ b', prelt b' b ∧ a ≤ b' :=
⟨by { suffices : ∀ {a b : α} (le : a ≤ b) (ne : a ≠ b), (∃ b', prelt b' b ∧ a ≤ b'),
  { intros lt, exact this (le_of_lt lt) (ne_of_lt lt) },
  intros a b h, induction h,
  case refl { simp },
  case of_prelt : a b prelt { intros nle, refine ⟨a, prelt, by refl⟩ },
  case trans : a b c le_ab le_bc IH_ab IH_bc
  { intros ne,
    by_cases C : b = c, rcases C with (rfl | C),
    { exact IH_ab ne },
    { rcases IH_bc C with ⟨b', prelt, le⟩,
      refine ⟨b', prelt, le_trans (show a ≤ b, from le_ab) le⟩ } } },
 by { rintros ⟨b', prelt, le⟩, exact gt_of_gt_of_ge (lt_of_prelt prelt) le }⟩

lemma lt_mono {a b : α} (h : a < b) : wt a < wt b :=
by { rcases lt_iff.mp h with ⟨b', prelt, le⟩, exact gt_of_gt_of_ge (mono' prelt) (mono le) }

def wf : well_founded ((<) : α → α → Prop) :=
subrelation.wf (λ x y h, @lt_mono _ _ _ _ h) (inv_image.wf wt nat.lt_wf)

lemma lt_finite (h : ∀ a : α, set.finite {b | prelt b a}) (a : α) : set.finite {b | b < a} :=
begin
  refine @well_founded.induction _ _ wf (λ a, set.finite {b | b < a}) a _,
  simp, intros a IH,
  let P := {b | prelt b a},
  let B := P ∪ ⋃ b ∈ P, {c | c < b},
  have : B = {b : α | b < a},
  { ext b, simp[B], split,
    { rintros (prelt | ⟨c, prelt, lt⟩),
      { exact lt_of_prelt prelt },
      { have : c < a, from lt_of_prelt prelt, exact lt_trans lt this } },
    { intros lt, rcases lt_iff.mp lt with ⟨c, prelt, le⟩,
      have : b = c ∨ b < c, from eq_or_lt_of_le le,
      rcases this with (rfl | lt_bc),
      { exact or.inl prelt },
      { refine or.inr ⟨c, prelt, lt_bc⟩ } } },
  rw ←this,
  show B.finite,
  have : (⋃ b ∈ P, {c | c < b}).finite, from set.finite.bUnion (h _) (λ c prelt, IH c (lt_of_prelt prelt)),
  exact set.finite.union (show P.finite, from h _) this
end

lemma le_finite (h : ∀ a : α, set.finite {b | prelt b a}) (a : α) : set.finite {b | b ≤ a} :=
by { have : {b : α | b ≤ a} = insert a {b | b < a}, { ext b, simp, exact le_iff_eq_or_lt },
     simp[this], exact set.finite.insert a (lt_finite h a) }

end wf_lt

namespace list
variables {α : Type*} {ι : Type*} [fintype ι]

def Sup {n} (f : fin n → list α) : list α := (list.of_fn f).join

@[simp] lemma ss_Sup {n} (f : fin n → list α) (i : fin n) : f i ⊆ Sup f := λ x h,
by simp[Sup]; refine ⟨f i, _, h⟩; simp[list.mem_of_fn]

@[simp] lemma mem_Sup_iff {n} {f : fin n → list α} {a : α} :
  a ∈ Sup f ↔ ∃ i, a ∈ f i :=
⟨by { simp[Sup], intros i h, refine ⟨i, h⟩ },
 by { rintros ⟨i, h⟩, simp[Sup, list.mem_of_fn], refine ⟨i, h⟩ }⟩

section inf
variables [has_inf α] [has_top α]

@[simp] def inf : list α → α
| []        := ⊤
| (a :: as) := a ⊓ as.inf

end inf

end list

namespace set
variables {α : Type*} {β : Type*}

lemma image_finite_inversion_aux (s : set β) (h : s.finite) (f : α → β) : ∀ (z : set α), s ⊆ f '' z → ∃ u ⊆ z, u.finite ∧ f '' u = s :=
begin
  apply set.finite.induction_on h,
  { intros, refine ⟨∅, by simp⟩ },
  { rintros b s hb sfin IH z ss,
    have : (∃ a, a ∈ z ∧ f a = b) ∧ s ⊆ f '' z, by simpa[set.insert_subset] using ss,
    rcases this with ⟨⟨a, ha, rfl⟩, hs⟩,
    have : ∃ u ⊆ z, u.finite ∧ f '' u = s, from IH z hs,
    rcases this with ⟨u, hu, u_fin, rfl⟩,
    refine ⟨insert a u, by simp[set.insert_subset, ha, hu], finite.insert a u_fin, image_insert_eq⟩ }
end

lemma image_finite_inversion {f : α → β} {s : set α} (h : (f '' s).finite) : ∃ u ⊆ s, u.finite ∧ f '' u = f '' s :=
image_finite_inversion_aux (f '' s) h f s (by refl)

lemma subset_union_iff_exists {s t u : set α} : s ⊆ t ∪ u ↔ ∃ (t' ⊆ t) (u' ⊆ u), s = t' ∪ u' :=
⟨by { intros h,
  refine ⟨s ∩ t, by simp, s ∩ u, by simp, by symmetry; simp[←set.inter_union_distrib_left, h]⟩, 
   },
 by { rintros ⟨t', ht', u', hu', rfl⟩,
      simp[set.subset_union_of_subset_left ht', set.subset_union_of_subset_right hu'] }⟩

end set

section classical
attribute [instance, priority 0] classical.prop_decidable

end classical
