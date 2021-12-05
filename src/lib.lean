import
  tactic data.equiv.encodable.basic
  computability.primrec
  computability.partrec
  computability.partrec_code
  computability.halting
  data.pfun
  order
  init.data.list
  init.data.subtype

universes u v

attribute [instance, priority 0] classical.prop_decidable

namespace nat

@[simp] lemma max_zero_left {n m} : max n m = 0 ↔ n = 0 ∧ m = 0 :=
⟨λ h, ⟨nat.le_zero_iff.mp (le_of_max_le_left (eq.symm h).ge),
       nat.le_zero_iff.mp (le_of_max_le_right (eq.symm h).ge)⟩,
 λ ⟨e₁, e₂⟩, by simp[e₁, e₂]⟩

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

end nat

namespace function
variables {α : Type*}

def fun_pow (f : α → α) : ℕ → α → α
| 0     a := a
| (n+1) a := f (fun_pow n a)
infix ` ^ᶠ `:60 := fun_pow

end function

inductive dvector (α : Type u) : ℕ → Type u
| nil {} : dvector 0
| cons   : ∀ {n}, α → dvector n → dvector (n+1)

infixr ` ::ᵈ `:60  := dvector.cons

namespace dvector
variables {α : Type u} {β : Type v}

@[simp] def unary (a : α) : dvector α 1 := a ::ᵈ nil

@[simp] def head : ∀ {n}, dvector α (n+1) → α
| _ (a ::ᵈ _) := a

@[simp] def tail : ∀ {n}, dvector α (n+1) → dvector α n
| _ (_ ::ᵈ as) := as

lemma dvector1_tail : ∀ (a : dvector α 1), a.tail = dvector.nil
| (a ::ᵈ dvector.nil) := rfl

@[simp] lemma dvector0 : ∀ (a : dvector α 0), a = dvector.nil := λ a,
by cases a; refl

lemma head_tail : ∀ {n} (v : dvector α (n+1)), v.head ::ᵈ v.tail = v
| _ (_ ::ᵈ _) := rfl

@[simp] lemma head_inj : ∀ (v₁ v₂ : dvector α 1), v₁.head = v₂.head ↔ v₁ = v₂
| (_ ::ᵈ nil) (_ ::ᵈ nil) := by simp

@[simp] lemma head_nil : ∀ (v : dvector α 1), v.head ::ᵈ nil = v
| (_ ::ᵈ nil) := rfl

@[simp] protected def append : ∀ {n}, dvector α n → ∀ {m}, dvector α m → dvector α (m + n)
| _ nil      _ l := l
| _ (a ::ᵈ l) _ k := a ::ᵈ (append l k)

@[simp] def filter (f : α → β) : ∀ {n}, dvector α n → dvector β n
| 0     _         := dvector.nil
| (n+1) (a ::ᵈ as) := f a ::ᵈ filter as

@[simp] def app {C : Π i : α, Type v} (a) : ∀ {n}, dvector (Π i, C i) n → dvector (C a) n
| 0     _         := dvector.nil
| (n+1) (f ::ᵈ fs) := f a ::ᵈ app fs

@[simp] def partition {C : Π i : α, Type*} : ∀ {n}, (Π i, dvector (C i) n) → dvector (Π i, C i) n
| 0     _ := dvector.nil
| (n+1) F := (λ i, (F i).head) ::ᵈ (partition $ λ i, (F i).tail)

@[simp] lemma app_partition {C : Π i : α, Type v} (a) : ∀ {n} (F : Π i, dvector (C i) n),
  (partition F).app a = F a
| 0     F := by { simp, cases F a, refl }
| (n+1) F := by { simp, cases C : F a with _ f fs, simp[C, app_partition (λ i, (F i).tail)] }

@[simp] def to_vector : Π {n}, dvector α n → vector α n
| _ nil := vector.nil
| _ (a ::ᵈ as) := a ::ᵥ as.to_vector

end dvector

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

@[simp] lemma succ_nth_1 (v : vector α (n + 1)) (a : α)  :
  (a ::ᵥ v).nth 1 = v.nth 0 := succ_nth' v a 0

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

end finitary

namespace encodable
variables {α : Type u} [encodable α] [inhabited α] 

def idecode (α : Type u) [encodable α] [inhabited α] : ℕ → α := λ n, (decode α n).iget 

lemma idecode_surj : function.surjective (idecode α) := surjective_decode_iget _

@[simp] lemma idecode_encodek : ∀ (a : α), idecode α (encode a) = a :=
by simp[idecode, encodek]

end encodable

namespace setoid

@[simp] def vec_r {α : Type u} [s : setoid α] : ∀ {n}, dvector α n → dvector α n → Prop
| 0     _         _         := true
| (n+1) (a ::ᵈ as) (b ::ᵈ bs) := a ≈ b ∧ vec_r as bs

infix ` ≋ `:80 := vec_r

@[simp] lemma vec_r_refl {α : Type u} [s : setoid α] {n} (v : dvector α n) : vec_r v v := by induction v; simp*

lemma vec_r_symm {α : Type u} [s : setoid α] : ∀ {n} {v w : dvector α n}, vec_r v w → vec_r w v
| 0 _ _ := by simp
| (n+1) (a ::ᵈ as) (b ::ᵈ bs) := by { simp, refine λ e h, ⟨setoid.symm e, vec_r_symm h⟩ }

lemma vec_r_trans {α : Type u} [s : setoid α] : ∀ {n} {a b c : dvector α n}, vec_r a b → vec_r b c → vec_r a c
| 0 _ _ _ := by simp
| (n+1) (a ::ᵈ as) (b ::ᵈ bs) (c ::ᵈ cs) := by { simp, refine λ e₁ h₁ e₂ h₂, ⟨setoid.trans e₁ e₂, vec_r_trans h₁ h₂⟩ }

lemma vec_r_equiv {α : Type u} [s : setoid α] {n} : equivalence (@vec_r α s n) := ⟨vec_r_refl, λ _ _, vec_r_symm, λ _ _ _, vec_r_trans⟩

instance vec {α : Type u} (s : setoid α) (n) : setoid (dvector α n) := ⟨@vec_r α s n, vec_r_equiv⟩

@[simp] lemma vec_r_simp_nil {α : Type*} [s : setoid α] :
  (dvector.nil : dvector α 0) ≋ dvector.nil := by simp[has_equiv.equiv]

@[simp] lemma vec_r_simp_cons {α : Type*} [s : setoid α] {n} {a b : α} {as bs : dvector α n} :
  (a ::ᵈ as) ≋ (b ::ᵈ bs) ↔ a ≈ b ∧ as ≋ bs := by { simp, }

@[simp] lemma vec_r_equiv_equiv {α : Type*} [s : setoid α] {n} {a b : dvector α n} :
  @setoid.r _ (s.vec n) a b ↔ a ≋ b := iff.rfl

end setoid

namespace quotient
universes u_a u_b u_c
variables {α : Type u_a} {β : Sort u_b} {φ : Sort u_c}

def cons_aux (s : setoid α) (a : α) {n} : quotient (s.vec n) → quotient (s.vec (n+1)) :=
λ q, @quotient.lift_on _ _ (s.vec n) q (λ v, @quotient.mk _ (s.vec (n+1)) (a ::ᵈ v)) $
λ as bs, by { simp, refine λ h, ⟨by refl, h⟩ }

def cons (s : setoid α) {n} : quotient s → quotient (s.vec n) → quotient (s.vec (n+1)) :=
λ q v, @quotient.lift_on _ _ s q (λ a, cons_aux s a v) $ λ as bs eqn, by { simp[cons_aux],
  induction v, simp[eqn, has_equiv.equiv], refine eqn, refl }

@[simp] def dvec_to_quo (s : setoid α) : ∀ {n}, dvector (quotient s) n → quotient (s.vec n)
| 0     _         := @quotient.mk _ (s.vec 0) (dvector.nil : dvector α 0)
| (n+1) (q ::ᵈ qs) := cons s q (dvec_to_quo qs)

protected def mk_v' (n) {s : setoid α} (a : dvector α n) : quotient (s.vec n) := quot.mk (s.vec n).1 a

private lemma quo_to_vec_eq (s : setoid α) : ∀ {n} (a b : dvector α n), a ≋ b → 
  dvector.filter quotient.mk a = dvector.filter quotient.mk b
| 0 dvector.nil dvector.nil _ := rfl
| (n+1) (a ::ᵈ as) (b ::ᵈ bs) eqn := by { simp at*, refine ⟨eqn.1, quo_to_vec_eq _ _ eqn.2⟩ }

@[simp] def quo_to_dvec (s : setoid α) : ∀ {n}, quotient (s.vec n) → dvector (quotient s) n :=
λ n q, @quotient.lift_on _ _ (s.vec n) q (λ v, v.filter (λ x, ⟦x⟧)) $
λ a b eqn, by { simp, refine quo_to_vec_eq s _ _ eqn }

def mk_vec' {n} {s : setoid α} (a : dvector α n) : dvector (quotient s) n := quo_to_dvec s (quot.mk (s.vec n).1 a)
notation `ᵥ⟦`u`⟧` := mk_vec' u

@[elab_as_eliminator, reducible]
def lift_on_vec {s : setoid α} {n} (q : dvector (quotient s) n) (f : dvector α n → φ)
  (c : ∀ a b : dvector α n, a ≋ b → f a = f b) : φ :=
@quotient.lift_on _ _ (s.vec _) (dvec_to_quo s q) f c

variables {s : setoid α} 

@[simp]
protected lemma lift_on_vecnil_eq (f : dvector α 0 → φ)
  (h : ∀ a b : dvector α 0, a ≋ b → f a = f b) :
  quotient.lift_on_vec (dvector.nil : dvector (quotient s) 0) f h = f dvector.nil := rfl

@[simp]
protected lemma lift_on_eq {s : setoid α}  {φ} (u₀ : α) (f : α → φ)
  (h : ∀ v u, v ≈ u → f v = f u) : quotient.lift_on ⟦u₀⟧ f h = f u₀ := rfl

@[simp] lemma cons_eq {s : setoid α} {n} (u : α) (us : dvector α n) :
  cons s ⟦u⟧ (@quotient.mk _ (s.vec n) us) = @quotient.mk _ (s.vec (n+1)) (u ::ᵈ us) := rfl

@[simp] lemma dvec_to_quo_filter_quotient_mk {s : setoid α} : ∀ {n} (u : dvector α n),
  dvec_to_quo s (dvector.filter quotient.mk u) = @quotient.mk _ (s.vec n) u
| 0     dvector.nil := rfl
| (n+1) (a ::ᵈ as)   := by simp [dvec_to_quo_filter_quotient_mk as]

@[simp]
protected lemma lift_on_vec_eq {s : setoid α} : ∀ {n} (u : dvector α n) (f : dvector α n → φ)
  (h : ∀ a b : dvector α n, a ≋ b → f a = f b),
quotient.lift_on_vec ᵥ⟦u⟧ f h = f u := by simp[mk_vec', lift_on_vec]

@[simp]
protected lemma lift_on_nil_eq {s : setoid α} : ∀ (f : dvector α 0 → φ)
  (h : ∀ a b : dvector α 0, a ≋ b → f a = f b),
quotient.lift_on_vec dvector.nil f h = f dvector.nil := by simp

lemma vquotient_cons {s : setoid α} {n} (a : α) (as : dvector α n) : ᵥ⟦a ::ᵈ as⟧ = ⟦a⟧ ::ᵈ ᵥ⟦as⟧ := rfl

@[simp] lemma quotients_eq_iff (s : setoid α) : ∀ {n} (v₁ v₂ : dvector α n), ᵥ⟦v₁⟧ = @mk_vec' _ _ s v₂  ↔ v₁ ≋ v₂
| 0 dvector.nil dvector.nil := by simp
| (n+1) (a ::ᵈ as) (b ::ᵈ bs) := by simp[vquotient_cons, quotients_eq_iff as bs]

end quotient

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

@[notation_class] class has_succ (α : Sort*) := (succ : α → α)

prefix `Succ `:85 := has_succ.succ

@[notation_class] class has_eq (α : Sort*) (β : Sort*) := (eq : α → α → β)

infix ` ≃ `:50 := has_eq.eq

@[notation_class] class has_preceq (α : Sort*) (β : Sort*) := (preceq : α → α → β)

infix ` ⩽ `:50 := has_preceq.preceq

@[notation_class] class has_elem (α : Sort*) (β : Sort*) := (elem : α → α → β)

infix ` ∊ `:50 := has_elem.elem

@[notation_class] class has_negation (α : Sort*) := (neg : α → α)

prefix `⁻`:75 := has_negation.neg

@[reducible] def has_eq.ineq {α : Sort*} {β : Sort*} [has_eq α β] [has_negation β] (a b : α) : β := ⁻(a ≃ b)

infix ` ≄ `:50 := has_eq.ineq

@[notation_class] class has_arrow (α : Sort*) := (arrow : α → α → α)

infixr ` ⟶ `:60 := has_arrow.arrow

@[notation_class] class has_lrarrow (α : Sort*) := (lrarrow : α → α → α)

@[notation_class] class has_univ_quantifier (α : Sort*) (β : Sort*):= (univ : α → β)

prefix `∏ `:64 := has_univ_quantifier.univ

@[notation_class] class has_exists_quantifier (α : Sort*) (β : Sort*) := (ex : α → β)

prefix `∐ `:64 := has_exists_quantifier.ex

@[notation_class] class has_turnstile (α : Sort*) := (turnstile : set α → α → Prop)

infix ` ⊢ `:45 := has_turnstile.turnstile

def has_arrow.lrarrow {α : Type*} [has_arrow α] [has_inf α] (a b : α) : α := (a ⟶ b) ⊓ (b ⟶ a)

infix ` ⟷ `:59 := has_arrow.lrarrow

lemma lrarrow_def {α : Type*} [has_arrow α] [has_inf α] (a b : α) : a ⟷ b = (a ⟶ b) ⊓ (b ⟶ a) := rfl

notation T` +{ ` :max p ` }` := set.insert p T

@[simp] lemma set.insert_mem {α : Sort*} (T : set α) (a : α) : a ∈ T +{ a } :=
by simp[set.insert]

@[simp] lemma set.insert_mem_of_mem {α : Sort*} {T : set α} {b : α} (h : b ∈ T) (a : α) :
  b ∈ T +{ a } := by simp[set.insert, h]

@[simp] lemma set.insert_mem_iff {α : Sort*} {T : set α} {a b : α} :
  b ∈ T +{ a } ↔ b = a ∨ b ∈ T := by simp[set.insert]

class intuitionistic_logic
  {F : Sort*} [has_negation F] [has_arrow F] [has_inf F] [has_sup F] [has_top F] [has_bot F] (P : F → Prop) :=
(modus_ponens {p q : F} : P (p ⟶ q) → P p → P q)
(imply₁ {p q : F} : P (p ⟶ q ⟶ p))
(imply₂ {p q r : F} : P ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r))
(conj₁ {p q : F} : P (p ⊓ q ⟶ p))
(conj₂ {p q : F} : P (p ⊓ q ⟶ q))
(conj₃ {p q : F} : P (p ⟶ q ⟶ p ⊓ q))
(disj₁ {p q : F} : P (p ⟶ p ⊔ q))
(disj₂ {p q : F} : P (q ⟶ p ⊔ q))
(disj₃ {p q r : F} : P ((p ⟶ r) ⟶ (q ⟶ r) ⟶ p ⊔ q ⟶ r))
(neg₁ {p q : F} : P ((p ⟶ q) ⟶ (p ⟶ ⁻q) ⟶ ⁻p))
(neg₂ {p q : F} : P (p ⟶ ⁻p ⟶ q))
(provable_top : P ⊤)
(bot_eq : (⊥ : F) = ⁻⊤)

class classical_logic
  {F : Sort*} [has_negation F] [has_arrow F] [has_inf F] [has_sup F] [has_top F] [has_bot F] (P : set F) :=
(modus_ponens {p q : F} : p ⟶ q ∈ P → p ∈ P → q ∈ P)
(imply₁ {p q : F} : p ⟶ q ⟶ p ∈ P)
(imply₂ {p q r : F} : (p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r ∈ P)
(contraposition {p q : F} : (⁻p ⟶ ⁻q) ⟶ q ⟶ p ∈ P)
(provable_top : ⊤ ∈ P)
(bot_eq : (⊥ : F) = ⁻⊤)
(and_def {p q : F} : p ⊓ q = ⁻(p ⟶ ⁻q))
(or_def {p q : F} : p ⊔ q = ⁻p ⟶ q)

attribute [simp] classical_logic.imply₁ classical_logic.imply₂ classical_logic.contraposition
  classical_logic.provable_top

class axiomatic_classical_logic'
  (F : Sort*) [has_negation F] [has_arrow F] [has_inf F] [has_sup F] [has_top F] [has_bot F] extends has_turnstile F :=
(classical {T : set F} : classical_logic ((⊢) T))
(by_axiom {T : set F} {p : F} : p ∈ T → T ⊢ p)

class axiomatic_classical_logic
  (F : Sort*) [has_negation F] [has_arrow F] [has_inf F] [has_sup F] [has_top F] [has_bot F] extends axiomatic_classical_logic' F :=
(deduction' {T : set F} {p q : F} : T +{ p } ⊢ q → T ⊢ p ⟶ q)
(weakening {T : set F} {U : set F} {p : F} : T ⊆ U → T ⊢ p → U ⊢ p)

@[notation_class] class has_double_turnstile (α : Sort*) (β : Sort*) (γ : Sort*) := (double_turnstile : α → β → γ)

infix ` ⊧ ` :55 := has_double_turnstile.double_turnstile

instance : has_arrow Prop := ⟨(→)⟩

instance : has_negation Prop := ⟨not⟩

section classical
attribute [instance, priority 0] classical.prop_decidable

end classical
