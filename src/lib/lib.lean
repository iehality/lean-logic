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
  order.zorn

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
| 0       v v' := by { simp[show v' = nil, by ext],
    intros i, have := i.property, exfalso, exact i.val.not_lt_zero this }
| (n + 1) v v' := by { simp[@of_option_eq_some_iff _ v.tail], split,
    { rintros ⟨a, v0_eq, v', h, rfl⟩ ⟨i, i_lt⟩, rw ←app_0_cons_tail_refl v, 
      cases i; simp* },
    { intros h, refine ⟨v' 0, by simp[h], v'.tail, by simp[tail, h], by simp[app_0_cons_tail_refl]⟩ } }

lemma of_option_eq_none_iff : ∀ {n} (v : finitary (option α) n),
  of_option v = none ↔ ∃ i, v i = none
| 0       v := by { simp, intros x, have := x.property, exfalso, exact x.val.not_lt_zero this }
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

@[simp] lemma is_empty_sigma {α} {s : α → Sort*} : is_empty (Σ a, s a) ↔ ∀ a, is_empty (s a) :=
by simp only [← not_nonempty_iff, nonempty_sigma, not_exists]

@[notation_class] class has_succ (α : Sort*) := (succ : α → α)

prefix `Succ `:85 := has_succ.succ

def numeral {α : Type*} [has_zero α] [has_succ α] : ℕ → α
| 0       := 0
| (n + 1) := Succ (numeral n)

instance numeral_has_one {α : Type*} [has_zero α] [has_succ α] : has_one α := ⟨Succ 0⟩

lemma numeral_one_def  {α : Type*} [has_zero α] [has_succ α] : (1 : α) = Succ 0 := rfl 

@[notation_class] class has_eq (α : out_param (Sort*)) (β : Sort*) := (eq : α → α → β)

infix ` ≃ `:50 := has_eq.eq

@[notation_class] class has_preceq (α : out_param (Sort*)) (β : Sort*) := (preceq : α → α → β)

infix ` ≼ `:50 := has_preceq.preceq

@[notation_class] class has_elem (α : out_param (Sort*)) (β : Sort*) := (elem : α → α → β)

infix ` ∊ `:50 := has_elem.elem

@[notation_class] class has_negation (α : Sort*) := (neg : α → α)

prefix `⁻`:75 := has_negation.neg

@[reducible] def has_eq.ineq {α : out_param (Sort*)} {β : Sort*} [has_eq α β] [has_negation β] (a b : α) : β := ⁻(a ≃ b)

infix ` ≄ `:50 := has_eq.ineq

@[notation_class] class has_arrow (α : Sort*) := (arrow : α → α → α)

infixr ` ⟶ `:60 := has_arrow.arrow

@[notation_class] class has_lrarrow (α : Sort*) := (lrarrow : α → α → α)

@[notation_class] class has_univ_quantifier (α : Sort*) := (univ : α → α)

prefix `∏ `:64 := has_univ_quantifier.univ

@[notation_class] class has_exists_quantifier (α : Sort*) := (ex : α → α)

prefix `∐ `:64 := has_exists_quantifier.ex

@[notation_class] class has_univ_quantifier' (α : Sort*) (β : Sort*):= (univ : α → β)

prefix `∏' `:64 := has_univ_quantifier'.univ

@[notation_class] class has_exists_quantifier' (α : Sort*) (β : Sort*) := (ex : α → β)

prefix `∐' `:64 := has_exists_quantifier'.ex

@[notation_class] class has_turnstile (α : Sort*) := (turnstile : set α → α → Prop)

infix ` ⊢ `:45 := has_turnstile.turnstile
notation T ` ⊢{`:45 β `} `:45 p := has_turnstile.turnstile T β p

namespace has_turnstile
variables {α : Type*} [has_turnstile α]

def turnstile_set (T : set α) (Γ : set α) : Prop := ∀ p ∈ Γ, T ⊢ p

infix ` ⊢* `:45 := turnstile_set

end has_turnstile

@[notation_class] class has_Longarrow (α : Sort*) := (Longarrow : set α → α → Type u)

infix ` ⟹ `:45 := has_Longarrow.Longarrow

def has_arrow.lrarrow {α : Type*} [has_arrow α] [has_inf α] (a b : α) : α := (a ⟶ b) ⊓ (b ⟶ a)

infix ` ⟷ `:59 := has_arrow.lrarrow

lemma lrarrow_def {α : Type*} [has_arrow α] [has_inf α] (a b : α) : a ⟷ b = (a ⟶ b) ⊓ (b ⟶ a) := rfl

notation T` +{ ` :max p ` }` := set.insert p T

@[reducible] def set.insert' {α} (T : set α) (a : α) := set.insert a T

infixl `❟ ` :46 := set.insert'

@[simp] lemma set.insert_mem {α : Sort*} (T : set α) (a : α) : a ∈ T +{ a } :=
by simp[set.insert]

@[simp] lemma set.insert_mem_of_mem {α : Sort*} {T : set α} {b : α} (h : b ∈ T) (a : α) :
  b ∈ T +{ a } := by simp[set.insert, h]

@[simp] lemma set.insert_mem_iff {α : Sort*} {T : set α} {a b : α} :
  b ∈ T +{ a } ↔ b = a ∨ b ∈ T := by simp[set.insert]

@[notation_class] class has_double_turnstile (α : Sort*) (β : Sort*) := (double_turnstile : α → β → Prop)

infix ` ⊧ ` :55 := has_double_turnstile.double_turnstile

namespace has_double_turnstile
variables {α : Type*} {β : Type*} [has_double_turnstile α β]

def double_turnstile_set (T : α) (S : set β) : Prop := ∀ p ∈ S, T ⊧ p

infix ` ⊧* `:45 := double_turnstile_set

end has_double_turnstile

@[simp] def inf_conjunction {α : Type*} [has_top α] [has_inf α] : ∀ n, (fin n → α) → α
| 0 _        := ⊤
| (n + 1) f  := (f ⟨n, lt_add_one n⟩) ⊓ inf_conjunction n (λ i, f ⟨i.val, nat.lt.step i.property⟩)

notation `⋀` binders `, ` r:(scoped p, inf_conjunction _ p) := r

@[simp] def sup_disjunction {α : Type*} [has_bot α] [has_sup α] : ∀ n, (fin n → α) → α
| 0 _        := ⊥
| (n + 1) f  := (f ⟨n, lt_add_one n⟩) ⊔ sup_disjunction n (λ i, f ⟨i.val, nat.lt.step i.property⟩)

notation `⋁` binders `, ` r:(scoped p, sup_disjunction _ p) := r

instance : has_arrow Prop := ⟨(→)⟩

instance : has_negation Prop := ⟨not⟩

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
  (⨆ᶠ i, f i) = ⊥ := by simp[fintype_sup]

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

end list

namespace tukey
variables {α : Type*} {F : set α → Prop}

def finite_charactor (P : set α → Prop) : Prop := ∀ a, P a ↔ (∀ s ⊆ a, s.finite → P s)

lemma of_ss (H : finite_charactor F) {a} (ha : F a) {b} (ss : b ⊆ a) : F b :=
begin
  have : ∀ s ⊆ a, s.finite → F s, from (H a).mp ha,
  have : ∀ s ⊆ b, s.finite → F s,
  { intros s hs s_fin, exact this s (set.subset.trans hs ss) s_fin },
  exact (H b).mpr this
end

lemma empty_of_nonempty (H : finite_charactor F) {a} (ha : F a) : F ∅ :=
of_ss H ha (by simp)

lemma finite_chain_sup (H : finite_charactor F) {c : set (set α)} (ch : is_chain has_subset.subset c) :
  ∀ {d : set (set α)} (hs : d.finite) (nemp : d.nonempty) (ss : d ⊆ c), ∃ m ∈ d, ⋃₀d ⊆ m :=
begin
  intros d d_fin,
  refine set.finite.induction_on d_fin (by simp) _,
  intros a s ha s_fin IH _ ss,
  by_cases nemp : s.nonempty,
  { have : ∃ (m ∈ s), ⋃₀ s ⊆ m, from IH nemp (set.subset.trans (by simp) ss),
    rcases this with ⟨m, mem, hs⟩,
    have : m ⊆ a ∨ a ⊆ m, from is_chain.total ch (show m ∈ c, from ss (by simp[mem])) (show a ∈ c, from ss (by simp)),
    rcases this,
    { refine ⟨a, by simp, _⟩,
      simp at hs ⊢, refine ⟨by refl, λ t ht, set.subset.trans (hs t ht) this⟩ },
    { refine ⟨m, by simp[mem], _⟩,
      simp at hs ⊢, refine ⟨this, hs⟩ } },
  { have : s = ∅, from set.not_nonempty_iff_eq_empty.mp nemp, rcases this with rfl,
    refine ⟨a, by simp⟩ }
end

theorem exists_maximum (H : finite_charactor F) (a : set α) (ha : F a) :
  ∃ m, F m ∧ a ⊆ m ∧ ∀ s, F s → m ⊆ s → s = m :=
begin
  suffices : ∃ (m : set α) (H : m ∈ {x : set α | F x}),
  a ⊆ m ∧ ∀ (a : set α), a ∈ {x : set α | F x} → m ⊆ a → a = m,
  { simp at this, exact this },
  refine zorn_subset_nonempty {x | F x} _ a ha, simp,
  rintros c hF hc nemp,
  have : F (⋃₀ c),
  { have : ∀ s ⊆ ⋃₀ c, s.finite → F s,
    { rw[set.sUnion_eq_Union], intros s s_ss s_fin,
      have : ∃ (d : set (set α)), d ⊆ c ∧ d.finite ∧ s ⊆ ⋃₀ d,
      { rcases set.finite_subset_Union s_fin s_ss with ⟨I, I_fin, s_ss⟩,  simp at s_ss,
        refine ⟨coe '' I, by simp, set.finite.image coe I_fin, by simpa using s_ss⟩ },
      rcases this with ⟨d, d_ss, d_fin, hs⟩,
      by_cases d_nemp : d.nonempty,
      { have : ∃ m ∈ d, ⋃₀d ⊆ m, from finite_chain_sup H hc d_fin d_nemp d_ss,
        rcases this with ⟨m, m_mem, ss_m⟩,
        exact of_ss H (show F m, from hF (d_ss m_mem)) (show s ⊆ m, from set.subset.trans hs ss_m) },
      { have : d = ∅, from set.not_nonempty_iff_eq_empty.mp d_nemp, rcases this with rfl,
        simp at hs, have : s = ∅, exact set.subset_eq_empty hs rfl, rcases this with rfl,
        rcases set.nonempty_def.mp nemp with ⟨x, hx⟩, refine empty_of_nonempty H (hF hx) } },
    refine (H (⋃₀ c)).mpr this },
  refine ⟨⋃₀ c, this, λ _, set.subset_sUnion_of_mem⟩
end 

end tukey

section classical
attribute [instance, priority 0] classical.prop_decidable

end classical
