import
  tactic data.equiv.encodable.basic
  computability.primrec
  computability.partrec
  computability.partrec_code
  computability.halting
  data.pfun
  init.data.list init.data.subtype init.meta.interactive init.data.fin

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

end vector

def finitary (α : Type*) (n : ℕ) := fin n → α

namespace finitary
variables {α : Type*}
open vector

lemma zero_eq (f₁ f₂ : finitary α 0) : f₁ = f₂ :=
funext (λ i, by { have := i.property, exfalso, exact i.val.not_lt_zero this })

def of_vec_of_fn : Π {n}, (fin n → α) → vector α n
| 0 f := nil
| (n+1) f := cons (f 0) (of_fn (λi, f i.succ))

def Max [linear_order α] (d : α) : ∀ {n}, finitary α n → α
| 0     _ := d
| (n+1) f := max (f ⟨n, lt_add_one n⟩) (@Max n (λ i, f ⟨i, nat.lt.step i.property⟩))

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

def cons {n} (f : finitary α n) (a : α) : finitary α (n + 1) := λ i, if h : ↑i < n then f ⟨i, h⟩ else a

infixr ` ::ᶠ `:60  := finitary.cons

@[simp] lemma cons_app0 {n} (f : finitary α n) (a : α) : (f ::ᶠ a) ⟨n, lt_add_one n⟩ = a := by simp[finitary.cons]

@[simp] lemma cons_app1 {n} (f : finitary α n) (a : α) (i : fin n) : (f ::ᶠ a) ⟨i, nat.lt.step i.property⟩ = f i :=
by { simp[finitary.cons], intros h, exfalso, exact nat.lt_le_antisymm i.property h }

def nil : finitary α 0 := λ i, by { exfalso, exact i.val.not_lt_zero i.property }
notation `fin[` l:(foldr `, ` (h t, finitary.cons t h) nil `]`) := l

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
by { induction n with n IH; simp[quotient.lift_on_finitary], { simp [finitary.zero_eq finitary.nil v] },
     simp[IH], congr, funext i,
     have : ↑i < n ∨ ↑i = n, exact nat.lt_succ_iff_lt_or_eq.mp i.property, cases this; simp[this], simp[←this] }


end quotient

section classical
attribute [instance, priority 0] classical.prop_decidable

end classical

