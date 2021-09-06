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
#check vector.elim

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

def finitary (α β : Type u) : ℕ → Type u
| 0     := β
| (n+1) := α → finitary n

section classical
attribute [instance, priority 0] classical.prop_decidable

end classical

