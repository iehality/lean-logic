import deduction model data.equiv.encodable.basic order.filter.ultrafilter
open encodable

universes u v

namespace fopl
variables {L : language.{u}} {I : Type v} [inhabited I] (F : ultrafilter I) {𝔄 : I → model L}

def uequiv : (Π i, |𝔄 i|) → (Π i, |𝔄 i|) → Prop :=
λ u₁ u₂, {i | u₁ i = u₂ i} ∈ F

notation u` ~[`:80 F`] `v:80 := uequiv F u v

@[simp] lemma uequiv_refl (u : Π i, |𝔄 i|) : u ~[F] u :=
by { simp[uequiv], exact F.univ_sets }

lemma uequiv_symm {u₁ u₂ : Π i, |𝔄 i|} : u₁ ~[F] u₂ → u₂ ~[F] u₁ :=
by { simp[uequiv], have : {i | u₁ i = u₂ i} = {i | u₂ i = u₁ i}, { ext, simp, exact eq_comm }, simp[this] }

lemma uequiv_trans {u₁ u₂ u₃ : Π i, |𝔄 i|} : u₁ ~[F] u₂ → u₂ ~[F] u₃ → u₁ ~[F] u₃ :=
by { simp[uequiv], intros h₁ h₂,
     have : {i | u₁ i = u₂ i} ∩ {i | u₂ i = u₃ i} ⊆ {i | u₁ i = u₃ i},
     { intros i hi, simp* at* },
     exact filter.mem_sets_of_superset (filter.inter_mem_sets h₁ h₂) this }

theorem uequiv_equivalence : equivalence (@uequiv L I _ F 𝔄) :=
⟨uequiv_refl F, λ _ _ , uequiv_symm F, λ _ _ _, uequiv_trans F⟩


@[reducible, simp, instance]
def ult (𝔄 : I → model L) (F : ultrafilter I) : setoid (Π i, |𝔄 i|) := ⟨@uequiv L I _ F 𝔄, uequiv_equivalence F⟩

def Ult (𝔄 : I → model L) (F : ultrafilter I) : Type* :=
quotient (ult 𝔄 F: setoid (Π i, |𝔄 i|))

def to_quotient {𝔄 : I → model L} {F : ultrafilter I} (u : Π i, |𝔄 i|) : Ult 𝔄 F := quotient.mk' u

def to_quotients {𝔄 : I → model L} {F : ultrafilter I} {n} (u : dvector (Π i, |𝔄 i|) n) : dvector (Ult 𝔄 F) n :=
quotient.mk_vec' u

notation `⟦`u`⟧*` :max := to_quotient u

instance : inhabited (Ult 𝔄 F) := ⟨⟦λ i, (𝔄 i).one⟧*⟩

namespace Ult

local infix `≋`:80 := (@setoid.vec_r _ (ult 𝔄 F) _)

@[elab_as_eliminator]
protected lemma ind_on {C : Ult 𝔄 F → Prop} (u : Ult 𝔄 F)
  (h : ∀ u : Π i, |𝔄 i|, C ⟦u⟧*) : C u :=
quotient.induction_on' u h

@[elab_as_eliminator, reducible]
protected def lift_on {φ} (d : Ult 𝔄 F) (f : (Π i, |𝔄 i|) → φ)
  (h : ∀ (v u : Π i, |𝔄 i|), v ~[F] u → f v = f u) : φ :=
quotient.lift_on' d f h

@[simp]
protected lemma lift_on_eq {φ} (u₀ : Π i, |𝔄 i|) (f : (Π i, |𝔄 i|) → φ)
  (h : ∀ v u, v ~[F] u → f v = f u) : fopl.Ult.lift_on F ⟦u₀⟧* f h = f u₀ := rfl

@[elab_as_eliminator, reducible, simp]
protected def lift_on₂ {φ} (u₁ u₂ : Ult 𝔄 F) (f : (Π i, |𝔄 i|) → (Π i, |𝔄 i|) → φ)
  (h : ∀ u₁ u₂ v₁ v₂, u₁ ~[F] v₁ → u₂ ~[F] v₂ → f u₁ u₂ = f v₁ v₂) : φ :=
quotient.lift_on₂' u₁ u₂ f h

@[simp]
protected lemma lift_on₂_eq {φ} (u₁ u₂ : Π i, |𝔄 i|) (f : (Π i, |𝔄 i|) → (Π i, |𝔄 i|) → φ)
  (h : ∀ t₁ t₂ u₁ u₂, (t₁ ~[F] u₁) → (t₂ ~[F] u₂) → f t₁ t₂ = f u₁ u₂) :
  fopl.Ult.lift_on₂ F ⟦u₁⟧* ⟦u₂⟧* f h = f u₁ u₂ := rfl

@[simp] lemma of_eq_of {u₁ u₂ : Π i, |𝔄 i|} : (⟦u₁⟧* : Ult 𝔄 F) = ⟦u₂⟧* ↔ u₁ ~[F] u₂ :=
by simp[to_quotient, quotient.eq']

@[elab_as_eliminator, reducible]
protected def lift_on_vec {φ} {n} (d : dvector (Ult 𝔄 F) n) (f : dvector (Π i, |𝔄 i|) n → φ)
  (h : ∀ (v u : dvector (Π i, |𝔄 i|) n), v ≋ u → f v = f u) : φ :=
quotient.lift_on_vec d f h

@[simp]
protected lemma lift_on_vec_eq {φ} {n} (u : dvector (Π i, |𝔄 i|) n) (f : dvector (Π i, |𝔄 i|) n → φ)
  (h : ∀ (v u : dvector (Π i, |𝔄 i|) n), v ≋ u → f v = f u) :
fopl.Ult.lift_on_vec F ᵥ⟦u⟧ f h = f u := quotient.lift_on_vec_eq u f h

@[simp]
protected lemma lift_on_nil_eq {φ} (f : dvector (Π i, |𝔄 i|) 0 → φ)
  (h : ∀ (v u : dvector (Π i, |𝔄 i|) 0), v ≋ u → f v = f u) :
fopl.Ult.lift_on_vec F dvector.nil f h = f dvector.nil := quotient.lift_on_vec_eq _ f h 

#check quotient.quo_to_dvec

lemma equivs_mem : ∀ {n} {u₁ u₂ : dvector (Π i, |𝔄 i|) n},
  u₁ ≋ u₂ → {i | u₁.app i = u₂.app i} ∈ F
| 0     dvector.nil dvector.nil _ := by { simp, exact F.univ_sets }
| (n+1) (u₁ :: us₁) (u₂ :: us₂) h := by { simp at*,
    have : {i | u₁ i = u₂ i} ∩ {i | us₁.app i = us₂.app i} ⊆ {i | u₁ i = u₂ i ∧ us₁.app i = us₂.app i},
    { intros i hi, simp* at* },
    refine filter.mem_sets_of_superset (filter.inter_mem_sets h.1 (equivs_mem h.2)) this }

lemma fn_equiv {n} {u₁ u₂ : dvector (Π i, |𝔄 i|) n} (h : u₁ ≋ u₂) (f : L.fn n) :
  (λ i, (𝔄 i).fn f (u₁.app i)) ~[F] (λ i, (𝔄 i).fn f (u₂.app i)) :=
begin
  simp[uequiv] at*,
  have : {i | u₁.app i = u₂.app i} ⊆ {i | (𝔄 i).fn f (u₁.app i) = (𝔄 i).fn f (u₂.app i)},
  { intros i hi, simp* at* },
  exact F.sets_of_superset (equivs_mem F h) this
end

lemma pr_equiv : ∀ {n} {u₁ u₂ : dvector (Π i, |𝔄 i|) n} (h : u₁ ≋ u₂) (p : L.pr n),
  {i | (𝔄 i).pr p (u₁.app i)} ∈ F ↔ {i | (𝔄 i).pr p (u₂.app i)} ∈ F :=
begin
  suffices : ∀ {n} {u₁ u₂ : dvector (Π i, |𝔄 i|) n} (h : u₁ ≋ u₂) (p : L.pr n),
  {i | (𝔄 i).pr p (u₁.app i)} ∈ F → {i | (𝔄 i).pr p (u₂.app i)} ∈ F,
  { intros n u₁ u₂ eqn p, refine ⟨this eqn p, this (@setoid.vec_r_symm _ (ult _ _) _ _ _ eqn) _⟩ },
  intros n u₁ u₂ eqn p h,
  have : {i | (𝔄 i).pr p (u₁.app i)} ∩ {i | u₁.app i = u₂.app i} ⊆ {i | (𝔄 i).pr p (u₂.app i)},
  { intros i hi, simp* at*, simp[←hi.2], exact hi.1 },
  refine filter.mem_sets_of_superset (filter.inter_mem_sets h (equivs_mem _ eqn)) this
end

def product_fn (n) (f : L.fn n) : dvector (Ult 𝔄 F) n → Ult 𝔄 F :=
λ v, fopl.Ult.lift_on_vec F v (λ u, (⟦λ i, (𝔄 i).fn f (u.app i)⟧* : Ult 𝔄 F)) $ λ u₁ u₂ eqn,
by { simp, exact fn_equiv F eqn f }

def product_pr (n) (p : L.pr n) : dvector (Ult 𝔄 F) n → Prop :=
λ v, fopl.Ult.lift_on_vec F v (λ u, {i | (𝔄 i).pr p (u.app i)} ∈ F) $ λ u₁ u₂ eqn,
by { simp, exact pr_equiv F eqn p }

def product (𝔄 : I → model L) (F : ultrafilter I) : model L := ⟨Ult 𝔄 F, default _, product_fn F, product_pr F⟩
notation `ℿ `𝔄` ⫽ `F:90 := product 𝔄 F

variables {F}

@[simp] lemma ult_eq : Ult 𝔄 F = |ℿ 𝔄 ⫽ F| := rfl

private lemma model_exists (p : form L) {e : ∀ i, ℕ → |𝔄 i|} (h : {i | ∃ u, p.val (u ^ˢ e i)} ∈ F) :
  ∃ (u : Π i, |𝔄 i|), {i | p.val ((u i) ^ˢ e i)} ∈ F :=
begin
  have : ∀ i, ∃ u, i ∈ {i | ∃ u, p.val (u ^ˢ e i)} → p.val (u ^ˢ e i),
  { intros i, simp, by_cases C : i ∈ {i | ∃ u, p.val (u ^ˢ e i)}; simp at C,
    { rcases C with ⟨u, hu⟩, refine ⟨u, λ v _, hu⟩ },
    { refine ⟨default _, λ _ h, _⟩, exfalso, refine C _ h } },
  rcases classical.skolem.mp this with ⟨u, hu⟩,
  refine ⟨u, _⟩, exact F.sets_of_superset h hu
end
#check quotient.lift_on_vec_eq

lemma model_fn_eq {n} (f : L.fn n) : (ℿ 𝔄 ⫽ F).fn f = product_fn F _ f := rfl

lemma model_pr_eq {n} (r : L.pr n) : (ℿ 𝔄 ⫽ F).pr r = product_pr F _ r := rfl

lemma models_pr_iff_lmm : ∀ {n} (v : vecterm L n) (e : ∀ i, ℕ → |𝔄 i|),
  (@vecterm.val _ (ℿ 𝔄 ⫽ F) (λ n, ⟦λ i, e i n⟧*) _ v) = ᵥ⟦dvector.partition (λ i, @vecterm.val _ (𝔄 i) (λ n, e i n) _ v)⟧
| _ (vecterm.cons a v) e := by {
  have IH₁ := models_pr_iff_lmm v e, have IH₂ := models_pr_iff_lmm a e,
  simp at IH₁ IH₂, simp[quotient.vquotient_cons, IH₁, IH₂], refine ⟨by refl, by refl⟩ }
| _ (#n)              _ := by { simp[quotient.vquotient_cons], refine ⟨by refl, by refl⟩ } 
| _ (vecterm.const c) _ := by { simp[quotient.vquotient_cons], refine ⟨by refl, by refl⟩ }
| _ (vecterm.app f v) _ := by { simp[model_fn_eq, product_fn, models_pr_iff_lmm v], refl }

lemma models_pr_iff {n} (r : L.pr (n + 1)) (v : vecterm L n) (e : ∀ i, ℕ → |𝔄 i|) :
  (ℿ 𝔄 ⫽ F).pr r (v.val (λ n, ⟦(λ i, e i n)⟧*)) ↔ {i | (𝔄 i).pr r (v.val (e i))} ∈ F :=
begin
  have : (@vecterm.val _ (ℿ 𝔄 ⫽ F) (λ n, ⟦λ i, e i n⟧*) _ v) = ᵥ⟦dvector.partition (λ i, @vecterm.val _ (𝔄 i) (λ n, e i n) _ v)⟧,
  from models_pr_iff_lmm v e,
  simp[this, model_pr_eq, product_pr]
end

lemma vecterm_eq_iff : ∀ {n} (v₁ v₂ : vecterm L n) (e : ∀ i, ℕ → |𝔄 i|),
  @vecterm.val _ (ℿ 𝔄 ⫽ F) (λ n, ⟦(λ i, e i n)⟧*) _ v₁ = @vecterm.val _ (ℿ 𝔄 ⫽ F) (λ n, ⟦(λ i, e i n)⟧*) _ v₂ ↔
  {i | v₁.val (e i) = v₂.val (e i)} ∈ F
| (n+1) (vecterm.cons t₁ v₁) (vecterm.cons t₂ v₂) e := by { 
    simp[vecterm_eq_iff t₁, vecterm_eq_iff t₂, vecterm_eq_iff v₁, vecterm_eq_iff v₂],
    exact filter.eventually_and.symm }
| 0     t₁                   t₂                   e := by {
    cases t₁; cases t₂; simp[model_fn_eq, product_fn, models_pr_iff_lmm]; try { refl } }

-- Łoś's theorem
theorem fundamental : ∀ (p : form L) (e : ∀ i, ℕ → |𝔄 i|),
  ℿ 𝔄 ⫽ F ⊧[λ n, ⟦λ i, e i n⟧*] p ↔ {i | 𝔄 i ⊧[e i] p} ∈ F
| (form.const p) e := by simp; refl
| (form.app p v) e := models_pr_iff p _ _
| (t₁ =̇ t₂)      e := by simp[vecterm_eq_iff]
| (p →̇ q)       e := by { simp[fundamental p, fundamental q],
    show {i | p.val (e i)} ∈ F → {i | q.val (e i)} ∈ F ↔ {i | p.val (e i) → q.val (e i)} ∈ F,
    split,
    { intros h, by_cases C : {i | form.val (e i) p} ∈ F,
      { have : {i | q.val (e i)} ⊆ {i | p.val (e i) → q.val (e i)}, { intros i hi, simp* at* },
        exact F.sets_of_superset (h C) this },
      { have : {i | p.val (e i)}ᶜ ∈ F, from ultrafilter.compl_mem_iff_not_mem.mpr C,
        have ss : {i | p.val (e i)}ᶜ ⊆ {i | p.val (e i) → q.val (e i)},
        { intros i hi, simp* at* },
        exact F.sets_of_superset this ss } },
    { intros h₁ h₂,
      have : {i | p.val (e i)} ∩ {i | p.val (e i) → q.val (e i)} ⊆ {i | q.val (e i)},
      { intros i hi, simp at*, refine hi.2 hi.1 },
      exact filter.mp_sets h₂ h₁ } }
| (¬̇p)          e := by { simp[fundamental p], exact ultrafilter.eventually_not.symm }
| (Ȧp)          e := by { simp, 
    calc
      (∀ u, ℿ 𝔄 ⫽ F ⊧[u ^ˢ λ n, ⟦λ i, e i n⟧*] p)
          ↔ (∀ (u : Π i, |𝔄 i|), ℿ 𝔄 ⫽ F ⊧[λ n, ⟦λ i, (λ i, (u i) ^ˢ (e i)) i n⟧*] p) :
        by { have eqn: ∀ u, (⟦u⟧* ^ˢ λ n, ⟦(λ i, e i n)⟧*) = (λ n, ⟦(λ i, (u i) ^ˢ e i $ n)⟧* : ℕ → |ℿ 𝔄 ⫽ F|),
             { intros i, funext x, cases x; simp }, simp, split,
             { intros h u, have := h ⟦u⟧*, simp[eqn] at this, exact this },
             { intros h u, induction u using fopl.Ult.ind_on, simp[eqn, h] } }
      ... ↔ (∀ (u : Π i, |𝔄 i|), {i | p.val ((u i) ^ˢ e i)} ∈ F) :
        by { split, { intros h u, simp[←fundamental  p _, h] }, { intros h u, simp[fundamental  p _, h] } }
      ... ↔ {i | ∀ (u : |𝔄 i|), p.val (u ^ˢ e i)} ∈ F : 
        by { split,
             { contrapose, simp[←ultrafilter.compl_mem_iff_not_mem, ←set.compl_eq_compl, set.compl], intros h,
               show ∃ (u : Π i, |𝔄 i|), {i | ¬p.val ((u i) ^ˢ e i)} ∈ F, from model_exists (¬̇p) h },
             { refine λ h u, F.sets_of_superset h (λ _ _ , by simp* at*) } } }

theorem fundamental1 {p : form L} (h : sentence p) :
  ℿ 𝔄 ⫽ F ⊧ p ↔ {i | 𝔄 i ⊧ p} ∈ F :=
by { have : ℿ 𝔄 ⫽ F ⊧[λ n, ⟦(λ i, default (|𝔄 i|))⟧*] p ↔ {i | 𝔄 i ⊧[λ n, default (|𝔄 i|)] p} ∈ F,
     from fundamental p (λ i n, default (|𝔄 i|)),
     simp[eval_sentence_iff h] at this, exact this }

end Ult




end fopl