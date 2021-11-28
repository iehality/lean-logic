import deduction semantics lindenbaum data.equiv.encodable.basic order.filter.ultrafilter
open encodable

universes u v

namespace fopl
variables {L : language.{u}} {I : Type u} [inhabited I] (F : ultrafilter I) {𝔄 : I → model L}

local infix ` ≃₁ `:80 := ((≃) : term L → term L → formula L)
local prefix `∏₁ `:64 := (has_univ_quantifier.univ : formula L → formula L)

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
     exact F.sets_of_superset (F.inter_sets h₁ h₂) this }

theorem uequiv_equivalence : equivalence (@uequiv L I _ F 𝔄) :=
⟨uequiv_refl F, λ _ _ , uequiv_symm F, λ _ _ _, uequiv_trans F⟩


@[reducible, simp, instance]
def ult (𝔄 : I → model L) (F : ultrafilter I) : setoid (Π i, |𝔄 i|) := ⟨@uequiv L I _ F 𝔄, uequiv_equivalence F⟩

def Ult (𝔄 : I → model L) (F : ultrafilter I) : Type* :=
quotient (ult 𝔄 F: setoid (Π i, |𝔄 i|))

#check @Ult

def to_quotient {𝔄 : I → model L} {F : ultrafilter I} (u : Π i, |𝔄 i|) : Ult 𝔄 F := quotient.mk' u

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

@[elab_as_eliminator, reducible]
protected def lift_on_finitary {φ} {n : ℕ} (v : finitary (Ult 𝔄 F) n) (f : finitary (Π i, |𝔄 i|) n → φ)
  (h : ∀ v₁ v₂ : finitary (Π i, |𝔄 i|) n, (∀ n, (v₁ n) ~[F] (v₂ n)) → f v₁ = f v₂) : φ :=
quotient.lift_on_finitary v f h 

@[simp]
protected lemma lift_on_finitary_eq {φ} {n} (v : finitary (Π i, |𝔄 i|) n) (f : finitary (Π i, |𝔄 i|) n → φ)
  (h : ∀ v₁ v₂ : finitary (Π i, |𝔄 i|) n, (∀ n, (v₁ n) ~[F] (v₂ n)) → f v₁ = f v₂) :
  fopl.Ult.lift_on_finitary F (λ x, ⟦v x⟧*) f h = f v :=
quotient.lift_on_finitary_eq v f h

@[simp] lemma of_eq_of {u₁ u₂ : Π i, |𝔄 i|} : (⟦u₁⟧* : Ult 𝔄 F) = ⟦u₂⟧* ↔ u₁ ~[F] u₂ :=
by simp[to_quotient, quotient.eq']

lemma equivs_mem {n} {v₁ v₂ : finitary (Π i, |𝔄 i|) n} (h : ∀ (x : fin n), {i : I | v₁ x i = v₂ x i} ∈ F) :
  {i | (λ x, v₁ x i) = (λ x, v₂ x i)} ∈ F := 
begin
  induction n with n IH,
  { have : {i : I | (λ x, v₁ x i) = (λ x, v₂ x i)} = set.univ,
    { ext i, simp }, rw this, exact F.univ_sets },
  { have ss : {i | v₁.head i = v₂.head i} ∩ {i | (λ x, v₁.tail x i) = (λ x, v₂.tail x i)} ⊆ {i : I | (λ x, v₁ x i) = (λ x, v₂ x i)},
    { intros i hi, rw [←finitary.tail_cons_head v₁, ←finitary.tail_cons_head v₂], simp at*,
      funext x, cases fin.cases' x with h h,
      { rcases h with ⟨x', rfl⟩, simp, exact (@congr_fun _ _ _ _ hi.2) x' },
      { rcases h with rfl, simp[hi.1] } },
    have : {i | v₁.head i = v₂.head i} ∩ {i | (λ x, v₁.tail x i) = (λ x, v₂.tail x i)} ∈ F,
      from (F.inter_sets (h _) (@IH v₁.tail v₂.tail (λ x, h _))),
    refine F.sets_of_superset this ss }
end

lemma fn_equiv {n} {v₁ v₂ : finitary (Π i, |𝔄 i|) n} (h : ∀ x, v₁ x ~[F] v₂ x) (f : L.fn n) :
  (λ i, (𝔄 i).fn f (λ x, v₁ x i)) ~[F] (λ i, (𝔄 i).fn f (λ x, v₂ x i)) :=
begin
  simp[uequiv] at*,
  have : {i | (λ x, v₁ x i) = (λ x, v₂ x i)} ⊆ {i | (𝔄 i).fn f (λ x, v₁ x i) = (𝔄 i).fn f (λ x, v₂ x i)},
  { intros i hi, simp* at* },
  exact F.sets_of_superset (equivs_mem F h) this
end

lemma pr_equiv : ∀ {n} {v₁ v₂ : finitary (Π i, |𝔄 i|) n} (h : ∀ x, v₁ x ~[F] v₂ x) (p : L.pr n),
  {i | (𝔄 i).pr p (λ x, v₁ x i)} ∈ F ↔ {i | (𝔄 i).pr p (λ x, v₂ x i)} ∈ F :=
begin
  suffices : ∀ {n} {v₁ v₂ : finitary (Π i, |𝔄 i|) n} (h : ∀ x, v₁ x ~[F] v₂ x) (p : L.pr n),
  {i | (𝔄 i).pr p (λ x, v₁ x i)} ∈ F → {i | (𝔄 i).pr p (λ x, v₂ x i)} ∈ F,
  { intros n v₁ v₂ eqn p, refine ⟨this eqn p, this (λ x, uequiv_symm _ (eqn x)) p⟩ },
  intros n v₁ v₂ eqn p h,
  have : {i | (𝔄 i).pr p (λ x, v₁ x i)} ∩ {i | (λ x, v₁ x i) = (λ x, v₂ x i)} ⊆ {i | (𝔄 i).pr p (λ x, v₂ x i)},
  { intros i hi, simp* at*, simp[←hi.2], exact hi.1 },
  refine F.sets_of_superset (F.inter_sets h (equivs_mem _ eqn)) this
end

def product_fn (n) (f : L.fn n) : finitary (Ult 𝔄 F) n → Ult 𝔄 F :=
λ v, fopl.Ult.lift_on_finitary F v (λ v, (⟦λ i, (𝔄 i).fn f (λ x, v x i)⟧* : Ult 𝔄 F)) $ λ u₁ u₂ eqn,
by { simp, exact fn_equiv F eqn f }

def product_pr (n) (p : L.pr n) : finitary (Ult 𝔄 F) n → Prop :=
λ v, fopl.Ult.lift_on_finitary F v (λ v, {i | (𝔄 i).pr p (λ x, v x i)} ∈ F) $ λ u₁ u₂ eqn,
by { simp, exact pr_equiv F eqn p }

def product (𝔄 : I → model L) (F : ultrafilter I) : model L := ⟨Ult 𝔄 F, default _, product_fn F, product_pr F⟩
notation `ℿ `𝔄` ⫽ `F:90 := product 𝔄 F

variables {F}

@[simp] lemma ult_eq : Ult 𝔄 F = |ℿ 𝔄 ⫽ F| := rfl

private lemma model_exists (p : formula L) {e : ∀ i, ℕ → |𝔄 i|} (h : {i | ∃ u, p.val (u ⌢ e i)} ∈ F) :
  ∃ (u : Π i, |𝔄 i|), {i | p.val ((u i) ⌢ e i)} ∈ F :=
begin
  have : ∀ i, ∃ u, i ∈ {i | ∃ u, p.val (u ⌢ e i)} → p.val (u ⌢ e i),
  { intros i, simp, by_cases C : i ∈ {i | ∃ u, p.val (u ⌢ e i)}; simp at C,
    { rcases C with ⟨u, hu⟩, refine ⟨u, λ v _, hu⟩ },
    { refine ⟨default _, λ _ h, _⟩, exfalso, refine C _ h } },
  rcases classical.skolem.mp this with ⟨u, hu⟩,
  refine ⟨u, _⟩, exact F.sets_of_superset h hu
end
#check quotient.lift_on_vec_eq

lemma model_fn_eq {n} (f : L.fn n) : (ℿ 𝔄 ⫽ F).fn f = product_fn F _ f := rfl

lemma model_pr_eq {n} (r : L.pr n) : (ℿ 𝔄 ⫽ F).pr r = product_pr F _ r := rfl

lemma models_pr_iff_lmm : ∀ (t : term L) (e : ∀ i, ℕ → |𝔄 i|),
  (@term.val _ (ℿ 𝔄 ⫽ F) (λ n, ⟦λ i, e i n⟧*) t) = ⟦λ i, @term.val _ (𝔄 i) (λ n, e i n) t⟧*
| (#n)                _ := by simp 
| (@term.app _ n f v) e :=
  by { simp[model_fn_eq, product_fn],
       let v' : finitary (Π i, |𝔄 i|) n := λ x i, (v x).val (e i),
       have : (λ x, @term.val _ (ℿ 𝔄 ⫽ F) (λ n, ⟦(λ i, e i n)⟧*) (v x)) = λ x, ⟦v' x⟧*,
       { funext x, simp[v', models_pr_iff_lmm (v x)] },
       simp[this] }

lemma models_pr_iff {n} (r : L.pr n) (v : finitary (term L) n) (e : ∀ i, ℕ → |𝔄 i|) :
  (ℿ 𝔄 ⫽ F).pr r (λ x, (v x).val (λ n, ⟦λ i, e i n⟧*)) ↔ {i | (𝔄 i).pr r (λ x, (v x).val (e i))} ∈ F :=
by simp[models_pr_iff_lmm, model_pr_eq, product_pr]

-- Łoś's theorem
theorem fundamental_param : ∀ (p : formula L) (e : ∀ i, ℕ → |𝔄 i|),
  ℿ 𝔄 ⫽ F ⊧[λ n, ⟦λ i, e i n⟧*] p ↔ {i | 𝔄 i ⊧[e i] p} ∈ F
| (formula.app p v) e := models_pr_iff p _ _
| (t₁ ≃₁ t₂)      e := by simp[models_pr_iff_lmm]; refl
| (p ⟶ q)       e := by { simp[fundamental_param p, fundamental_param q],
    show {i | p.val (e i)} ∈ F → {i | q.val (e i)} ∈ F ↔ {i | p.val (e i) → q.val (e i)} ∈ F,
    split,
    { intros h, by_cases C : {i | formula.val (e i) p} ∈ F,
      { have : {i | q.val (e i)} ⊆ {i | p.val (e i) → q.val (e i)}, { intros i hi, simp* at* },
        exact F.sets_of_superset (h C) this },
      { have : {i | p.val (e i)}ᶜ ∈ F, from ultrafilter.compl_mem_iff_not_mem.mpr C,
        have ss : {i | p.val (e i)}ᶜ ⊆ {i | p.val (e i) → q.val (e i)},
        { intros i hi, simp* at* },
        exact F.sets_of_superset this ss } },
    { intros h₁ h₂,
      have : {i | p.val (e i)} ∩ {i | p.val (e i) → q.val (e i)} ⊆ {i | q.val (e i)},
      { intros i hi, simp at*, refine hi.2 hi.1 },
      exact filter.mp_mem h₂ h₁ } }
| (⁻p)          e := by { simp[fundamental_param p], exact ultrafilter.eventually_not.symm }
| (∏₁ p)          e := by { simp, 
    calc
      (∀ u, ℿ 𝔄 ⫽ F ⊧[u ⌢ λ n, ⟦λ i, e i n⟧*] p)
          ↔ (∀ (u : Π i, |𝔄 i|), ℿ 𝔄 ⫽ F ⊧[λ n, ⟦λ i, (λ i, (u i) ⌢ (e i)) i n⟧*] p) :
        by { have eqn: ∀ u, (⟦u⟧* ⌢ λ n, ⟦(λ i, e i n)⟧*) = (λ n, ⟦(λ i, (u i) ⌢ e i $ n)⟧* : ℕ → |ℿ 𝔄 ⫽ F|),
             { intros i, funext x, cases x; simp[concat] }, simp, split,
             { intros h u, have := h ⟦u⟧*, simp[eqn] at this, exact this },
             { intros h u, induction u using fopl.Ult.ind_on, simp[eqn, h] } }
      ... ↔ (∀ (u : Π i, |𝔄 i|), {i | p.val ((u i) ⌢ e i)} ∈ F) :
        by { split, { intros h u, simp[←fundamental_param  p _, h] }, { intros h u, simp[fundamental_param  p _, h] } }
      ... ↔ {i | ∀ (u : |𝔄 i|), p.val (u ⌢ e i)} ∈ F : 
        by { split,
             { contrapose, simp[←ultrafilter.compl_mem_iff_not_mem, ←set.compl_eq_compl, set.compl], intros h,
               show ∃ (u : Π i, |𝔄 i|), {i | ¬p.val ((u i) ⌢ e i)} ∈ F, from model_exists (⁻p) h },
             { refine λ h u, F.sets_of_superset h (λ _ _ , by simp* at*) } } }

theorem fundamental {p : formula L} :
  ℿ 𝔄 ⫽ F ⊧ p ↔ {i | 𝔄 i ⊧ p} ∈ F :=
begin
  calc
    ℿ 𝔄 ⫽ F ⊧ p ↔ ℿ 𝔄 ⫽ F ⊧ nfal p p.arity : nfal_models_iff.symm
    ...         ↔ {i | 𝔄 i ⊧ nfal p p.arity} ∈ F :
      by { have := fundamental_param (nfal p p.arity) (λ i n, default (|𝔄 i|)),
           simp[eval_sentence_iff (formula.nfal_sentence p)] at this, exact this }
    ...         ↔ {i | 𝔄 i ⊧ p} ∈ F :
      by { have : {i | 𝔄 i ⊧ nfal p p.arity} = {i | 𝔄 i ⊧ p},
           { ext i, simp, refine nfal_models_iff },
           simp[this] }
end

end Ult
end fopl

namespace fopl
variables {L : language.{u}} 

def fintheory (T : theory L) := {S : finset (formula L) // ∀ {x}, x ∈ S → x ∈ T}

variables {T : theory L}

def fintheory.empty {T : theory L} : fintheory T := ⟨∅, by simp⟩
instance : inhabited (fintheory T) := ⟨⟨∅, by simp⟩⟩

noncomputable def fintheory.insert (P : fintheory T) (p : formula L) (h : p ∈ T) : fintheory T :=
⟨insert p P.val, λ x hx,  by { simp at hx, cases hx, simp[hx, h], refine P.property hx }⟩

@[simp] lemma fintheory.insert_val (P : fintheory T) (p : formula L) (h : T p) :
  (P.insert p h).val = insert p P.val := rfl

instance : has_coe (fintheory T) (set (formula L)) := ⟨λ S, S.val⟩

namespace compactness

variables (𝔄 : fintheory T → model L) 

def formdomain (p : formula L) : set (fintheory T) := {i | 𝔄 i ⊧ p}

def F : set (set (fintheory T)) := {x | ∃ p, T p ∧ x = formdomain 𝔄 p}

private lemma finite_intersection_lmm (h : ∃ p, T p) (H : ∀ (i : fintheory T) p, p ∈ i.val → 𝔄 i ⊧ p) :
  ∀ S : finset (set (fintheory T)), (↑S : set (set (fintheory T))) ⊆ F 𝔄 →
  ∃ P : fintheory T,
  (∀ p, p ∈ P.val → formdomain 𝔄 p ∈ S) ∧ (∀ S', S' ∈ S → ∃ p, p ∈ P.val ∧ S' = formdomain 𝔄 p) :=
begin
  intros S, induction S using finset.induction with i S i_fresh IH,
  { intros _, simp[set.nonempty], rcases h with ⟨p₀, hyp_p₀⟩,
    refine ⟨⟨∅, by simp⟩, _⟩, unfold_coes, simp },
  { intros h, simp at*,
    have lmm₁ : ↑S ⊆ F 𝔄, from set.subset.trans (set.subset_insert _ _) h,
    have : ∃ (P : fintheory T),
      (∀ p, p ∈ ↑P → formdomain 𝔄 p ∈ S) ∧ (∀ S', S' ∈ S → ∃ p, p ∈ ↑P ∧ S' = formdomain 𝔄 p),
    from IH lmm₁, rcases this with ⟨P, IH₁, IH₂⟩,
    have : ∃ p, T p ∧ i = formdomain 𝔄 p, from h (set.mem_insert i ↑S),
    rcases this with ⟨p, hyp_p, rfl⟩,
    refine ⟨P.insert p hyp_p, _, _, _⟩; unfold_coes; simp,
    { refine λ q hyp_q, or.inr (IH₁ _ hyp_q) },
    { refine ⟨p, or.inl rfl, rfl⟩ },
    { intros S' hyp_S',
      have : ∃ p, p ∈ ↑P ∧ S' = formdomain 𝔄 p, from IH₂ _ hyp_S', rcases this with ⟨p, hyp, rfl⟩,
      refine ⟨p, or.inr hyp, rfl⟩ } }
end

theorem finite_intersection (h : ∃ p, T p) (H : ∀ (i : fintheory T) p, p ∈ i.val → 𝔄 i ⊧ p) :
  ∀ S : finset (set (fintheory T)), 
  (↑S : set (set (fintheory T))) ⊆ F 𝔄 → (⋂₀ (↑S : set (set (fintheory T)))).nonempty :=
begin
  intros S hS, have := finite_intersection_lmm _ h H S hS, rcases this with ⟨P, hyp⟩,
  refine ⟨P, λ S' hS', _⟩, 
  have := hyp.2 S' hS', rcases this with ⟨p, hyp_p, rfl⟩, simp[formdomain] at*,
  refine H _ _ hyp_p
end

theorem ultrafilter_exists (h : ∃ p, p ∈ T) (H : ∀ (i : fintheory T) p, p ∈ i.val → 𝔄 i ⊧ p) :
  ∃ U : ultrafilter (fintheory T), F 𝔄 ⊆ U.to_filter.sets :=
ultrafilter.exists_ultrafilter_of_finite_inter_nonempty _ (finite_intersection _ h H)

theorem compact (T : theory L) :
  (∃ 𝔄, 𝔄 ⊧ₜₕ T) ↔ (∀ S : finset (formula L), (∀ {p}, p ∈ S → p ∈ T) → ∃ 𝔄, 𝔄 ⊧ₜₕ (S : set (formula L))) :=
  ⟨by { intros H S hyp_S, rcases H with ⟨𝔄, hyp⟩,
        refine ⟨𝔄, λ p h, hyp _ (hyp_S h)⟩ },
   by { suffices : (∀ S : fintheory T, ∃ 𝔄, 𝔄 ⊧ₜₕ (↑S : set (formula L))) → (∃ 𝔅, 𝔅 ⊧ₜₕ T),
        { intros h, refine this (λ S, _),
          rcases h S.val S.property with ⟨𝔄, hyp_𝔄⟩, refine ⟨𝔄, hyp_𝔄⟩ },
    intros H, by_cases C : T = ∅,
        { simp[C], refine empty_has_model },
        { have ex : ∃ p, p ∈ T, { by_contra, simp at*, refine C _, { ext x, simp, refine h _ } }, 
          have : ∃ (𝔄 : fintheory T → model L), ∀ (i : fintheory T) p, p ∈ i.val → 𝔄 i ⊧ p,
          from classical.skolem.mp H, rcases this with ⟨𝔄, hyp_𝔄⟩,
          have := ultrafilter_exists _ ex hyp_𝔄, rcases this with ⟨U, hyp_U⟩,
          use ℿ 𝔄 ⫽ U, intros p hyp_p, rw Ult.fundamental,
          have : {i | 𝔄 i ⊧ p} ∈ F 𝔄, { refine ⟨p, hyp_p, rfl⟩ },
          exact hyp_U this } }⟩

end compactness

end fopl
