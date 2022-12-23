import QL.FOL.semantics order.filter.ultrafilter data.finset.basic
open encodable

universes u v

namespace fol

open_locale logic_symbol
open logic.semantics

variables {L : language.{u}} {μ : Type v} {n : ℕ} {I : Type u} [inhabited I] (F : ultrafilter I)
  {𝔄 : I → nonempty_Structure L}

def uequiv : (Π i, 𝔄 i) → (Π i, 𝔄 i) → Prop :=
λ u₁ u₂, {i | u₁ i = u₂ i} ∈ F

notation u` ~[`:80 F`] `v:80 := uequiv F u v

@[simp] lemma uequiv_refl (u : Π i, 𝔄 i) : u ~[F] u :=
by { simp[uequiv], exact F.univ_sets }

lemma uequiv_symm {u₁ u₂ : Π i, 𝔄 i} : u₁ ~[F] u₂ → u₂ ~[F] u₁ :=
by { simp[uequiv], have : {i | u₁ i = u₂ i} = {i | u₂ i = u₁ i}, { ext, simp, exact eq_comm }, simp[this] }

lemma uequiv_trans {u₁ u₂ u₃ : Π i, 𝔄 i} : u₁ ~[F] u₂ → u₂ ~[F] u₃ → u₁ ~[F] u₃ :=
by { simp[uequiv], intros h₁ h₂,
     have : {i | u₁ i = u₂ i} ∩ {i | u₂ i = u₃ i} ⊆ {i | u₁ i = u₃ i},
     { intros i hi, simp* at* },
     exact F.sets_of_superset (F.inter_sets h₁ h₂) this }

theorem uequiv_equivalence : equivalence (@uequiv L I _ F 𝔄) :=
⟨uequiv_refl F, λ _ _ , uequiv_symm F, λ _ _ _, uequiv_trans F⟩


@[reducible, simp, instance]
def ult (𝔄 : I → nonempty_Structure L) (F : ultrafilter I) : setoid (Π i, 𝔄 i) := ⟨@uequiv L I _ F 𝔄, uequiv_equivalence F⟩

def Ult (𝔄 : I → nonempty_Structure L) (F : ultrafilter I) : Type* :=
quotient (ult 𝔄 F: setoid (Π i, 𝔄 i))

def to_quotient {𝔄 : I → nonempty_Structure L} {F : ultrafilter I} (u : Π i, 𝔄 i) : Ult 𝔄 F := quotient.mk' u

notation `⟦`u`⟧*` :max := to_quotient u

instance : inhabited (Ult 𝔄 F) := ⟨⟦λ i, default⟧*⟩

namespace Ult
open logic.semantics

@[elab_as_eliminator]
protected lemma ind_on {C : Ult 𝔄 F → Prop} (u : Ult 𝔄 F)
  (h : ∀ u : Π i, 𝔄 i, C ⟦u⟧*) : C u :=
quotient.induction_on' u h

@[elab_as_eliminator, reducible]
protected def lift_on {φ} (d : Ult 𝔄 F) (f : (Π i, 𝔄 i) → φ)
  (h : ∀ (v u : Π i, 𝔄 i), v ~[F] u → f v = f u) : φ :=
quotient.lift_on' d f h

@[simp]
protected lemma lift_on_eq {φ} (u₀ : Π i, 𝔄 i) (f : (Π i, 𝔄 i) → φ)
  (h : ∀ v u, v ~[F] u → f v = f u) : fol.Ult.lift_on F ⟦u₀⟧* f h = f u₀ := rfl

@[elab_as_eliminator, reducible, simp]
protected def lift_on₂ {φ} (u₁ u₂ : Ult 𝔄 F) (f : (Π i, 𝔄 i) → (Π i, 𝔄 i) → φ)
  (h : ∀ u₁ u₂ v₁ v₂, u₁ ~[F] v₁ → u₂ ~[F] v₂ → f u₁ u₂ = f v₁ v₂) : φ :=
quotient.lift_on₂' u₁ u₂ f h

@[simp]
protected lemma lift_on₂_eq {φ} (u₁ u₂ : Π i, 𝔄 i) (f : (Π i, 𝔄 i) → (Π i, 𝔄 i) → φ)
  (h : ∀ t₁ t₂ u₁ u₂, (t₁ ~[F] u₁) → (t₂ ~[F] u₂) → f t₁ t₂ = f u₁ u₂) :
  fol.Ult.lift_on₂ F ⟦u₁⟧* ⟦u₂⟧* f h = f u₁ u₂ := rfl

@[elab_as_eliminator, reducible]
protected def lift_on_finitary {φ} {n : ℕ} (v : finitary (Ult 𝔄 F) n) (f : finitary (Π i, 𝔄 i) n → φ)
  (h : ∀ v₁ v₂ : finitary (Π i, 𝔄 i) n, (∀ n, (v₁ n) ~[F] (v₂ n)) → f v₁ = f v₂) : φ :=
quotient.lift_on_finitary v f h 

@[simp]
protected lemma lift_on_finitary_eq {φ} {n} (v : finitary (Π i, 𝔄 i) n) (f : finitary (Π i, 𝔄 i) n → φ)
  (h : ∀ v₁ v₂ : finitary (Π i, 𝔄 i) n, (∀ n, (v₁ n) ~[F] (v₂ n)) → f v₁ = f v₂) :
  fol.Ult.lift_on_finitary F (λ x, ⟦v x⟧*) f h = f v :=
quotient.lift_on_finitary_eq v f h

@[simp] lemma of_eq_of {u₁ u₂ : Π i, 𝔄 i} : (⟦u₁⟧* : Ult 𝔄 F) = ⟦u₂⟧* ↔ u₁ ~[F] u₂ :=
by simp[to_quotient, quotient.eq']

lemma equivs_mem {n} {v₁ v₂ : finitary (Π i, 𝔄 i) n} (h : ∀ (x : fin n), {i : I | v₁ x i = v₂ x i} ∈ F) :
  {i | (λ x, v₁ x i) = (λ x, v₂ x i)} ∈ F := 
begin
  induction n with n IH,
  { have : {i : I | (λ x, v₁ x i) = (λ x, v₂ x i)} = set.univ,
    { ext i, simp }, rw this, exact F.univ_sets },
  { have ss : {i | v₁ 0 i = v₂ 0 i} ∩ {i | (λ x, v₁.tail x i) = (λ x, v₂.tail x i)} ⊆ {i : I | (λ x, v₁ x i) = (λ x, v₂ x i)},
    { intros i hi, simp[finitary.tail] at*,
      funext x, refine fin.cases _ _ x,
      { exact hi.1 },
      { intros j, have := congr_fun hi.2 j, simp at this, exact this } },
    have : {i | v₁ 0 i = v₂ 0 i} ∩ {i | (λ x, v₁.tail x i) = (λ x, v₂.tail x i)} ∈ F,
      from (F.inter_sets (h _) (@IH v₁.tail v₂.tail (λ x, h _))),
    refine F.sets_of_superset this ss }
end

lemma fn_equiv {n} {v₁ v₂ : finitary (Π i, 𝔄 i) n} (h : ∀ x, v₁ x ~[F] v₂ x) (f : L.fn n) :
  (λ i, (𝔄 i).fn f (λ x, v₁ x i)) ~[F] (λ i, (𝔄 i).fn f (λ x, v₂ x i)) :=
begin
  simp[uequiv] at*,
  have : {i | (λ x, v₁ x i) = (λ x, v₂ x i)} ⊆ {i | (𝔄 i).fn f (λ x, v₁ x i) = (𝔄 i).fn f (λ x, v₂ x i)},
  { intros i hi, simp* at* },
  exact F.sets_of_superset (equivs_mem F h) this
end

lemma pr_equiv : ∀ {n} {v₁ v₂ : finitary (Π i, 𝔄 i) n} (h : ∀ x, v₁ x ~[F] v₂ x) (p : L.pr n),
  {i | (𝔄 i).pr p (λ x, v₁ x i)} ∈ F ↔ {i | (𝔄 i).pr p (λ x, v₂ x i)} ∈ F :=
begin
  suffices : ∀ {n} {v₁ v₂ : finitary (Π i, 𝔄 i) n} (h : ∀ x, v₁ x ~[F] v₂ x) (p : L.pr n),
  {i | (𝔄 i).pr p (λ x, v₁ x i)} ∈ F → {i | (𝔄 i).pr p (λ x, v₂ x i)} ∈ F,
  { intros n v₁ v₂ eqn p, refine ⟨this eqn p, this (λ x, uequiv_symm _ (eqn x)) p⟩ },
  intros n v₁ v₂ eqn p h,
  have : {i | (𝔄 i).pr p (λ x, v₁ x i)} ∩ {i | (λ x, v₁ x i) = (λ x, v₂ x i)} ⊆ {i | (𝔄 i).pr p (λ x, v₂ x i)},
  { intros i hi, simp* at*, simp[←hi.2], exact hi.1 },
  refine F.sets_of_superset (F.inter_sets h (equivs_mem _ eqn)) this
end

def product_fn (k) (f : L.fn k) : finitary (Ult 𝔄 F) k → Ult 𝔄 F :=
λ v, fol.Ult.lift_on_finitary F v (λ v, (⟦λ i, (𝔄 i).fn f (λ x, v x i)⟧* : Ult 𝔄 F)) $ λ u₁ u₂ eqn,
by { simp, exact fn_equiv F eqn f }

def product_pr (n) (p : L.pr n) : finitary (Ult 𝔄 F) n → Prop :=
λ v, fol.Ult.lift_on_finitary F v (λ v, {i | (𝔄 i).pr p (λ x, v x i)} ∈ F) $ λ u₁ u₂ eqn,
by { simp, exact pr_equiv F eqn p }

@[reducible] def product (𝔄 : I → nonempty_Structure L) (F : ultrafilter I) : nonempty_Structure L :=
{ dom := Ult 𝔄 F,
  fn := product_fn F,
  pr := product_pr F,
  dom_inhabited := Ult.inhabited F }

variables {F}
open subformula

lemma Structure_fn_eq {n} (f : L.fn n) : (product 𝔄 F).fn f = product_fn F _ f := rfl

lemma Structure_pr_eq {n} (r : L.pr n) : (product 𝔄 F).pr r = product_pr F _ r := rfl

variables (Φ : Π i, μ → 𝔄 i) (e : Π i, fin n → 𝔄 i)

lemma val_subterm (t : subterm L μ n) :
  subterm.val (product 𝔄 F : Structure L) (λ x, ⟦λ i, Φ i x⟧*) (λ x, ⟦λ i, e i x⟧*) t = ⟦λ i, subterm.val (𝔄 i) (Φ i) (e i) t⟧* :=
by induction t; simp[Structure_fn_eq, product_fn, *]

private lemma concat_to_quo (u : Π i, 𝔄 i) :
  ((⟦u⟧* : Ult 𝔄 F) *> λ x, ⟦λ i, e i x⟧*) = λ x, ⟦λ i, (u i *> e i) x⟧* :=
by ext x; refine fin.cases _ _ x; simp

theorem subval_subformula : ∀ {n} (e : Π i, fin n → 𝔄 i) (p : subformula L μ n),
  subval (product 𝔄 F : Structure L) (λ x, ⟦λ i, Φ i x⟧*) (λ x, ⟦λ i, e i x⟧*) p ↔ {i | subval (𝔄 i : Structure L) (Φ i) (e i) p} ∈ F
| n e verum          := by simp[top_eq]; exact F.univ_sets
| n e (relation r v) := by simp[Structure_pr_eq, product_pr, val_subterm, (∘)]
| n e (imply p q)    :=
    by simp[imply_eq, subval_subformula _ p, subval_subformula _ q, decidable.imp_iff_not_or,
      ←ultrafilter.compl_mem_iff_not_mem]; exact ultrafilter.union_mem_iff.symm
| n e (neg p)        := by simp[neg_eq, subval_subformula _ p]; exact ultrafilter.compl_mem_iff_not_mem.symm
| n e (fal p)        :=
    begin
      simp[fal_eq],
      let e' := λ (u : Π i, 𝔄 i), (λ i, u i *> e i),
      calc (∀ u : product 𝔄 F, subval (product 𝔄 F : Structure L) (λ x, ⟦λ i, Φ i x⟧*) (u *> λ x, ⟦λ i, e i x⟧*) p)
          ↔ (∀ u : Π i, 𝔄 i, subval (product 𝔄 F : Structure L) (λ x, ⟦λ i, Φ i x⟧*) (λ x, ⟦λ i, e' u i x⟧*) p)
      : by { split,
             { intros h u, simpa[e', concat_to_quo] using h ⟦u⟧* },
             { intros h u, induction u using fol.Ult.ind_on, simpa[concat_to_quo] using h u } }
      ... ↔ ∀ u : Π i, 𝔄 i, {i | subval (𝔄 i : Structure L) (Φ i) (e' u i) p} ∈ F
      : by { exact forall_congr (λ u, subval_subformula (e' u) p) }
      ... ↔ {i : I | ∀ (x : 𝔄 i), subval (𝔄 i : Structure L) (Φ i) (x *> e i) p} ∈ F
      : by { simp[e'], split,
            { intros h,
              let u : Π i, 𝔄 i := λ i, classical.epsilon (λ u, ¬subval ↑(𝔄 i) (Φ i) (u *> e i) p),
              refine F.sets_of_superset (h u) _,
              { intros i, simp, intros hi, by_contradiction A, simp at A,
                have : ¬subval ↑(𝔄 i) (Φ i) (u i *> e i) p,
                from classical.epsilon_spec_aux _ _ A,
                contradiction } },
            { intros h u, refine filter.mem_of_superset h (by intros i hi; exact hi (u i)) } }
    end

-- Łoś's theorem
theorem fundamental_param (p : formula L μ) (Φ : ∀ i, μ → 𝔄 i) :
  val (product 𝔄 F : Structure L) (λ x, ⟦λ i, Φ i x⟧*) p ↔ {i | val (𝔄 i : Structure L) (Φ i) p} ∈ F :=
by have := @subval_subformula L _ _ _ F _ Φ _ (λ i, fin.nil) p; exact cast (by congr) this

theorem fundamental {σ : sentence L} :
  product 𝔄 F ⊧ σ ↔ {i | 𝔄 i ⊧ σ} ∈ F :=
by have := @fundamental_param L _ _ _ F 𝔄 σ (λ i, fin.nil); simp[nonempty_Structure.sentence_models_def];
   exact cast (by congr) this

end Ult
end fol

namespace fol
variables {L : language.{u}} 

def finTheory (T : Theory L) := {s : finset (sentence L) // ↑s ⊆ T}

variables {T : Theory L}

def finTheory.empty {T : Theory L} : finTheory T := ⟨∅, by simp⟩
instance : inhabited (finTheory T) := ⟨⟨∅, by simp⟩⟩

noncomputable def finTheory.insert (P : finTheory T) {σ : sentence L} (h : σ ∈ T) : finTheory T :=
⟨insert σ P.val, λ x hx,  by { simp at hx, cases hx, simp[hx, h], refine P.property hx }⟩

@[simp] lemma finTheory.insert_val (P : finTheory T) {σ : sentence L} (h : σ ∈ T) :
  (P.insert h).val = insert σ P.val := rfl

instance : has_coe (finTheory T) (Theory L) := ⟨λ s, {p | p ∈ s.val}⟩

namespace compactness
open nonempty_Structure

variables (𝔄 : finTheory T → nonempty_Structure L) 

def formdomain (p : sentence L) : set (finTheory T) := {i | 𝔄 i ⊧ p}

def F : set (set (finTheory T)) := {x | ∃ p, T p ∧ x = formdomain 𝔄 p}

private lemma finite_intersection_lmm (nonempty : ∃ p, T p) (H : ∀ (i : finTheory T) p, p ∈ i.val → 𝔄 i ⊧ p) :
  ∀ S : finset (set (finTheory T)), (↑S : set (set (finTheory T))) ⊆ F 𝔄 →
  ∃ P : finTheory T,
  (∀ p, p ∈ P.val → formdomain 𝔄 p ∈ S) ∧ (∀ S', S' ∈ S → ∃ p, p ∈ P.val ∧ S' = formdomain 𝔄 p) :=
begin
  intros S, induction S using finset.induction with i S i_fresh IH,
  { intros _, simp[set.nonempty], rcases nonempty with ⟨p₀, hyp_p₀⟩,
    refine ⟨⟨∅, by simp⟩, _⟩, unfold_coes, simp },
  { intros h, simp at*,
    have lmm₁ : ↑S ⊆ F 𝔄, from set.subset.trans (set.subset_insert _ _) h,
    have : ∃ (P : finTheory T),
      (∀ p, p ∈ ↑P → formdomain 𝔄 p ∈ S) ∧ (∀ S', S' ∈ S → ∃ p, p ∈ ↑P ∧ S' = formdomain 𝔄 p),
    from IH lmm₁, rcases this with ⟨P, IH₁, IH₂⟩,
    have : ∃ p, T p ∧ i = formdomain 𝔄 p, from h (set.mem_insert i ↑S),
    rcases this with ⟨p, hyp_p, rfl⟩,
    refine ⟨P.insert hyp_p, _, _, _⟩; unfold_coes; simp,
    { refine λ q hyp_q, or.inr (IH₁ _ hyp_q) },
    { refine ⟨p, or.inl rfl, rfl⟩ },
    { intros S' hyp_S',
      have : ∃ p, p ∈ ↑P ∧ S' = formdomain 𝔄 p, from IH₂ _ hyp_S', rcases this with ⟨p, hyp, rfl⟩,
      refine ⟨p, or.inr hyp, rfl⟩ } }
end

theorem finite_intersection (h : ∃ p, T p) (H : ∀ (i : finTheory T) p, p ∈ i.val → 𝔄 i ⊧ p) :
  ∀ S : finset (set (finTheory T)), 
  (↑S : set (set (finTheory T))) ⊆ F 𝔄 → (⋂₀ (↑S : set (set (finTheory T)))).nonempty :=
begin
  intros S hS, have := finite_intersection_lmm _ h H S hS, rcases this with ⟨P, hyp⟩,
  refine ⟨P, λ S' hS', _⟩, 
  have := hyp.2 S' hS', rcases this with ⟨p, hyp_p, rfl⟩, simp[formdomain] at*,
  refine H _ _ hyp_p
end

theorem ultrafilter_exists (h : ∃ p, p ∈ T) (H : ∀ (i : finTheory T) p, p ∈ i.val → 𝔄 i ⊧ p) :
  ∃ U : ultrafilter (finTheory T), F 𝔄 ⊆ U.to_filter.sets :=
ultrafilter.exists_ultrafilter_of_finite_inter_nonempty _ (finite_intersection _ h H)

theorem compact (T : Theory L) :
  Satisfiable T ↔ ∀ S : finset (sentence L), ↑S ⊆ T → Satisfiable (S : Theory L) :=
  ⟨by { intros H S hyp_S, rcases H with ⟨𝔄, hyp⟩,
        refine ⟨𝔄, λ p h, hyp (hyp_S h)⟩ },
   by { suffices : (∀ S : finTheory T, Satisfiable (↑S : Theory L)) → Satisfiable T,
        { intros h, refine this (λ S, _),
          rcases h S.val S.property with ⟨𝔄, hyp_𝔄⟩, refine ⟨𝔄, hyp_𝔄⟩ },
    intros H, by_cases C : T = ∅,
        { rcases C with rfl, refine ⟨default, by intros p; simp⟩ },
        { have ex : ∃ p, p ∈ T, { by_contra, simp at*, refine C _, { ext x, simp, refine h _ } }, 
          have : ∃ (𝔄 : finTheory T → nonempty_Structure L), ∀ (i : finTheory T) p, p ∈ i.val → 𝔄 i ⊧ p,
          from classical.skolem.mp H, rcases this with ⟨𝔄, hyp_𝔄⟩,
          have := @ultrafilter_exists _ _ 𝔄 ex hyp_𝔄, rcases this with ⟨U, hyp_U⟩,
          refine ⟨Ult.product 𝔄 U, _⟩, intros p hyp_p, rw Ult.fundamental,
          have : {i | 𝔄 i ⊧ p} ∈ F 𝔄, { refine ⟨p, hyp_p, rfl⟩ },
          exact hyp_U this } }⟩

end compactness

end fol
