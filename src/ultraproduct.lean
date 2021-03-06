import deduction semantics lindenbaum order.filter.ultrafilter
open encodable

universes u v

namespace fopl
variables {L : language.{u}} {I : Type u} [inhabited I] (F : ultrafilter I) {π : I β model L}

def uequiv : (Ξ  i, |π i|) β (Ξ  i, |π i|) β Prop :=
Ξ» uβ uβ, {i | uβ i = uβ i} β F

notation u` ~[`:80 F`] `v:80 := uequiv F u v

@[simp] lemma uequiv_refl (u : Ξ  i, |π i|) : u ~[F] u :=
by { simp[uequiv], exact F.univ_sets }

lemma uequiv_symm {uβ uβ : Ξ  i, |π i|} : uβ ~[F] uβ β uβ ~[F] uβ :=
by { simp[uequiv], have : {i | uβ i = uβ i} = {i | uβ i = uβ i}, { ext, simp, exact eq_comm }, simp[this] }

lemma uequiv_trans {uβ uβ uβ : Ξ  i, |π i|} : uβ ~[F] uβ β uβ ~[F] uβ β uβ ~[F] uβ :=
by { simp[uequiv], intros hβ hβ,
     have : {i | uβ i = uβ i} β© {i | uβ i = uβ i} β {i | uβ i = uβ i},
     { intros i hi, simp* at* },
     exact F.sets_of_superset (F.inter_sets hβ hβ) this }

theorem uequiv_equivalence : equivalence (@uequiv L I _ F π) :=
β¨uequiv_refl F, Ξ» _ _ , uequiv_symm F, Ξ» _ _ _, uequiv_trans Fβ©


@[reducible, simp, instance]
def ult (π : I β model L) (F : ultrafilter I) : setoid (Ξ  i, |π i|) := β¨@uequiv L I _ F π, uequiv_equivalence Fβ©

def Ult (π : I β model L) (F : ultrafilter I) : Type* :=
quotient (ult π F: setoid (Ξ  i, |π i|))

def to_quotient {π : I β model L} {F : ultrafilter I} (u : Ξ  i, |π i|) : Ult π F := quotient.mk' u

notation `β¦`u`β§*` :max := to_quotient u

instance : inhabited (Ult π F) := β¨β¦Ξ» i, defaultβ§*β©

namespace Ult

local infix `β`:80 := (@setoid.vec_r _ (ult π F) _)

@[elab_as_eliminator]
protected lemma ind_on {C : Ult π F β Prop} (u : Ult π F)
  (h : β u : Ξ  i, |π i|, C β¦uβ§*) : C u :=
quotient.induction_on' u h

@[elab_as_eliminator, reducible]
protected def lift_on {Ο} (d : Ult π F) (f : (Ξ  i, |π i|) β Ο)
  (h : β (v u : Ξ  i, |π i|), v ~[F] u β f v = f u) : Ο :=
quotient.lift_on' d f h

@[simp]
protected lemma lift_on_eq {Ο} (uβ : Ξ  i, |π i|) (f : (Ξ  i, |π i|) β Ο)
  (h : β v u, v ~[F] u β f v = f u) : fopl.Ult.lift_on F β¦uββ§* f h = f uβ := rfl

@[elab_as_eliminator, reducible, simp]
protected def lift_onβ {Ο} (uβ uβ : Ult π F) (f : (Ξ  i, |π i|) β (Ξ  i, |π i|) β Ο)
  (h : β uβ uβ vβ vβ, uβ ~[F] vβ β uβ ~[F] vβ β f uβ uβ = f vβ vβ) : Ο :=
quotient.lift_onβ' uβ uβ f h

@[simp]
protected lemma lift_onβ_eq {Ο} (uβ uβ : Ξ  i, |π i|) (f : (Ξ  i, |π i|) β (Ξ  i, |π i|) β Ο)
  (h : β tβ tβ uβ uβ, (tβ ~[F] uβ) β (tβ ~[F] uβ) β f tβ tβ = f uβ uβ) :
  fopl.Ult.lift_onβ F β¦uββ§* β¦uββ§* f h = f uβ uβ := rfl

@[elab_as_eliminator, reducible]
protected def lift_on_finitary {Ο} {n : β} (v : finitary (Ult π F) n) (f : finitary (Ξ  i, |π i|) n β Ο)
  (h : β vβ vβ : finitary (Ξ  i, |π i|) n, (β n, (vβ n) ~[F] (vβ n)) β f vβ = f vβ) : Ο :=
quotient.lift_on_finitary v f h 

@[simp]
protected lemma lift_on_finitary_eq {Ο} {n} (v : finitary (Ξ  i, |π i|) n) (f : finitary (Ξ  i, |π i|) n β Ο)
  (h : β vβ vβ : finitary (Ξ  i, |π i|) n, (β n, (vβ n) ~[F] (vβ n)) β f vβ = f vβ) :
  fopl.Ult.lift_on_finitary F (Ξ» x, β¦v xβ§*) f h = f v :=
quotient.lift_on_finitary_eq v f h

@[simp] lemma of_eq_of {uβ uβ : Ξ  i, |π i|} : (β¦uββ§* : Ult π F) = β¦uββ§* β uβ ~[F] uβ :=
by simp[to_quotient, quotient.eq']

lemma equivs_mem {n} {vβ vβ : finitary (Ξ  i, |π i|) n} (h : β (x : fin n), {i : I | vβ x i = vβ x i} β F) :
  {i | (Ξ» x, vβ x i) = (Ξ» x, vβ x i)} β F := 
begin
  induction n with n IH,
  { have : {i : I | (Ξ» x, vβ x i) = (Ξ» x, vβ x i)} = set.univ,
    { ext i, simp }, rw this, exact F.univ_sets },
  { have ss : {i | vβ 0 i = vβ 0 i} β© {i | (Ξ» x, vβ.tail x i) = (Ξ» x, vβ.tail x i)} β {i : I | (Ξ» x, vβ x i) = (Ξ» x, vβ x i)},
    { intros i hi, simp[finitary.tail] at*,
      funext x, refine fin.cases _ _ x,
      { exact hi.1 },
      { intros j, have := congr_fun hi.2 j, simp at this, exact this } },
    have : {i | vβ 0 i = vβ 0 i} β© {i | (Ξ» x, vβ.tail x i) = (Ξ» x, vβ.tail x i)} β F,
      from (F.inter_sets (h _) (@IH vβ.tail vβ.tail (Ξ» x, h _))),
    refine F.sets_of_superset this ss }
end

lemma fn_equiv {n} {vβ vβ : finitary (Ξ  i, |π i|) n} (h : β x, vβ x ~[F] vβ x) (f : L.fn n) :
  (Ξ» i, (π i).fn f (Ξ» x, vβ x i)) ~[F] (Ξ» i, (π i).fn f (Ξ» x, vβ x i)) :=
begin
  simp[uequiv] at*,
  have : {i | (Ξ» x, vβ x i) = (Ξ» x, vβ x i)} β {i | (π i).fn f (Ξ» x, vβ x i) = (π i).fn f (Ξ» x, vβ x i)},
  { intros i hi, simp* at* },
  exact F.sets_of_superset (equivs_mem F h) this
end

lemma pr_equiv : β {n} {vβ vβ : finitary (Ξ  i, |π i|) n} (h : β x, vβ x ~[F] vβ x) (p : L.pr n),
  {i | (π i).pr p (Ξ» x, vβ x i)} β F β {i | (π i).pr p (Ξ» x, vβ x i)} β F :=
begin
  suffices : β {n} {vβ vβ : finitary (Ξ  i, |π i|) n} (h : β x, vβ x ~[F] vβ x) (p : L.pr n),
  {i | (π i).pr p (Ξ» x, vβ x i)} β F β {i | (π i).pr p (Ξ» x, vβ x i)} β F,
  { intros n vβ vβ eqn p, refine β¨this eqn p, this (Ξ» x, uequiv_symm _ (eqn x)) pβ© },
  intros n vβ vβ eqn p h,
  have : {i | (π i).pr p (Ξ» x, vβ x i)} β© {i | (Ξ» x, vβ x i) = (Ξ» x, vβ x i)} β {i | (π i).pr p (Ξ» x, vβ x i)},
  { intros i hi, simp* at*, simp[βhi.2], exact hi.1 },
  refine F.sets_of_superset (F.inter_sets h (equivs_mem _ eqn)) this
end

def product_fn (n) (f : L.fn n) : finitary (Ult π F) n β Ult π F :=
Ξ» v, fopl.Ult.lift_on_finitary F v (Ξ» v, (β¦Ξ» i, (π i).fn f (Ξ» x, v x i)β§* : Ult π F)) $ Ξ» uβ uβ eqn,
by { simp, exact fn_equiv F eqn f }

def product_pr (n) (p : L.pr n) : finitary (Ult π F) n β Prop :=
Ξ» v, fopl.Ult.lift_on_finitary F v (Ξ» v, {i | (π i).pr p (Ξ» x, v x i)} β F) $ Ξ» uβ uβ eqn,
by { simp, exact pr_equiv F eqn p }

def product (π : I β model L) (F : ultrafilter I) : model L := β¨Ult π F, β¨defaultβ©, product_fn F, product_pr Fβ©
notation `βΏ `π` β«½ `F:90 := product π F

variables {F}

@[simp] lemma ult_eq : Ult π F = |βΏ π β«½ F| := rfl

private lemma model_exists (p : formula L) {e : β i, β β |π i|} (h : {i | β u, π i β§[u β’ e i] p } β F) :
  β (u : Ξ  i, |π i|), {i | π i β§[(u i) β’ e i] p} β F :=
begin
  have : β i, β u, i β {i | β u, π i β§[u β’ e i] p} β π i β§[u β’ e i] p,
  { intros i, simp, by_cases C : i β {i | β u, π i β§[u β’ e i] p}; simp at C,
    { rcases C with β¨u, huβ©, refine β¨u, Ξ» v _, huβ© },
    { refine β¨default, Ξ» _ h, _β©, exfalso, refine C _ h } },
  rcases classical.skolem.mp this with β¨u, huβ©,
  refine β¨u, _β©, exact F.sets_of_superset h hu
end

lemma model_fn_eq {n} (f : L.fn n) : (βΏ π β«½ F).fn f = product_fn F _ f := rfl

lemma model_pr_eq {n} (r : L.pr n) : (βΏ π β«½ F).pr r = product_pr F _ r := rfl

lemma models_pr_iff_lmm : β (t : term L) (e : β i, β β |π i|),
  (@term.val _ (βΏ π β«½ F) (Ξ» n, β¦Ξ» i, e i nβ§*) t) = β¦Ξ» i, @term.val _ (π i) (Ξ» n, e i n) tβ§*
| (#n)                _ := by simp 
| (@term.app _ n f v) e :=
  by { simp[model_fn_eq, product_fn],
       let v' : finitary (Ξ  i, |π i|) n := Ξ» x i, (v x).val (π i) (e i),
       have : (Ξ» x, @term.val _ (βΏ π β«½ F) (Ξ» n, β¦(Ξ» i, e i n)β§*) (v x)) = Ξ» x, β¦v' xβ§*,
       { funext x, simp[v', models_pr_iff_lmm (v x)] },
       simp[this] }

lemma models_pr_iff {n} (r : L.pr n) (v : finitary (term L) n) (e : β i, β β |π i|) :
  (βΏ π β«½ F).pr r (Ξ» x, (v x).val (βΏ π β«½ F) (Ξ» n, β¦Ξ» i, e i nβ§*)) β {i | (π i).pr r (Ξ» x, (v x).val (π i) (e i))} β F :=
by simp[models_pr_iff_lmm, model_pr_eq, product_pr]

-- ΕoΕ's theorem
theorem fundamental_param : β (p : formula L) (e : β i, β β |π i|),
  βΏ π β«½ F β§[Ξ» n, β¦Ξ» i, e i nβ§*] p β {i | π i β§[e i] p} β F
| β€                 _ := by { simp, exact F.univ_sets }
| (formula.app p v) e := models_pr_iff p _ _
| (tβ β tβ)      e := by simp[models_pr_iff_lmm]; refl
| (p βΆ q)       e := by { simp[fundamental_param p, fundamental_param q],
    show {i | π i β§[e i] p} β F β {i | π i β§[e i] q} β F β {i | π i β§[e i] p β π i β§[e i] q} β F,
    split,
    { intros h, by_cases C : {i | π i β§[e i] p} β F,
      { have : {i | π i β§[e i] q} β {i | π i β§[e i] p β π i β§[e i] q}, { intros i hi, simp* at* },
        exact F.sets_of_superset (h C) this },
      { have : {i | π i β§[e i] p}αΆ β F, from ultrafilter.compl_mem_iff_not_mem.mpr C,
        have ss : {i | π i β§[e i] p}αΆ β {i | π i β§[e i] p β π i β§[e i] q},
        { intros i hi, simp* at* },
        exact F.sets_of_superset this ss } },
    { intros hβ hβ,
      have : {i | π i β§[e i] p} β© {i | π i β§[e i] p β π i β§[e i] q} β {i | π i β§[e i] q},
      { intros i hi, simp at*, refine hi.2 hi.1 },
      exact filter.mp_mem hβ hβ } }
| (β»p)          e := by { simp[fundamental_param p], exact ultrafilter.eventually_not.symm }
| (β p)          e := by { simp, 
    calc
      (β u, βΏ π β«½ F β§[u β’ Ξ» n, β¦Ξ» i, e i nβ§*] p)
          β (β (u : Ξ  i, |π i|), βΏ π β«½ F β§[Ξ» n, β¦Ξ» i, (Ξ» i, (u i) β’ (e i)) i nβ§*] p) :
        by { have eqn: β u, (β¦uβ§* β’ Ξ» n, β¦(Ξ» i, e i n)β§*) = (Ξ» n, β¦(Ξ» i, (u i) β’ e i $ n)β§* : β β |βΏ π β«½ F|),
             { intros i, funext x, cases x; simp[concat] }, simp, split,
             { intros h u, have := h β¦uβ§*, simp[eqn] at this, exact this },
             { intros h u, induction u using fopl.Ult.ind_on, simp[eqn, h] } }
      ... β (β (u : Ξ  i, |π i|), {i | π i β§[u i β’ e i] p} β F) :
        by { split, { intros h u, simp[βfundamental_param  p _, h] }, { intros h u, simp[fundamental_param  p _, h] } }
      ... β {i | β (u : |π i|), π i β§[u β’ e i] p} β F : 
        by { split,
             { contrapose, simp[βultrafilter.compl_mem_iff_not_mem, βset.compl_eq_compl, set.compl], intros h,
               show β (u : Ξ  i, |π i|), {i | Β¬π i β§[u i β’ e i] p} β F, from model_exists (β»p) h },
             { refine Ξ» h u, F.sets_of_superset h (Ξ» _ _ , by simp* at*) } } }

theorem fundamental {p : formula L} :
  βΏ π β«½ F β§ p β {i | π i β§ p} β F :=
begin
  calc
    βΏ π β«½ F β§ p β βΏ π β«½ F β§ nfal p p.arity : nfal_models_iff.symm
    ...         β {i | π i β§ nfal p p.arity} β F :
      by simpa[eval_is_sentence_iff _ (formula.nfal_is_sentence p)] using fundamental_param (nfal p p.arity) (Ξ» i n, default)
    ...         β {i | π i β§ p} β F :
      by { have : {i | π i β§ nfal p p.arity} = {i | π i β§ p},
           { ext i, simp, refine nfal_models_iff },
           simp[this] }
end

end Ult
end fopl

namespace fopl
variables {L : language.{u}} 

def fintheory (T : theory L) := {S : finset (formula L) // β {x}, x β S β x β T}

variables {T : theory L}

def fintheory.empty {T : theory L} : fintheory T := β¨β, by simpβ©
instance : inhabited (fintheory T) := β¨β¨β, by simpβ©β©

noncomputable def fintheory.insert (P : fintheory T) (p : formula L) (h : p β T) : fintheory T :=
β¨insert p P.val, Ξ» x hx,  by { simp at hx, cases hx, simp[hx, h], refine P.property hx }β©

@[simp] lemma fintheory.insert_val (P : fintheory T) (p : formula L) (h : T p) :
  (P.insert p h).val = insert p P.val := rfl

instance : has_coe (fintheory T) (set (formula L)) := β¨Ξ» S, {p | p β S.val}β©

namespace compactness

variables (π : fintheory T β model L) 

def formdomain (p : formula L) : set (fintheory T) := {i | π i β§ p}

def F : set (set (fintheory T)) := {x | β p, T p β§ x = formdomain π p}

private lemma finite_intersection_lmm (h : β p, T p) (H : β (i : fintheory T) p, p β i.val β π i β§ p) :
  β S : finset (set (fintheory T)), (βS : set (set (fintheory T))) β F π β
  β P : fintheory T,
  (β p, p β P.val β formdomain π p β S) β§ (β S', S' β S β β p, p β P.val β§ S' = formdomain π p) :=
begin
  intros S, induction S using finset.induction with i S i_fresh IH,
  { intros _, simp[set.nonempty], rcases h with β¨pβ, hyp_pββ©,
    refine β¨β¨β, by simpβ©, _β©, unfold_coes, simp },
  { intros h, simp at*,
    have lmmβ : βS β F π, from set.subset.trans (set.subset_insert _ _) h,
    have : β (P : fintheory T),
      (β p, p β βP β formdomain π p β S) β§ (β S', S' β S β β p, p β βP β§ S' = formdomain π p),
    from IH lmmβ, rcases this with β¨P, IHβ, IHββ©,
    have : β p, T p β§ i = formdomain π p, from h (set.mem_insert i βS),
    rcases this with β¨p, hyp_p, rflβ©,
    refine β¨P.insert p hyp_p, _, _, _β©; unfold_coes; simp,
    { refine Ξ» q hyp_q, or.inr (IHβ _ hyp_q) },
    { refine β¨p, or.inl rfl, rflβ© },
    { intros S' hyp_S',
      have : β p, p β βP β§ S' = formdomain π p, from IHβ _ hyp_S', rcases this with β¨p, hyp, rflβ©,
      refine β¨p, or.inr hyp, rflβ© } }
end

theorem finite_intersection (h : β p, T p) (H : β (i : fintheory T) p, p β i.val β π i β§ p) :
  β S : finset (set (fintheory T)), 
  (βS : set (set (fintheory T))) β F π β (ββ (βS : set (set (fintheory T)))).nonempty :=
begin
  intros S hS, have := finite_intersection_lmm _ h H S hS, rcases this with β¨P, hypβ©,
  refine β¨P, Ξ» S' hS', _β©, 
  have := hyp.2 S' hS', rcases this with β¨p, hyp_p, rflβ©, simp[formdomain] at*,
  refine H _ _ hyp_p
end

theorem ultrafilter_exists (h : β p, p β T) (H : β (i : fintheory T) p, p β i.val β π i β§ p) :
  β U : ultrafilter (fintheory T), F π β U.to_filter.sets :=
ultrafilter.exists_ultrafilter_of_finite_inter_nonempty _ (finite_intersection _ h H)

theorem compact (T : theory L) :
  (β π, π β§ββ T) β (β S : finset (formula L), (β {p}, p β S β p β T) β β π, π β§ββ {p | p β S}) :=
  β¨by { intros H S hyp_S, rcases H with β¨π, hypβ©,
        refine β¨π, Ξ» p h, hyp _ (hyp_S h)β© },
   by { suffices : (β S : fintheory T, β π, π β§ββ (βS : set (formula L))) β (β π, π β§ββ T),
        { intros h, refine this (Ξ» S, _),
          rcases h S.val S.property with β¨π, hyp_πβ©, refine β¨π, hyp_πβ© },
    intros H, by_cases C : T = β,
        { rcases C with rfl, refine empty_has_model },
        { have ex : β p, p β T, { by_contra, simp at*, refine C _, { ext x, simp, refine h _ } }, 
          have : β (π : fintheory T β model L), β (i : fintheory T) p, p β i.val β π i β§ p,
          from classical.skolem.mp H, rcases this with β¨π, hyp_πβ©,
          have := ultrafilter_exists _ ex hyp_π, rcases this with β¨U, hyp_Uβ©,
          use βΏ π β«½ U, intros p hyp_p, rw Ult.fundamental,
          have : {i | π i β§ p} β F π, { refine β¨p, hyp_p, rflβ© },
          exact hyp_U this } }β©

end compactness

end fopl
