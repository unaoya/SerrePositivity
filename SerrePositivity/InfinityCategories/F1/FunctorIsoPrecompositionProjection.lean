module

public import SerrePositivity.InfinityCategories.F1.FunctorIsoEndpointProjection
public import SerrePositivity.InfinityCategories.F2.FunctorIsoWhiskerCancellation

/-!
概要：前合成で回収される指定同型は、任意の元の作用でさらに前合成しても回収される。
方針：同型の前合成の合成則と同じ回収等式への作用を組み合わせる。
規約：指定された同型と端点正規化の値を保持する。
使われ方：第二面の分解比較を元の大域 Hom 作用へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 前合成による指定値の回収とさらに前合成した端点正規化を合成する。 -/
lemma functorIso_precomp_of_projection_heq {H X Y K : SSet.{u}}
    {F G : X ⟶ Y} (e : FunctorIso F G) (p : H ⟶ X)
    (d : FunctorIso (p ≫ F) (p ≫ G)) (hp : e.precomp p = d)
    {f g : H ⟶ Y} (d₀ : FunctorIso f g) (r : K ⟶ H)
    (hd : HEq (d.precomp r) (d₀.precomp r)) :
    HEq (e.precomp (r ≫ p)) (d₀.precomp r) := by
  have hc := F2.functorIso_precomp_precomp e p r
  have hh := congrArg (fun v ↦ FunctorIso.precomp v r) hp
  exact (heq_of_eq hc.symm).trans ((heq_of_eq hh).trans hd)

/-- 前合成の端点正規化後にさらに前合成すると、同じ合成した作用を回収する。 -/
lemma functorIsoOfEq_precomp_precomp_heq {H X Y K : SSet.{u}}
    {f g : X ⟶ Y} (e : FunctorIso f g) (p : H ⟶ X)
    {f' g' : H ⟶ Y} (hf : p ≫ f = f') (hg : p ≫ g = g') (r : K ⟶ H) :
    HEq ((F2.functorIsoOfEq (e.precomp p) hf hg).precomp r) (e.precomp (r ≫ p)) := by
  exact (functorIsoOfEq_precomp_heq (e.precomp p) hf hg r).trans
    (heq_of_eq (F2.functorIso_precomp_precomp e p r))

/-- 後合成の端点正規化を前合成すると、元の前後合成された指定値を回収する。 -/
lemma functorIsoOfEq_postcomp_precomp_heq {H X Y K : SSet.{u}}
    {f g : H ⟶ X} (e : FunctorIso f g) (p : X ⟶ Y)
    {f' g' : H ⟶ Y} (hf : f ≫ p = f') (hg : g ≫ p = g') (r : K ⟶ H) :
    HEq ((F2.functorIsoOfEq (e.postcomp p) hf hg).precomp r)
      ((e.precomp r).postcomp p) := by
  exact (functorIsoOfEq_precomp_heq (e.postcomp p) hf hg r).trans
    (heq_of_eq (F2.functorIso_precomp_postcomp e r p).symm)

/-- 前合成した同型の端点正規化が指定値なら、前後合成の交換後も同じ指定値。 -/
lemma functorIsoOfEq_precomp_postcomp_heq_of_eq {H X Y K : SSet.{u}}
    {f g : H ⟶ X} (e : FunctorIso f g) (r : K ⟶ H)
    {f' g' : K ⟶ X} (hf : r ≫ f = f') (hg : r ≫ g = g')
    (d : FunctorIso f' g') (hd : F2.functorIsoOfEq (e.precomp r) hf hg = d) (p : X ⟶ Y) :
    HEq ((e.postcomp p).precomp r) (d.postcomp p) := by
  exact (heq_of_eq (F2.functorIso_precomp_postcomp e r p).symm).trans
    (functorIsoOfEq_postcomp_heq_of_eq (e.precomp r) hf hg d hd p).symm

end SerrePositivity.InfinityCategories
