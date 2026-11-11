module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedFiberValueTo
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FullyFaithfulVertexIsoImage
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerAlgebra
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoTransport

/-!
概要：指定頂点等式で固定した値への射影は、全関手空間で同値となり指定同型を反映する。
方針：同じ頂点等式だけを消去し、元の pointed 値同値の後合成を使う。
規約：値射影・指定同型を選び直さない。使われ方：raw fiber 二面比較の指定値の反映。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 指定頂点等式の先の固定値への元の射影は、同じ pointed 値同値の射。 -/
lemma pointedFiberValueTo_isQCatEquivalence {z z' : SpaceInfinity.{u} _⦋0⦌} (hz : z = z') :
    IsQCatEquivalence (pointedFiberValueTo hz) := by
  cases hz
  exact (pointedSpaceFiberValueEquivalence z).isQCatEquivalence

/-- 同じ指定値への射影による任意の始域の後合成は、全関手空間の同値。 -/
lemma pointedFiberValueTo_postcompose_isQCatEquivalence (C : SSet.{u + 1})
    {z z' : SpaceInfinity.{u} _⦋0⦌} (hz : z = z') :
    IsQCatEquivalence ((ihom C).map (pointedFiberValueTo hz)) :=
  (pointedFiberValueTo_isQCatEquivalence hz).postcompose C

/-- 固定値への全射影は、同じ実両端間の元の指定関手同型の等式を反映する。 -/
lemma pointedFiberValueTo_postcompose_iso_injective (C : SSet.{u + 1})
    {z z' : SpaceInfinity.{u} _⦋0⦌} (hz : z = z')
    {x y : ((ihom C).obj (vertexFiber pointedSpaceProjection z)) _⦋0⦌} :
    Function.Injective (fun e : VertexIso x y =>
      VertexIso.map e ((ihom C).map (pointedFiberValueTo hz))) := by
  exact vertexIso_map_injective
    (pointedFiberValueTo_postcompose_isQCatEquivalence C hz).isFullyFaithful

/-- 同じ固定値への元の後合成は、同じ実両端間の指定関手同型の値を反映する。 -/
lemma pointedFiberValueTo_postcompose_functorIso_injective (C : SSet.{u + 1})
    {z z' : SpaceInfinity.{u} _⦋0⦌} (hz : z = z')
    {f g : C ⟶ vertexFiber pointedSpaceProjection z} :
    Function.Injective (fun e : FunctorIso f g => e.postcomp (pointedFiberValueTo hz)) := by
  intro e d h
  apply pointedFiberValueTo_postcompose_iso_injective C hz
  simpa only [functorIso_postcomp_eq_mapIso, VertexIso.map, hoFunctor_map,
    Functor.toCatHom_toFunctor] using h

/-- 元の後合成の実両端だけを明示等式で揃えても、同じ指定値の等式を反映できる。 -/
lemma pointedFiberValueTo_postcompose_transport_injective (C : SSet.{u + 1})
    {z z' : SpaceInfinity.{u} _⦋0⦌} (hz : z = z')
    {f g : C ⟶ vertexFiber pointedSpaceProjection z}
    {f' g' : C ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (spaceInfinityObject z').obj}
    (hf : f ≫ pointedFiberValueTo hz = f') (hg : g ≫ pointedFiberValueTo hz = g') :
    Function.Injective (fun e : FunctorIso f g =>
      functorIsoOfEq (e.postcomp (pointedFiberValueTo hz)) hf hg) := by
  subst f' g'
  intro e d h
  apply pointedFiberValueTo_postcompose_functorIso_injective C hz
  exact h

end SerrePositivity.InfinityCategories.F2
