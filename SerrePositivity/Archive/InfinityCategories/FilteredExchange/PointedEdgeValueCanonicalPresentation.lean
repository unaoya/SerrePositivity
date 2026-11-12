module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedSpaceMorphismEdgeValueIso
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoPrecompEndpointTransport
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoWhiskerCancellation

/-!
概要：元の実辺の両端表示を、同じ canonical 区間の指定比較の値へ戻す。
方針：元の表示等式と前合成の合成則を使う。
規約：元の実辺・指定比較を保持。使われ方：raw 長辺の指定値比較の二因子の回収。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits

/-- 元の実辺の値比較の初期値前合成を、同じ canonical 値比較の同じ前合成へ戻す。 -/
lemma pointedSpaceMorphismEdgeValueIso_precomp_heq_canonical
    {K L : KanObject.{u}} (f : K ⟶ L) {C : SSet.{u + 1}}
    {x y : SpaceInfinity.{u} _⦋0⦌} (e : SSet.Edge x y)
    (hx : x = spaceInfinityVertex K) (hy : y = spaceInfinityVertex L)
    (he : e.edge = (pointedRightMorphismEdge f).edge)
    (q : C ⟶ vertexFiber pointedSpaceProjection x) :
    HEq ((pointedSpaceMorphismEdgeValueIso f e hx hy he).precomp q)
      ((pointedValueMorphismIntervalIso f).precomp
        (q ≫ eqToHom (congrArg (vertexFiber pointedSpaceProjection) hx))) := by
  unfold pointedSpaceMorphismEdgeValueIso
  exact (functorIsoOfEq_precomp_heq _ _ _ q).trans
    (heq_of_eq (functorIso_precomp_precomp (pointedValueMorphismIntervalIso f) _ q))

end SerrePositivity.InfinityCategories.F2
