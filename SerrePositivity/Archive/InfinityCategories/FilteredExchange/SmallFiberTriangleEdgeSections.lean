module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SmallFiberEdgeSectionsBase
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SmallFiberPointedPrismFaces
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedStrictConeFamily

/-!
概要：元の局所全三角形の図式側の切断族を、実際の二 fiber 作用による切断族へ同定する。
方針：底の表示変更を uncurry で消し、同じ第二面の全 prism の厳密な式を使う。
規約：全族と図式辺の等式を保持。使われ方：native 切断の指定比較の終点の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (x : (leftUnstraighteningTransformationSpace F G) _⦋0⦌)
  (y : (leftUnstraighteningTransformationSpace G J) _⦋0⦌)
  (T : CoherentTransformationVertexTriangle F G J x y) (b : B _⦋0⦌)
local notation "a" => coherentNativeTriangleFiberParameters F b
local notation "H" => coherentSmallFiberPointedTriangle F G J x y T b

/-- 図式側の同じ全切断族は、元の第一 fiber 射で代入した第二作用の切断族そのもの。 -/
lemma coherentSmallFiberTriangleDiagramSections_eq
    (D : (Δ[2] : SSet.{u + 1}) ⟶ SpaceInfinity.{u})
    (hH : H ≫ pointedSpaceProjection = fst Δ[2] a ≫ D)
    (e : (Δ[1] : SSet.{u + 1}) ⟶ SpaceInfinity.{u})
    (he : e = coherentTransformationPointEdge G J y b) (hj : stdSimplex.δ (0 : Fin 3) ≫ D = e) :
    pointedTriangleFaceSections D H hH 0 ≫
        eqToHom (congrArg (relativeFunctorSpace pointedSpaceProjection) hj) =
      (SSet.uliftFunctor.{u + 1, u}).map
        (vertexFiberMap (smallLeftUnstraighteningProjection F)
          (smallLeftUnstraighteningProjection G) (coherentTransformationTotalMap F G x)
          (coherentTransformationTotalMap_projection F G x) b) ≫
        coherentSmallFiberEdgeSectionsOfEq G J y b e he := by
  apply relativeFunctorUncurry_injective pointedSpaceProjection e
  rw [HomotopyLimits.relativeFunctorUncurry_eqToHom pointedSpaceProjection hj,
    pointedTriangleFaceSections_uncurry, relativeFunctorUncurry_naturality,
    coherentSmallFiberEdgeSectionsOfEq_uncurry]
  exact coherentSmallFiberPointedTriangle_second_prism F G J x y T b

end SerrePositivity.InfinityCategories.F2
