module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SmallRelativeVertexForgetImage
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SmallTriangleRelativePresentation
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentTransformationTriangleSmall
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorTriangleSmallTotalAction
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorTriangleTotalAction

/-!
概要：元の小さい三角形比較を、同じ全空間の指定三角形比較の縮小へ同定する。
方針：同じ相対比較の終点表示だけを除き、縮小と忘却の全族の整合を使う。
規約：元の三辺・全三角形・指定値を保持。使われ方：模型三角形と単位後の三角形の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}} [Quasicategory B]
  (F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (x : (leftUnstraighteningTransformationSpace F G) _⦋0⦌)
  (y : (leftUnstraighteningTransformationSpace G J) _⦋0⦌)
  (T : CoherentTransformationVertexTriangle F G J x y)

/-- 小さい指定三角形比較は、元の全空間の同じ指定三角形比較を縮小した値に一致する。 -/
lemma coherentTransformationTriangleSmallIso_heq_smallFunctor :
    HEq (coherentTransformationTriangleSmallIso F G J x y T)
      (smallUnstraighteningFunctorIso F J (unstraighteningTriangleVertexIso F G J x y T.diagonal
        T.diagram T.first T.second T.long)) := by
  have hm := vertexIso_map_heq_of_heq (coherentTransformationTriangleRelativeIso F G J x y T)
    (smallUnstraighteningRelativeVertexIso F J
      (leftUnstraighteningMappingVertexMap F J T.diagonal).property
      (coherentTransformationMappingComposite_projection F G J x y)
      (unstraighteningTriangleRelativeVertexIso F G J x y T.diagonal
        T.diagram T.first T.second T.long))
    rfl (coherentTransformationComposite_relativeVertex F G J x y).symm
    (coherentTriangleRelativeIso_heq_small F G J x y T)
    (vertexFiberι ((ihom (smallLeftUnstraightening F)).map (smallLeftUnstraighteningProjection J))
      (functorVertex (smallLeftUnstraighteningProjection F)))
  exact hm.trans (smallRelativeVertexIso_forget_heq_smallFunctor F J _ _ _)

/-- 元の全関手三角形の小さい比較は、同じ全空間作用比較の縮小と値まで一致する。 -/
lemma functorTriangleSmallTotalActionIso_heq_smallFunctor
    {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {c : SSet.Homotopy F J}
    (S : FunctorCompositionTriangle a b c) :
    HEq (functorTriangleSmallTotalActionIso S)
      (smallUnstraighteningFunctorIso F J (functorTriangleTotalActionIso S)) := by
  exact coherentTransformationTriangleSmallIso_heq_smallFunctor F G J
    (coherentVertexOfHomotopy a) (coherentVertexOfHomotopy b) (coherentTriangleOfFunctorTriangle S)

end SerrePositivity.InfinityCategories.F2
