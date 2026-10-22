module

public import SerrePositivity.InfinityCategories.F2.CoherentNativeModelComparisonTransport
public import SerrePositivity.InfinityCategories.F2.CoherentTriangleSmallFunctorComparison
public import SerrePositivity.InfinityCategories.F2.CoherentTotalTriangleNativeComparison

/-!
概要：元の模型三角形の指定比較を、同じ元の全空間三角形の単位後合成へ同定する。
方針：同じ小さい三角形比較の縮小表示を移し、宇宙往復と始域縮小を消去する。
規約：元の三角形・三辺・模型比較を保持。使われ方：a6 の単位交換式への代入。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}} [Quasicategory B]
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b d)

/-- 元の模型三角形の指定値は、元の全空間三角形を元の単位で後合成した同じ値。 -/
lemma coherentTotalTriangleNativeModelComparison_heq_large_unit :
    HEq (coherentTotalTriangleNativeModelComparison T)
      ((functorTriangleTotalActionIso T).postcomp (coherentLargeTotalUnit J)) := by
  have h := coherentTotalMapNativeModelComparison_heq_of_heq F J
    (functorTriangleSmallTotalActionIso T)
    (smallUnstraighteningFunctorIso F J (functorTriangleTotalActionIso T)) rfl
    (smallSimplicialMap_comp.{u, u + 1}
      (leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy a)).val
      (leftUnstraighteningMappingVertexMap G J (coherentVertexOfHomotopy b)).val).symm
    (functorTriangleSmallTotalActionIso_heq_smallFunctor F G J T)
  exact h.trans (coherentTotalMapNativeModelComparison_smallFunctor_heq_large F J
    (functorTriangleTotalActionIso T))

end SerrePositivity.InfinityCategories.F2
