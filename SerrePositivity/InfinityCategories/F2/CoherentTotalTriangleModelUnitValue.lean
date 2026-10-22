module

public import SerrePositivity.InfinityCategories.F2.CoherentTotalTriangleNativeModelValue
public import SerrePositivity.InfinityCategories.F2.CoherentTotalTriangleModelUnitEndpoints
public import SerrePositivity.InfinityCategories.F2.CoherentColimitNativeModelEndpoints

/-!
概要：元の模型三角形の指定値を、同じ実両端で単位交換の指定三角形項へ同定する。
方針：同じ単位終点の等式を明示し、保持した模型値と元の全空間三角形の値を照合する。
規約：元の模型比較を保持。使われ方：a6 の指定比較の三角形交換式への等式としての代入。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u}) [Quasicategory B]
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b d)

/-- 元の模型三角形は、同じ単位実両端上で元の全空間三角形項に値まで等しい。 -/
lemma coherentTotalTriangleNativeModelComparison_eq_unit_triangle :
    vertexIsoOfEq (coherentTotalTriangleNativeModelComparison T)
      (congrArg functorVertex (coherentColimitNativeModelTarget_eq_unit B d))
      (congrArg functorVertex (coherentTotalTriangleNativeModelTarget_eq_unit a b)) =
    functorIsoOfEq ((functorTriangleTotalActionIso T).postcomp (coherentLargeTotalUnit J))
      (coherentTransformationTotalMap_unit_lift F J (coherentVertexOfHomotopy d))
      (coherentColimitUpperUnitTriangle_target (B := B) (a := a) (b := b)) := by
  apply eq_of_heq
  exact (vertexIsoOfEq_heq _ _ _).trans
    ((coherentTotalTriangleNativeModelComparison_heq_large_unit T).trans
      (functorIsoOfEq_heq _ _ _).symm)

end SerrePositivity.InfinityCategories.F2
