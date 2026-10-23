module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCospanConeNativeValuePath
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentTotalMapNativeValueDown

/-!
概要：元の四つの native 写像の値と指定可換 path を元の宇宙へ戻す。
方針：元の可換同型の両端を持ち上げの往復で表示し、その指定同型を降ろす。
規約：元の四射と指定同型を保持。使われ方：元の宇宙の引き戻し比較射。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}} [Quasicategory B]
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z)

/-- 概要：元の cospan の指定可換同型を元の小さい値の四射の間で表示。
方針：元の持ち上げた可換同型を両端の厳密な往復に沿って降ろす。
規約：元の二三角形からの指定同型。使われ方：実際の引き戻し比較の全 path。 -/
def coherentCospanConeNativePathDownIso :
    FunctorIso
      (coherentTotalMapNativeValueDown F X (coherentTransformationTotalMap F X C.toLeft) ≫
        coherentTotalMapNativeValueDown X Z (coherentTransformationTotalMap X Z C.fromLeft))
      (coherentTotalMapNativeValueDown F Y (coherentTransformationTotalMap F Y C.toRight) ≫
        coherentTotalMapNativeValueDown Y Z (coherentTransformationTotalMap Y Z C.fromRight)) := by
  apply functorIsoDown.{u, u + 1}
  apply functorIsoOfEq (coherentCospanConeNativeValuePathIso F X Y Z C)
  · rw [Functor.map_comp, coherentTotalMapNativeValueDown_lift,
      coherentTotalMapNativeValueDown_lift]
  · rw [Functor.map_comp, coherentTotalMapNativeValueDown_lift,
      coherentTotalMapNativeValueDown_lift]

end SerrePositivity.InfinityCategories.F2
