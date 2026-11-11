module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentTransformationTriangleSmall
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorEqIso

/-!
概要：元の coherent な cospan 錐の左右二三角形を共通の長辺とともに保持する。
方針：両三角形の指定全空間比較を同じ長辺で結ぶ。
規約：左右の辺・三角形を変更しない。使われ方：元の可換 path の Kan 置換への移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：共通の長辺を持つ元の cospan 錐の二つの全三角形。
方針：四辺と元の二三角形・長辺の等式を保持。
規約：存在・普遍性を仮定しない。使われ方：元の可換性の指定データ。 -/
structure CoherentTransformationCospanCone {B : SSet.{u}}
    (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) where
  toLeft : (leftUnstraighteningTransformationSpace F X) _⦋0⦌
  toRight : (leftUnstraighteningTransformationSpace F Y) _⦋0⦌
  fromLeft : (leftUnstraighteningTransformationSpace X Z) _⦋0⦌
  fromRight : (leftUnstraighteningTransformationSpace Y Z) _⦋0⦌
  leftTriangle : CoherentTransformationVertexTriangle F X Z toLeft fromLeft
  rightTriangle : CoherentTransformationVertexTriangle F Y Z toRight fromRight
  diagonal_eq : leftTriangle.diagonal = rightTriangle.diagonal

variable {B : SSet.{u}} [Quasicategory B]
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z)

/-- 概要：元の二三角形が定める小さい全空間の指定可換同型。
方針：左三角形を戻り、共通長辺を通って右三角形へ進む。
規約：指定比較を保持。使われ方：元の全 path の Kan 置換への延長。 -/
def coherentCospanConeTotalPathIso :
    FunctorIso
      (coherentTransformationTotalMap F X C.toLeft ≫ coherentTransformationTotalMap X Z C.fromLeft)
      (coherentTransformationTotalMap F Y C.toRight ≫
        coherentTransformationTotalMap Y Z C.fromRight) :=
  (coherentTransformationTriangleSmallIso F X Z C.toLeft C.fromLeft C.leftTriangle).symm ≪≫
    functorEqIso (congrArg (coherentTransformationTotalMap F Z) C.diagonal_eq) ≪≫
      coherentTransformationTriangleSmallIso F Y Z C.toRight C.fromRight C.rightTriangle

/-- 概要：指定可換同型は元の左右三角形の比較と同時に整合する。
方針：左三角形の往復を消去。
規約：同じ二つの指定比較。使われ方：元の共通長辺との整合。 -/
lemma coherentCospanConeTotalPathIso_triangle :
    coherentTransformationTriangleSmallIso F X Z C.toLeft C.fromLeft C.leftTriangle ≪≫
        coherentCospanConeTotalPathIso F X Y Z C =
      functorEqIso (congrArg (coherentTransformationTotalMap F Z) C.diagonal_eq) ≪≫
        coherentTransformationTriangleSmallIso F Y Z C.toRight C.fromRight C.rightTriangle := by
  simp only [coherentCospanConeTotalPathIso, Iso.trans_assoc]
  rw [← Iso.trans_assoc]
  simp

end SerrePositivity.InfinityCategories.F2
