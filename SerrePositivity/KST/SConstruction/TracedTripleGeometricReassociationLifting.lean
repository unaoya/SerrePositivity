module
public import SerrePositivity.KST.SConstruction.SixDiamondReassociationLifting
public import SerrePositivity.KST.SConstruction.TracedTripleGeometricPrefixStructureComparison

/-! # 元の実構造射に沿い六結合替えを全共有面と全基底像で持ち上げる
概要：元の raw 次段の十二面と上下合成面から、指定全基底六四面体を逐次持ち上げる。
方針：元の単射源構造射による実制限の fibration 性を、共有面を保つ六回の持ち上げへ渡す。
規約：指定基底データはまだ入力。上下合成面の同時選択と元の高次 prism の供給は別工程。
使われ方：隣接段の実六対角面消去を、元の全基底像を保って揃える。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet Spectra
open scoped Simplicial
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {w x y z : I} (f : w ⟶ x) (g : x ⟶ y) (h : y ⟶ z) (n : ℕ)
  (R : SixDiamondReassociations
    ((monicKTracedTripleFirstPairDiamond F f g h (n + 1)).map
      (monicKTracedTripleStageRestriction F w z n))
    ((monicKTracedTripleLastPairDiamond F f g h (n + 1)).map
      (monicKTracedTripleStageRestriction F w z n))
    ((monicKTracedTripleInterchangeDiamond F f g h (n + 1)).map
      (monicKTracedTripleStageRestriction F w z n))
    ((monicKTracedTripleLeftOuterDiamond F f g h (n + 1)).map
      (monicKTracedTripleStageRestriction F w z n))
    ((monicKTracedTripleRightOuterDiamond F f g h (n + 1)).map
      (monicKTracedTripleStageRestriction F w z n))
    ((monicKTracedTripleBFDiamond F f g h (n + 1)).map
      (monicKTracedTripleStageRestriction F w z n))
    ((monicKTracedTripleGeometricStagePasting F f g h (n + 1)).top.triangle.map
      (monicKTracedTripleStageRestriction F w z n))
    ((monicKTracedTripleGeometricStagePasting F f g h (n + 1)).bottom.triangle.map
      (monicKTracedTripleStageRestriction F w z n)))

/-- 元の実次段制限に沿い、全共有面を厳密に保って全基底六四面体を持ち上げる。 -/
def monicKTracedTripleGeometricReassociationLiftData :=
  sixDiamondReassociationsLiftData
    (monicKTracedTripleFirstPairDiamond F f g h (n + 1))
    (monicKTracedTripleLastPairDiamond F f g h (n + 1))
    (monicKTracedTripleInterchangeDiamond F f g h (n + 1))
    (monicKTracedTripleLeftOuterDiamond F f g h (n + 1))
    (monicKTracedTripleRightOuterDiamond F f g h (n + 1))
    (monicKTracedTripleBFDiamond F f g h (n + 1))
    (monicKTracedTripleGeometricStagePasting F f g h (n + 1)).top.triangle
    (monicKTracedTripleGeometricStagePasting F f g h (n + 1)).bottom.triangle
    (monicKTracedTripleStageRestriction F w z n) R

/-- 同時に持ち上げた第六全面の実制限は、元の指定第六基底全面そのもの。 -/
lemma monicKTracedTripleGeometricReassociationLiftData_sixth :
    SSet.yonedaEquiv.symm
        (monicKTracedTripleGeometricReassociationLiftData F f g h n R).pasting.sixthMove.simplex ≫
          monicKTracedTripleStageRestriction F w z n =
      SSet.yonedaEquiv.symm R.sixthMove.simplex :=
  (monicKTracedTripleGeometricReassociationLiftData F f g h n R).sixth_projection

/-- 最後の全残面の実制限も、終辺消去へ渡す同じ元の全基底残面そのもの。 -/
lemma monicKTracedTripleGeometricReassociationLiftData_residual :
    (monicKTracedTripleGeometricReassociationLiftData F f g h n R).pasting.sixthMove.left.map
        (monicKTracedTripleStageRestriction F w z n) = R.sixthMove.left :=
  (monicKTracedTripleGeometricReassociationLiftData F f g h n R).residual_eq

end SerrePositivity.KST.SConstruction
