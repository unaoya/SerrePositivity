module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCospanConePointwiseTriangles

/-!
概要：各点の native cospan 錐の四辺を元の四つの変換の評価辺と同定する。
方針：元の左右二三角形の第一面と第二面を読む。
規約：指定された全一次単体を保持。使われ方：元の各点の引き戻し性の適用。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z) (b : B _⦋0⦌)
local notation "c" => coherentCospanConePointwiseCone F X Y Z C b
local notation "d" => joinInr Δ[0] (horn 2 2) ≫ coherentCospanConePointwiseDiagram F X Y Z C b
local notation "el" => SSet.yonedaEquiv horn₂₂.ι₀₂
local notation "er" => SSet.yonedaEquiv horn₂₂.ι₁₂

/-- 概要：各点の左脚は元の左変換の指定評価辺。
方針：元の左三角形の第一面。規約：一次単体の等式。使われ方：元の左脚の同定。 -/
lemma coherentCospanConePointwiseCone_left :
    (nativeConeLeg c ((horn 2 2 : SSet.{u + 1}).δ 1 el)).edge =
      (functorEdgeAt (intervalMappingEdgeOfVertex C.toLeft) (ULift.up b)).edge := by
  exact (nativeConeTriangle_face c el (1 : Fin 2)).symm.trans
    ((congrArg (SpaceInfinity.δ 2)
      (coherentCospanConePointwiseCone_leftTriangle F X Y Z C b)).trans
        (coherentTransformationPointTriangle_first C.leftTriangle (ULift.up b)))

/-- 概要：各点の右脚は元の右変換の指定評価辺。
方針：元の右三角形の第一面。規約：一次単体の等式。使われ方：元の右脚の同定。 -/
lemma coherentCospanConePointwiseCone_right :
    (nativeConeLeg c ((horn 2 2 : SSet.{u + 1}).δ 1 er)).edge =
      (functorEdgeAt (intervalMappingEdgeOfVertex C.toRight) (ULift.up b)).edge := by
  exact (nativeConeTriangle_face c er (1 : Fin 2)).symm.trans
    ((congrArg (SpaceInfinity.δ 2)
      (coherentCospanConePointwiseCone_rightTriangle F X Y Z C b)).trans
        (coherentTransformationPointTriangle_first C.rightTriangle (ULift.up b)))

/-- 概要：各点の cospan の左辺は元の左入力変換の指定評価辺。
方針：元の左三角形の第二面。規約：一次単体の等式。使われ方：元の cospan の同定。 -/
lemma coherentCospanConePointwiseCone_fromLeft :
    (d).app (Opposite.op ⦋1⦌) el =
      (functorEdgeAt (intervalMappingEdgeOfVertex C.fromLeft) (ULift.up b)).edge := by
  exact (nativeConeTriangle_zero c el).symm.trans
    ((congrArg (SpaceInfinity.δ 0)
      (coherentCospanConePointwiseCone_leftTriangle F X Y Z C b)).trans
        (coherentTransformationPointTriangle_second C.leftTriangle (ULift.up b)))

/-- 概要：各点の cospan の右辺は元の右入力変換の指定評価辺。
方針：元の右三角形の第二面。規約：一次単体の等式。使われ方：元の cospan の同定。 -/
lemma coherentCospanConePointwiseCone_fromRight :
    (d).app (Opposite.op ⦋1⦌) er =
      (functorEdgeAt (intervalMappingEdgeOfVertex C.fromRight) (ULift.up b)).edge := by
  exact (nativeConeTriangle_zero c er).symm.trans
    ((congrArg (SpaceInfinity.δ 0)
      (coherentCospanConePointwiseCone_rightTriangle F X Y Z C b)).trans
        (coherentTransformationPointTriangle_second C.rightTriangle (ULift.up b)))

end SerrePositivity.InfinityCategories.F2
