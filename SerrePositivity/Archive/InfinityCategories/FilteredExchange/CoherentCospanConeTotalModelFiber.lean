module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCospanConeTotalModelComparison
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwisePullbackFiberIso

/-!
概要：底上の全空間比較を元の各 fiber の interval 引き戻しへの比較として表示する。
方針：底を固定した比較を fiber へ制限し、元の三座標を保つ fiber 同型を続ける。
規約：元の二脚・全 path を保持。使われ方：各点の引き戻し性による同値判定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z) (b : B _⦋0⦌)
local notation "cl" => coherentTransformationTotalMap F X C.toLeft
local notation "cr" => coherentTransformationTotalMap F Y C.toRight
local notation "cf" => coherentTransformationTotalMap X Z C.fromLeft
local notation "cg" => coherentTransformationTotalMap Y Z C.fromRight
local notation "p" => smallLeftUnstraighteningProjection Z
local notation "a" => smallLeftUnstraighteningProjection F
local notation "q" => fiberwiseIntervalPullbackProjection p cf cg
local notation "vf" => vertexFiberMap a q (coherentCospanConeTotalModelComparison F X Y Z C)
  (coherentCospanConeTotalModelComparison_over_base F X Y Z C) b
local notation "fb" => vertexFiberMap (cf ≫ p) p cf rfl b
local notation "gb" => vertexFiberMap (cg ≫ p) p cg rfl b

/-- 概要：元の全空間比較の各 fiber を元の三 fiber の path 引き戻しへ比較。
方針：元の fiber 同型で表示。規約：元の比較を保持。使われ方：各点の普遍性の入力。 -/
def coherentCospanConeTotalModelFiberComparison :
    vertexFiber a b ⟶ intervalPullback fb gb := vf ≫ (fiberwisePullbackFiberIso p cf cg b).hom

/-- 概要：fiber 比較の第一脚は元の第一脚の fiber 射そのもの。
方針：包含後で元の第一脚の厳密な式を使う。
規約：元の全空間射を保持。使われ方：各点の錐との照合。 -/
lemma coherentCospanConeTotalModelFiberComparison_left :
    coherentCospanConeTotalModelFiberComparison F X Y Z C b ≫ intervalPullbackLeft fb gb =
      vertexFiberMap a (cf ≫ p) cl (by
        rw [coherentTransformationTotalMap_projection,
          coherentTransformationTotalMap_projection]) b := by
  have h : coherentCospanConeTotalModelFiberComparison F X Y Z C b ≫
      intervalPullbackLeft fb gb = vf ≫ fiberwisePullbackFiberLeft p cf cg b := by
    change (vf ≫ fiberwisePullbackFiberComparison p cf cg b) ≫ _ = _
    rw [Category.assoc, fiberwisePullbackFiberComparison_left]
  apply vertexFiber_hom_ext
  rw [h, Category.assoc, fiberwisePullbackFiberLeft_ι, ← Category.assoc,
    vertexFiberMap_ι, vertexFiberMap_ι, Category.assoc, coherentCospanConeTotalModelComparison_left]

/-- 概要：fiber 比較の第二脚は元の第二脚の fiber 射そのもの。
方針：包含後で元の第二脚の厳密な式を使う。
規約：元の全空間射を保持。使われ方：各点の錐との照合。 -/
lemma coherentCospanConeTotalModelFiberComparison_right :
    coherentCospanConeTotalModelFiberComparison F X Y Z C b ≫ intervalPullbackRight fb gb =
      vertexFiberMap a (cg ≫ p) cr (by
        rw [coherentTransformationTotalMap_projection,
          coherentTransformationTotalMap_projection]) b := by
  have h : coherentCospanConeTotalModelFiberComparison F X Y Z C b ≫
      intervalPullbackRight fb gb = vf ≫ fiberwisePullbackFiberRight p cf cg b := by
    change (vf ≫ fiberwisePullbackFiberComparison p cf cg b) ≫ _ = _
    rw [Category.assoc, fiberwisePullbackFiberComparison_right]
  apply vertexFiber_hom_ext
  rw [h, Category.assoc, fiberwisePullbackFiberRight_ι, ← Category.assoc,
    vertexFiberMap_ι, vertexFiberMap_ι, Category.assoc,
    coherentCospanConeTotalModelComparison_right]

end SerrePositivity.InfinityCategories.F2
