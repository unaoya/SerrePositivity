module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCospanConeRelativeForget
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FiberwiseHomotopyPoint
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwiseIntervalPullbackLift
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwiseIntervalProjection

/-!
概要：元の coherent cospan 錐から元の底上の interval 引き戻し全空間へ比較する。
方針：元の相対可換円柱を fiberwise interval family へ入れ、元の二脚と合わせる。
規約：底・二脚・全 path を厳密に保持。使われ方：各点の引き戻し性から全空間の同値へ。
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
  (C : CoherentTransformationCospanCone F X Y Z)
local notation "cl" => coherentTransformationTotalMap F X C.toLeft
local notation "cr" => coherentTransformationTotalMap F Y C.toRight
local notation "cf" => coherentTransformationTotalMap X Z C.fromLeft
local notation "cg" => coherentTransformationTotalMap Y Z C.fromRight
local notation "p" => smallLeftUnstraighteningProjection Z

/-- 概要：元の相対可換円柱の全 path を元の底上の interval family に表示。
方針：底固定円柱の実現。規約：元の全 path。使われ方：全空間比較の path 座標。 -/
def coherentCospanConeTotalModelPath :=
  fiberwiseHomotopyPoint p (smallLeftUnstraighteningProjection F)
    (coherentCospanConeRelativePathHomotopy F X Y Z C)
    (coherentCospanConeRelativePathHomotopy_projection F X Y Z C)

/-- 概要：元の coherent 錐から底上の interval 引き戻し全空間への実際の射。
方針：元の底固定 path と二脚を二段の引き戻しへ入れる。
規約：元の指定三座標。使われ方：全空間比較の fiber ごとの同値判定。 -/
def coherentCospanConeTotalModelComparison :
    smallLeftUnstraightening F ⟶ fiberwiseIntervalPullback p cf cg :=
  fiberwiseIntervalPullbackLift p cf cg (coherentCospanConeTotalModelPath F X Y Z C) cl cr
    (fiberwiseHomotopyPoint_zero _ _ _ _) (fiberwiseHomotopyPoint_one _ _ _ _)

/-- 概要：全空間比較の第一脚は元の指定第一脚。
方針：第一射影。規約：厳密な等式。使われ方：元の二射影の照合。 -/
lemma coherentCospanConeTotalModelComparison_left :
    coherentCospanConeTotalModelComparison F X Y Z C ≫ fiberwiseIntervalPullbackLeft p cf cg = cl :=
  fiberwiseIntervalPullbackLift_left _ _ _ _ _ _ _ _

/-- 概要：全空間比較の第二脚は元の指定第二脚。
方針：第二射影。規約：厳密な等式。使われ方：元の二射影の照合。 -/
lemma coherentCospanConeTotalModelComparison_right :
    coherentCospanConeTotalModelComparison F X Y Z C ≫
      fiberwiseIntervalPullbackRight p cf cg = cr :=
  fiberwiseIntervalPullbackLift_right _ _ _ _ _ _ _ _

/-- 概要：全空間比較の全 path は元の指定底固定円柱の実現そのもの。
方針：path 射影。規約：全単体の等式。使われ方：Kan 比較の元の path との照合。 -/
lemma coherentCospanConeTotalModelComparison_path :
    coherentCospanConeTotalModelComparison F X Y Z C ≫ fiberwiseIntervalPullbackPath p cf cg =
      coherentCospanConeTotalModelPath F X Y Z C :=
  fiberwiseIntervalPullbackLift_path _ _ _ _ _ _ _ _

/-- 概要：全空間比較は元の底を厳密に保つ。
方針：第一脚と元の二射の底の条件。
規約：全空間の射の等式。使われ方：fiber ごとの同値性の反映。 -/
lemma coherentCospanConeTotalModelComparison_projection :
    coherentCospanConeTotalModelComparison F X Y Z C ≫
      (fiberwiseIntervalPullbackLeft p cf cg ≫ cf ≫ p) = smallLeftUnstraighteningProjection F := by
  rw [← Category.assoc, coherentCospanConeTotalModelComparison_left,
    coherentTransformationTotalMap_projection, coherentTransformationTotalMap_projection]

/-- 概要：全空間比較は模型本来の底射に関して元の底を厳密に保つ。
方針：元の第一脚と模型の底射の式。
規約：模型の元の射影。使われ方：底上の全空間比較の fiber ごとの判定。 -/
lemma coherentCospanConeTotalModelComparison_over_base :
    coherentCospanConeTotalModelComparison F X Y Z C ≫
      fiberwiseIntervalPullbackProjection p cf cg = smallLeftUnstraighteningProjection F := by
  have h : fiberwiseIntervalPullbackLeft p cf cg ≫ cf ≫ p =
      fiberwiseIntervalPullbackProjection p cf cg :=
    fiberwiseIntervalPullback_left_projection p cf cg
  rw [← h]
  exact coherentCospanConeTotalModelComparison_projection F X Y Z C

end SerrePositivity.InfinityCategories.F2
