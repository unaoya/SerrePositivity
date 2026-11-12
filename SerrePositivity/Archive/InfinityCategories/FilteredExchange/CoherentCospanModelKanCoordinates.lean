module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCospanModelKanEquivalence
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwisePullbackKanCoordinates

/-!
概要：元の全空間模型の Kan 比較が保持する二脚と全 path 座標を明示する。
方針：元の模型比較と既存の Kan 引き戻し比較の三座標の厳密な式を合成する。
規約：比較射・全 path を固定。使われ方：native 比較候補の指定可換性との照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z)
local notation "p" => smallLeftUnstraighteningProjection Z
local notation "cf" => coherentTransformationTotalMap X Z C.fromLeft
local notation "cg" => coherentTransformationTotalMap Y Z C.fromRight

/-- Kan 比較の第一脚は元の第一脚の Kan 置換に厳密に一致する。 -/
lemma coherentCospanConeKanComparison_left :
    coherentCospanConeKanComparison F X Y Z C ≫
      intervalPullbackLeft (continuousKanReplacement.map cf) (continuousKanReplacement.map cg) =
        continuousKanReplacement.map (coherentTransformationTotalMap F X C.toLeft) := by
  rw [coherentCospanConeKanComparison, Category.assoc]
  change continuousKanReplacement.map _ ≫ (fiberwisePullbackKanComparison p cf cg ≫ _ ≫ _) = _
  rw [fiberwisePullbackKanComparison_left, ← Functor.map_comp,
    coherentCospanConeTotalModelComparison_left]

/-- Kan 比較の第二脚は元の第二脚の Kan 置換に厳密に一致する。 -/
lemma coherentCospanConeKanComparison_right :
    coherentCospanConeKanComparison F X Y Z C ≫
      intervalPullbackRight (continuousKanReplacement.map cf) (continuousKanReplacement.map cg) =
        continuousKanReplacement.map (coherentTransformationTotalMap F Y C.toRight) := by
  rw [coherentCospanConeKanComparison, Category.assoc]
  dsimp only [intervalPullbackRight]
  rw [fiberwisePullbackKanComparison_right, ← Functor.map_comp,
    coherentCospanConeTotalModelComparison_right]

/-- Kan 比較の全 path は元の底固定 path の Kan 像と指定 path 比較の合成である。 -/
lemma coherentCospanConeKanComparison_path :
    coherentCospanConeKanComparison F X Y Z C ≫
      intervalPullbackPath (continuousKanReplacement.map cf) (continuousKanReplacement.map cg) =
        continuousKanReplacement.map (coherentCospanConeTotalModelPath F X Y Z C) ≫
          fiberwiseIntervalKanComparison p := by
  rw [coherentCospanConeKanComparison, Category.assoc]
  change continuousKanReplacement.map _ ≫ (fiberwisePullbackKanComparison p cf cg ≫ _ ≫ _) = _
  rw [fiberwisePullbackKanComparison_path, ← Category.assoc, ← Functor.map_comp,
    coherentCospanConeTotalModelComparison_path]

end SerrePositivity.InfinityCategories.F2
