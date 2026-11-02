module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCospanCommonComparisons

/-!
概要：共通の二脚置換後における native 比較と模型比較の二射影を明示する。
方針：元の二つの引き戻し比較の射影式と、元の候補・Kan 比較の脚を合成する。
規約：元の指定射を保持。使われ方：全体の同型を貼る左右の指定関手同型。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}} [Quasicategory B]
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z)
local notation "cf" => coherentTransformationTotalMap X Z C.fromLeft
local notation "cg" => coherentTransformationTotalMap Y Z C.fromRight
local notation "f" => continuousKanReplacement.map cf
local notation "g" => continuousKanReplacement.map cg
local notation "nf" => coherentTotalMapNativeValueDown X Z cf
local notation "ng" => coherentTotalMapNativeValueDown Y Z cg
local notation "s" => eqToHom (coherentDiagramTotalVertex_object X)
local notation "t" => eqToHom (coherentDiagramTotalVertex_object Y)
local notation "v" => eqToHom (coherentDiagramTotalVertex_object Z)

/-- native 合成比較の第一脚は元の第一置換への射影と指定左厳密化の合成。 -/
lemma coherentCospanNativeCommonComparison_left :
    coherentCospanNativeCommonComparison F X Y Z C ≫
      pullback.fst (intervalReplacementEndpoint f) (intervalReplacementEndpoint g) =
        coherentCospanConeNativeComparison F X Y Z C ≫
          pullback.fst (intervalReplacementEndpoint nf) ng ≫
            cospanRectificationLeftMap nf f s v (coherentTotalNativeKanIso X Z cf) := by
  rw [coherentCospanNativeCommonComparison, Category.assoc,
    coherentCospanNativeKanPullbackComparison, cospanRectifiedPullbackComparison_left]

/-- native 合成比較の第二脚は元の右脚と指定右厳密化の合成。 -/
lemma coherentCospanNativeCommonComparison_right :
    coherentCospanNativeCommonComparison F X Y Z C ≫
      pullback.snd (intervalReplacementEndpoint f) (intervalReplacementEndpoint g) =
        coherentTotalMapNativeValueDown F Y (coherentTransformationTotalMap F Y C.toRight) ≫
          cospanRectificationRightMap ng g t v (coherentTotalNativeKanIso Y Z cg) := by
  rw [coherentCospanNativeCommonComparison, Category.assoc,
    coherentCospanNativeKanPullbackComparison, cospanRectifiedPullbackComparison_right,
    ← Category.assoc, coherentCospanConeNativeComparison_right]

/-- 模型合成比較の第一脚は元の Kan 比較の第一置換への射影そのもの。 -/
lemma coherentCospanModelCommonComparison_left :
    coherentCospanModelCommonComparison F X Y Z C ≫
      pullback.fst (intervalReplacementEndpoint f) (intervalReplacementEndpoint g) =
        eqToHom (coherentDiagramTotalVertex_object F) ≫
          coherentCospanConeKanComparison F X Y Z C ≫
            pullback.fst (intervalReplacementEndpoint f) g := by
  rw [coherentCospanModelCommonComparison, Category.assoc, Category.assoc,
    intervalPullbackDoubleReplacementComparison_left]

/-- 模型合成比較の第二脚は元の右脚の Kan 像と同じ指定定値切断の合成。 -/
lemma coherentCospanModelCommonComparison_right :
    coherentCospanModelCommonComparison F X Y Z C ≫
      pullback.snd (intervalReplacementEndpoint f) (intervalReplacementEndpoint g) =
        eqToHom (coherentDiagramTotalVertex_object F) ≫
          continuousKanReplacement.map (coherentTransformationTotalMap F Y C.toRight) ≫
            intervalReplacementSection g := by
  rw [coherentCospanModelCommonComparison, Category.assoc, Category.assoc,
    intervalPullbackDoubleReplacementComparison_right,
    ← Category.assoc (coherentCospanConeKanComparison F X Y Z C) (intervalPullbackRight f g)
      (intervalReplacementSection g), coherentCospanConeKanComparison_right]

end SerrePositivity.InfinityCategories.F2
