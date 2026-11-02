module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCospanCommonCoordinates

/-!
概要：共通の第一置換への二比較の入力射影を、元の左脚に厳密に同定する。
方針：元の三座標の第一入力の式を、同じ頂点表示の下で読む。
規約：元の射の等式。使われ方：共通の左脚の指定関手同型の端点整合。
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
local notation "cl" => coherentTransformationTotalMap F X C.toLeft
local notation "cf" => coherentTransformationTotalMap X Z C.fromLeft
local notation "cg" => coherentTransformationTotalMap Y Z C.fromRight
local notation "nf" => coherentTotalMapNativeValueDown X Z cf
local notation "ng" => coherentTotalMapNativeValueDown Y Z cg
local notation "f" => continuousKanReplacement.map cf
local notation "g" => continuousKanReplacement.map cg

/-- native 候補の第一置換成分の入力は、元の native 左脚そのものである。 -/
lemma coherentCospanNativeFirstInput :
    (coherentCospanConeNativeComparison F X Y Z C ≫
      pullback.fst (intervalReplacementEndpoint nf) ng) ≫
        pullback.snd ((intervalEndpointNatTrans 0).app
          (spaceInfinityObject (coherentDiagramTotalVertex Z)).obj) nf =
            coherentTotalMapNativeValueDown F X cl := by
  simpa only [Category.assoc, intervalPullbackLeft] using
    coherentCospanConeNativeComparison_left F X Y Z C

/-- 模型の第一置換成分の入力は、元の左脚の Kan 像を同じ頂点表示で移した射。 -/
lemma coherentCospanModelFirstInput :
    (eqToHom (coherentDiagramTotalVertex_object F) ≫
      coherentCospanConeKanComparison F X Y Z C ≫
        pullback.fst (intervalReplacementEndpoint f) g) ≫
          pullback.snd ((intervalEndpointNatTrans 0).app
            (continuousKanReplacement.obj (smallLeftUnstraightening Z))) f =
              eqToHom (coherentDiagramTotalVertex_object F) ≫ continuousKanReplacement.map cl := by
  rw [Category.assoc, Category.assoc]
  change eqToHom (coherentDiagramTotalVertex_object F) ≫
    (coherentCospanConeKanComparison F X Y Z C ≫ intervalPullbackLeft f g) = _
  rw [coherentCospanConeKanComparison_left]

end SerrePositivity.InfinityCategories.F2
