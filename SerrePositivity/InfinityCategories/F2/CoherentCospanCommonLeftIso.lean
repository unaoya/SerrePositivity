module

public import SerrePositivity.InfinityCategories.F2.CoherentCospanCommonInputs
public import SerrePositivity.InfinityCategories.F2.CospanRectificationImages
public import SerrePositivity.InfinityCategories.F2.IntervalReplacementSectionHomotopy

/-!
概要：共通の二脚置換後における native 比較と模型比較の左脚の指定同型を構成する。
方針：左厳密化の逆・元の左脚の値比較・同じ定値切断の指定収縮を続ける。
規約：元の全 path の指定類を保持。使われ方：引き戻し全体の同型の貼り合わせ。
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
local notation "f" => continuousKanReplacement.map cf
local notation "g" => continuousKanReplacement.map cg
local notation "nf" => coherentTotalMapNativeValueDown X Z cf
local notation "ng" => coherentTotalMapNativeValueDown Y Z cg
local notation "nl" => coherentTotalMapNativeValueDown F X cl
local notation "s" => eqToHom (coherentDiagramTotalVertex_object X)
local notation "v" => eqToHom (coherentDiagramTotalVertex_object Z)
local notation "eF" => eqToHom (coherentDiagramTotalVertex_object F)
local notation "p" => pullback.fst (intervalReplacementEndpoint f) (intervalReplacementEndpoint g)

/-- 元の左比較を同じ定値切断の指定収縮で補い、共通の第一置換内の指定同型を作る。 -/
def coherentCospanCommonLeftIso :
    FunctorIso (coherentCospanNativeCommonComparison F X Y Z C ≫ p)
      (coherentCospanModelCommonComparison F X Y Z C ≫ p) := by
  let aN := coherentCospanConeNativeComparison F X Y Z C ≫
    pullback.fst (intervalReplacementEndpoint nf) ng
  let bM := eF ≫ coherentCospanConeKanComparison F X Y Z C ≫
    pullback.fst (intervalReplacementEndpoint f) g
  let prn := pullback.snd ((intervalEndpointNatTrans 0).app
    (spaceInfinityObject (coherentDiagramTotalVertex Z)).obj) nf
  let prQ := pullback.snd ((intervalEndpointNatTrans 0).app
    (continuousKanReplacement.obj (smallLeftUnstraightening Z))) f
  let r := FunctorIso.precomp
    (cospanRectificationLeftIso nf f s v (coherentTotalNativeKanIso X Z cf)).symm aN
  have hr : aN ≫ (prn ≫ s ≫ intervalReplacementSection f) =
      (nl ≫ s) ≫ intervalReplacementSection f := by
    simpa only [aN, prn, Category.assoc] using congrArg
      (fun k => k ≫ s ≫ intervalReplacementSection f)
      (coherentCospanNativeFirstInput F X Y Z C)
  let r' := functorIsoOfEq r rfl hr
  let e := (coherentTotalNativeKanIso F X cl).postcomp (intervalReplacementSection f)
  let i := FunctorIso.precomp (intervalReplacementSectionIso f) bM
  have hi : bM ≫ (prQ ≫ intervalReplacementSection f) =
      (eF ≫ continuousKanReplacement.map cl) ≫ intervalReplacementSection f := by
    simpa only [bM, prQ, Category.assoc] using congrArg (fun k => k ≫ intervalReplacementSection f)
      (coherentCospanModelFirstInput F X Y Z C)
  let i' := functorIsoOfEq i hi (Category.comp_id bM)
  have hsrc : aN ≫ cospanRectificationLeftMap nf f s v
      (coherentTotalNativeKanIso X Z cf) = coherentCospanNativeCommonComparison F X Y Z C ≫ p := by
    simpa only [aN, Category.assoc] using
      (coherentCospanNativeCommonComparison_left F X Y Z C).symm
  exact functorIsoOfEq (r' ≪≫ e ≪≫ i') hsrc
    (coherentCospanModelCommonComparison_left F X Y Z C).symm

end SerrePositivity.InfinityCategories.F2
