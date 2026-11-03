module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCospanCommonLeftCorrectionImage
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCospanCommonLeftValueImage
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCospanCommonLeftSectionImage
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCospanCommonLeftImageMaps

/-!
概要：共通の左脚全体の底の指定像を、元の四射と指定 path の合成へ同定する。
方針：三因子の指定像と四端点の厳密な式を合成する。
規約：元の指定値を保持。使われ方：左右の底の像の整合と引き戻し全体の比較。
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
local notation "f" => continuousKanReplacement.map cf
local notation "g" => continuousKanReplacement.map (coherentTransformationTotalMap Y Z C.fromRight)
local notation "nf" => coherentTotalMapNativeValueDown X Z cf
local notation "ng" => coherentTotalMapNativeValueDown Y Z
  (coherentTransformationTotalMap Y Z C.fromRight)
local notation "nl" => coherentTotalMapNativeValueDown F X cl
local notation "s" => eqToHom (coherentDiagramTotalVertex_object X)
local notation "v" => eqToHom (coherentDiagramTotalVertex_object Z)
local notation "w" => eqToHom (Eq.symm (coherentDiagramTotalVertex_object Z))
local notation "eF" => eqToHom (coherentDiagramTotalVertex_object F)
local notation "p" => intervalReplacementEndpoint f

/-- 左脚全体の底の指定像は、元の逆 path・二値比較・値の path の指定合成。 -/
lemma coherentCospanCommonLeftImage :
    HEq (((coherentCospanCommonLeftIso F X Y Z C).postcomp p).postcomp w)
      (((coherentCospanConeNativePathDownIso F X Y Z C).symm ≪≫
        (coherentTotalMapNativeValueDownIso X Z cf).precomp nl) ≪≫
        (coherentTotalMapNativeValueDownIso F X cl).postcomp (coherentTotalVertexMap X Z cf) ≪≫
        coherentCospanConeValuePathIso F X Y Z C) := by
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
  let a := functorIsoOfEq r rfl hr
  let b := (coherentTotalNativeKanIso F X cl).postcomp (intervalReplacementSection f)
  let i := FunctorIso.precomp (intervalReplacementSectionIso f) bM
  have hi : bM ≫ (prQ ≫ intervalReplacementSection f) =
      (eF ≫ continuousKanReplacement.map cl) ≫ intervalReplacementSection f := by
    simpa only [bM, prQ, Category.assoc] using congrArg (fun k => k ≫ intervalReplacementSection f)
      (coherentCospanModelFirstInput F X Y Z C)
  let c := functorIsoOfEq i hi (Category.comp_id bM)
  have hc : HEq (coherentCospanCommonLeftIso F X Y Z C) (a ≪≫ b ≪≫ c) :=
    functorIsoOfEq_heq _ _ _
  have hp := functorIso_postcomp_postcomp_heq_of_heq (a ≪≫ b ≪≫ c)
    (coherentCospanCommonLeftIso F X Y Z C)
    (by simpa only [aN, Category.assoc] using
      (coherentCospanNativeCommonComparison_left F X Y Z C).symm)
    (coherentCospanModelCommonComparison_left F X Y Z C).symm hc p w
  apply hp.trans
  rw [functorIso_postcomp_trans, functorIso_postcomp_trans,
    functorIso_postcomp_trans, functorIso_postcomp_trans]
  exact functorIso_trans_heq_of_heq _ _ _ _
    (coherentCospanCommonLeftSourceMap F X Y Z C)
    (coherentCospanCommonLeftMiddleMap F X Y Z C)
    (coherentCospanCommonLeftTargetMap F X Y Z C)
    ((functorIsoOfEq_postcomp_twice_heq r rfl hr p w).trans
      (coherentCospanCommonLeftCorrectionImage F X Y Z C))
    (functorIso_trans_heq_of_heq _ _ _ _
      (coherentCospanCommonLeftMiddleMap F X Y Z C)
      (coherentCospanCommonLeftValueTargetMap F X Y Z C)
      (coherentCospanCommonLeftTargetMap F X Y Z C)
      (coherentCospanCommonLeftValueImage F X Y Z C)
      ((functorIsoOfEq_postcomp_twice_heq i hi (Category.comp_id bM) p w).trans
        (coherentCospanCommonLeftSectionImage F X Y Z C)))

end SerrePositivity.InfinityCategories.F2
