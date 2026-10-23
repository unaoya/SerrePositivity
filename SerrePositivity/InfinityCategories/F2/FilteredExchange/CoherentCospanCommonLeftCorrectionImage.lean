module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CospanLeftInverseImage
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCospanCommonLeftCorrectionMaps
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentNativeInversePathImage
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCospanCommonLeftOuterImage

/-!
概要：共通の左脚の逆厳密化補正を、元の逆 path と左外脚の値比較へ戻す。
方針：逆厳密化の指定像を制限し、三端点の式の下で二因子の指定像を合成する。
規約：元の指定 path と端点を保持。使われ方：共通の左脚の全指定像の正規化。
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
local notation "f" => continuousKanReplacement.map cf
local notation "nf" => coherentTotalMapNativeValueDown X Z cf
local notation "ng" => coherentTotalMapNativeValueDown Y Z
  (coherentTransformationTotalMap Y Z C.fromRight)
local notation "nl" => coherentTotalMapNativeValueDown F X
  (coherentTransformationTotalMap F X C.toLeft)
local notation "aN" => coherentCospanConeNativeComparison F X Y Z C ≫
  pullback.fst (intervalReplacementEndpoint nf) ng
local notation "s" => eqToHom (coherentDiagramTotalVertex_object X)
local notation "v" => eqToHom (coherentDiagramTotalVertex_object Z)
local notation "w" => eqToHom (Eq.symm (coherentDiagramTotalVertex_object Z))
local notation "e" => coherentTotalNativeKanIso X Z cf
local notation "L" => cospanRectificationLeftIso nf f s v e
local notation "p" => intervalReplacementEndpoint f
local notation "pr" => pullback.snd (NatTrans.app (intervalEndpointNatTrans 0)
  (KanObject.obj (spaceInfinityObject (coherentDiagramTotalVertex Z)))) nf

/-- 左逆補正の底の指定像は、元の逆 path と元の左外脚の値比較の合成。 -/
lemma coherentCospanCommonLeftCorrectionImage :
    HEq (((FunctorIso.precomp (Iso.symm L) aN).postcomp p).postcomp w)
      ((coherentCospanConeNativePathDownIso F X Y Z C).symm ≪≫
        (coherentTotalMapNativeValueDownIso X Z cf).precomp nl) := by
  have h := cospanRectificationLeftIso_inverse_whisker_image nf f s v e aN w
  apply h.trans
  exact functorIso_trans_heq_of_heq _ _ _ _
    (coherentCospanCommonLeftCorrectionSourceMap F X Y Z C)
    (coherentCospanCommonLeftCorrectionMiddleMap F X Y Z C)
    (coherentCospanCommonLeftCorrectionTargetMap F X Y Z C)
    (coherentCospanNativeInversePathImage F X Y Z C)
    (coherentCospanCommonLeftOuterImage F X Y Z C)

end SerrePositivity.InfinityCategories.F2
