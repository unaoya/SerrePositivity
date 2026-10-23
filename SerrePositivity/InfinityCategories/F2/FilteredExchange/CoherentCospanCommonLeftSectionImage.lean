module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.IntervalSectionPathImage
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCospanModelFirstPathValueImage

/-!
概要：共通の左脚の最後の切断収縮の底の像を元の値の指定 path に同定する。
方針：切断収縮の終点像と模型の第一置換 path の像の二つの一致を合成する。
規約：元の指定値を保持。使われ方：左脚全体の三因子の像を合成する。
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
local notation "f" => continuousKanReplacement.map (coherentTransformationTotalMap X Z C.fromLeft)
local notation "g" => continuousKanReplacement.map (coherentTransformationTotalMap Y Z C.fromRight)
local notation "bM" => eqToHom (coherentDiagramTotalVertex_object F) ≫
  coherentCospanConeKanComparison F X Y Z C ≫ pullback.fst (intervalReplacementEndpoint f) g
local notation "w" => eqToHom (Eq.symm (coherentDiagramTotalVertex_object Z))

/-- 定値切断収縮の元の値での像は、元の候補の値の指定 path である。 -/
lemma coherentCospanCommonLeftSectionImage :
    HEq ((((intervalReplacementSectionIso f).precomp bM).postcomp
      (intervalReplacementEndpoint f)).postcomp w)
      (coherentCospanConeValuePathIso F X Y Z C) := by
  exact (intervalReplacementSectionIso_precomp_endpoint_image f bM w).trans
    (coherentCospanModelFirstPathValueImage F X Y Z C)

end SerrePositivity.InfinityCategories.F2
