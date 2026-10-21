module

public import SerrePositivity.InfinityCategories.F2.CoherentCospanCommonRightCorrectionImage
public import SerrePositivity.InfinityCategories.F2.CoherentCospanCommonRightValueImage
public import SerrePositivity.InfinityCategories.F2.CoherentCospanCommonRightImageMaps
public import SerrePositivity.InfinityCategories.F2.HomotopyIsoRawComparison

/-!
概要：共通の右脚の指定同型の底の像を、元の小宇宙の二つの値比較の指定合成へ同定する。
方針：元の外側の端点補正を保持し、三つの実際の端点等式で二因子の像を合成する。
規約：元の指定値を保持。使われ方：左右の底の整合から全体の同型を貼る。
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
local notation "cr" => coherentTransformationTotalMap F Y C.toRight
local notation "cg" => coherentTransformationTotalMap Y Z C.fromRight
local notation "f" => continuousKanReplacement.map (coherentTransformationTotalMap X Z C.fromLeft)
local notation "g" => continuousKanReplacement.map cg
local notation "ng" => coherentTotalMapNativeValueDown Y Z cg
local notation "nr" => coherentTotalMapNativeValueDown F Y cr
local notation "t" => eqToHom (coherentDiagramTotalVertex_object Y)
local notation "v" => eqToHom (coherentDiagramTotalVertex_object Z)
local notation "w" => eqToHom (Eq.symm (coherentDiagramTotalVertex_object Z))
local notation "p" => intervalReplacementEndpoint g
local notation "R" => cospanRectificationRightIso ng g t v (coherentTotalNativeKanIso Y Z cg)

/-- 元の右脚全体の底の指定像は、元の右外脚・右内脚の値比較の指定合成である。 -/
lemma coherentCospanCommonRightImage :
    HEq (((coherentCospanCommonRightIso F X Y Z C).postcomp p).postcomp w)
      ((coherentTotalMapNativeValueDownIso Y Z cg).precomp nr ≪≫
        (coherentTotalMapNativeValueDownIso F Y cr).postcomp (coherentTotalVertexMap Y Z cg)) := by
  let a := FunctorIso.precomp (Iso.symm R) nr
  let b := functorIsoOfEq ((coherentTotalNativeKanIso F Y cr).postcomp
    (intervalReplacementSection g)) (Category.assoc _ _ _) (Category.assoc _ _ _)
  have hc : HEq (coherentCospanCommonRightIso F X Y Z C) (a ≪≫ b) :=
    functorIsoOfEq_heq _ _ _
  have hp := functorIso_postcomp_postcomp_heq_of_heq (a ≪≫ b)
    (coherentCospanCommonRightIso F X Y Z C)
    (coherentCospanNativeCommonComparison_right F X Y Z C).symm
    (coherentCospanModelCommonComparison_right F X Y Z C).symm hc p w
  have hi : HEq (FunctorIso.postcomp (FunctorIso.postcomp (a ≪≫ b) p) w)
      ((coherentTotalMapNativeValueDownIso Y Z cg).precomp nr ≪≫
        (coherentTotalMapNativeValueDownIso F Y cr).postcomp (coherentTotalVertexMap Y Z cg)) := by
    rw [functorIso_postcomp_trans, functorIso_postcomp_trans]
    exact functorIso_trans_heq_of_heq ((a.postcomp p).postcomp w) ((b.postcomp p).postcomp w)
      ((coherentTotalMapNativeValueDownIso Y Z cg).precomp nr)
      ((coherentTotalMapNativeValueDownIso F Y cr).postcomp (coherentTotalVertexMap Y Z cg))
      (coherentCospanCommonRightCorrectionSourceMap F X Y Z C)
      (coherentCospanCommonRightMiddleMap F X Y Z C)
      (coherentCospanCommonRightTargetMap F X Y Z C)
      (coherentCospanCommonRightCorrectionImage F X Y Z C)
      (coherentCospanCommonRightValueImage F X Y Z C)
  exact hp.trans hi

end SerrePositivity.InfinityCategories.F2
