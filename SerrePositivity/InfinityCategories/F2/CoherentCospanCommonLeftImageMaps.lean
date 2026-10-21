module

public import SerrePositivity.InfinityCategories.F2.CoherentCospanCommonLeftIso
public import SerrePositivity.InfinityCategories.F2.CoherentCospanCommonLeftCorrectionMaps

/-!
概要：共通の左脚の三因子の底の像の四端点を、元の小さい値の合成射へ同定する。
方針：厳密化・切断・元の模型の二射影の厳密な式を使う。
規約：端点等式を元の射から証明。使われ方：左脚全体の指定像の合成。
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
local notation "cr" => coherentTransformationTotalMap F Y C.toRight
local notation "cf" => coherentTransformationTotalMap X Z C.fromLeft
local notation "cg" => coherentTransformationTotalMap Y Z C.fromRight
local notation "f" => continuousKanReplacement.map cf
local notation "g" => continuousKanReplacement.map cg
local notation "nf" => coherentTotalMapNativeValueDown X Z cf
local notation "ng" => coherentTotalMapNativeValueDown Y Z cg
local notation "nl" => coherentTotalMapNativeValueDown F X cl
local notation "nr" => coherentTotalMapNativeValueDown F Y cr
local notation "s" => eqToHom (coherentDiagramTotalVertex_object X)
local notation "v" => eqToHom (coherentDiagramTotalVertex_object Z)
local notation "w" => eqToHom (Eq.symm (coherentDiagramTotalVertex_object Z))
local notation "eF" => eqToHom (coherentDiagramTotalVertex_object F)
local notation "aN" => coherentCospanConeNativeComparison F X Y Z C ≫
  pullback.fst (intervalReplacementEndpoint nf) ng
local notation "bM" => eF ≫ coherentCospanConeKanComparison F X Y Z C ≫
  pullback.fst (intervalReplacementEndpoint f) g
local notation "L" => cospanRectificationLeftMap nf f s v (coherentTotalNativeKanIso X Z cf)
local notation "p" => intervalReplacementEndpoint f

/-- 左補正の始端の底の射は元の native 右二射の合成。 -/
lemma coherentCospanCommonLeftSourceMap :
    ((aN ≫ L) ≫ p) ≫ w = nr ≫ ng := by
  calc
    _ = (aN ≫ (intervalReplacementEndpoint nf ≫ v)) ≫ w := by
      rw [Category.assoc aN L p, cospanRectificationLeftMap_over]
    _ = _ := coherentCospanCommonLeftCorrectionSourceMap F X Y Z C

/-- 左補正と内脚の値比較の接点の底の射。 -/
lemma coherentCospanCommonLeftMiddleMap :
    (((nl ≫ s) ≫ intervalReplacementSection f) ≫ p) ≫ w =
      nl ≫ coherentTotalVertexMap X Z cf := by
  simp only [Category.assoc, intervalReplacementSection_endpoint, coherentTotalVertexMap]

/-- 内脚の値比較と切断収縮の接点の底の射。 -/
lemma coherentCospanCommonLeftValueTargetMap :
    (((eF ≫ continuousKanReplacement.map cl) ≫ intervalReplacementSection f) ≫ p) ≫ w =
      coherentTotalVertexMap F X cl ≫ coherentTotalVertexMap X Z cf := by
  rw [← coherentTotalVertexMap_comp F X Z cl cf]
  simp only [coherentTotalVertexMap, Functor.map_comp, Category.assoc,
    intervalReplacementSection_endpoint]

/-- 切断収縮の終端の底の射は元の具体的な右二射の合成。 -/
lemma coherentCospanCommonLeftTargetMap :
    (bM ≫ p) ≫ w = coherentTotalVertexMap F Y cr ≫ coherentTotalVertexMap Y Z cg := by
  have hpb := congrArg
    (fun k => (eF ≫ coherentCospanConeKanComparison F X Y Z C) ≫ k ≫ w)
    (pullback.condition : pullback.fst (intervalReplacementEndpoint f) g ≫
      intervalReplacementEndpoint f = pullback.snd (intervalReplacementEndpoint f) g ≫ g)
  have hr := congrArg (fun k => (eF ≫ k ≫ g) ≫ w)
    (coherentCospanConeKanComparison_right F X Y Z C)
  calc
    _ = (eF ≫ (coherentCospanConeKanComparison F X Y Z C ≫
        intervalPullbackRight f g) ≫ g) ≫ w := by
      simpa only [Category.assoc, intervalPullbackRight] using hpb
    _ = (eF ≫ continuousKanReplacement.map cr ≫ g) ≫ w := hr
    _ = _ := by
      rw [← coherentTotalVertexMap_comp F Y Z cr cg]
      simp only [coherentTotalVertexMap, Functor.map_comp, Category.assoc]

end SerrePositivity.InfinityCategories.F2
