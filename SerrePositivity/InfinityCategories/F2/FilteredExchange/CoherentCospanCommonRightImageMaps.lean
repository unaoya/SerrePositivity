module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCospanCommonRightIso

/-!
概要：共通の右脚の指定像を元の小宇宙へ戻す際の三つの端点の射を明示する。
方針：右厳密化の底の式、定値切断の終点、元の二射の合成式を使う。
規約：実際の射の等式を保持。使われ方：右脚の二因子の指定像を同時に合成する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}} [Quasicategory B]
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z)
local notation "cr" => coherentTransformationTotalMap F Y C.toRight
local notation "cg" => coherentTransformationTotalMap Y Z C.fromRight
local notation "g" => continuousKanReplacement.map cg
local notation "ng" => coherentTotalMapNativeValueDown Y Z cg
local notation "nr" => coherentTotalMapNativeValueDown F Y cr
local notation "t" => eqToHom (coherentDiagramTotalVertex_object Y)
local notation "v" => eqToHom (coherentDiagramTotalVertex_object Z)
local notation "w" => eqToHom (Eq.symm (coherentDiagramTotalVertex_object Z))
local notation "e" => coherentTotalNativeKanIso Y Z cg
local notation "R" => cospanRectificationRightMap ng g t v e
local notation "p" => intervalReplacementEndpoint g

/-- 右厳密化側の底の像の始域射は、元の native 右二射の合成である。 -/
lemma coherentCospanCommonRightCorrectionSourceMap :
    ((nr ≫ R) ≫ p) ≫ w = nr ≫ ng := by
  have hv : v ≫ w = 𝟙 _ := (eqToIso (coherentDiagramTotalVertex_object Z)).hom_inv_id
  calc
    _ = nr ≫ ((R ≫ p) ≫ w) := by simp only [Category.assoc]
    _ = nr ≫ ((ng ≫ v) ≫ w) := congrArg (fun k => nr ≫ (k ≫ w))
      (cospanRectificationRightMap_over ng g t v e)
    _ = _ := by rw [Category.assoc ng v w, hv, Category.comp_id]

/-- 二因子の間の底の射は、元の native 右内脚と具体的な右外射の合成である。 -/
lemma coherentCospanCommonRightMiddleMap :
    ((nr ≫ (t ≫ intervalReplacementSection g)) ≫ p) ≫ w =
      nr ≫ coherentTotalVertexMap Y Z cg := by
  simp only [coherentTotalVertexMap, Category.assoc, intervalReplacementSection_endpoint]

/-- 右脚の底の像の終域射は、元の具体的な二頂点射の合成である。 -/
lemma coherentCospanCommonRightTargetMap :
    ((eqToHom (coherentDiagramTotalVertex_object F) ≫
      (continuousKanReplacement.map cr ≫ intervalReplacementSection g)) ≫ p) ≫ w =
        coherentTotalVertexMap F Y cr ≫ coherentTotalVertexMap Y Z cg := by
  rw [← coherentTotalVertexMap_comp F Y Z cr cg]
  simp only [coherentTotalVertexMap, Functor.map_comp, Category.assoc,
    intervalReplacementSection_endpoint]

end SerrePositivity.InfinityCategories.F2
