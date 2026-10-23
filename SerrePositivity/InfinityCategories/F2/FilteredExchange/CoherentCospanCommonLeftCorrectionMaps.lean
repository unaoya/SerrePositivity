module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentNativeFirstPathMaps
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentNativeKanValueMaps

/-!
概要：共通の左脚の逆補正の三端点を元の小さい値の合成射へ戻す。
方針：元の入力射影と path の終端の式を、頂点表示の往復の相殺と合成する。
規約：端点等式は元の射から証明。使われ方：左補正の二因子の指定像を貼り合わせる。
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
local notation "nf" => coherentTotalMapNativeValueDown X Z cf
local notation "ng" => coherentTotalMapNativeValueDown Y Z
  (coherentTransformationTotalMap Y Z C.fromRight)
local notation "nl" => coherentTotalMapNativeValueDown F X
  (coherentTransformationTotalMap F X C.toLeft)
local notation "nr" => coherentTotalMapNativeValueDown F Y
  (coherentTransformationTotalMap F Y C.toRight)
local notation "aN" => coherentCospanConeNativeComparison F X Y Z C ≫
  pullback.fst (intervalReplacementEndpoint nf) ng
local notation "v" => eqToHom (coherentDiagramTotalVertex_object Z)
local notation "w" => eqToHom (Eq.symm (coherentDiagramTotalVertex_object Z))
local notation "s" => eqToHom (coherentDiagramTotalVertex_object X)
local notation "pr" => pullback.snd (NatTrans.app (intervalEndpointNatTrans 0)
  (KanObject.obj (spaceInfinityObject (coherentDiagramTotalVertex Z)))) nf

/-- 逆 path の始端を元の native 右二射の合成へ戻す。 -/
lemma coherentCospanCommonLeftCorrectionSourceMap :
    (aN ≫ (intervalReplacementEndpoint nf ≫ v)) ≫ w = nr ≫ ng := by
  have hv : v ≫ w = 𝟙 _ := (eqToIso (coherentDiagramTotalVertex_object Z)).hom_inv_id
  simpa only [Category.assoc, hv, Category.comp_id] using
    coherentCospanNativeFirstPathTargetMap F X Y Z C

/-- 逆 path と値比較の接点を元の native 左二射の合成へ戻す。 -/
lemma coherentCospanCommonLeftCorrectionMiddleMap :
    (aN ≫ (pr ≫ (nf ≫ v))) ≫ w = nl ≫ nf := by
  have hv : v ≫ w = 𝟙 _ := (eqToIso (coherentDiagramTotalVertex_object Z)).hom_inv_id
  simpa only [Category.assoc, hv, Category.comp_id] using
    coherentCospanNativeFirstPathSourceMap F X Y Z C

/-- 値比較の終端を元の native 左内脚と模型左外脚の合成へ戻す。 -/
lemma coherentCospanCommonLeftCorrectionTargetMap :
    (aN ≫ (pr ≫ (s ≫ continuousKanReplacement.map cf))) ≫ w =
      nl ≫ coherentTotalVertexMap X Z cf := by
  simpa only [Category.assoc, coherentTotalVertexMap] using congrArg
    (fun k => k ≫ s ≫ continuousKanReplacement.map cf ≫ w)
    (coherentCospanNativeFirstInput F X Y Z C)

end SerrePositivity.InfinityCategories.F2
