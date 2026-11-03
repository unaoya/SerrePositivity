module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCospanNativeSectionPathImage
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCospanNativeFiberPath
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PrismDirectFiberFunctor

/-!
概要：切断模型の指定 path の下降を、既存の模型 fiber 比較の native 指定 path へ同定する。
方針：同じ共通長辺の指定像を下降し、全出力関手の一致と明示した実 fiber 合成式を使う。
規約：元の実端点と指定値を保持。使われ方：切断模型の普遍性の元の模型への移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z) (b : B _⦋0⦌)
local notation "pF" => smallLeftUnstraighteningProjection F
local notation "pX" => smallLeftUnstraighteningProjection X
local notation "pY" => smallLeftUnstraighteningProjection Y
local notation "pZ" => smallLeftUnstraighteningProjection Z
local notation "cl" => coherentTransformationTotalMap F X C.toLeft
local notation "cf" => coherentTransformationTotalMap X Z C.fromLeft
local notation "cr" => coherentTransformationTotalMap F Y C.toRight
local notation "cg" => coherentTransformationTotalMap Y Z C.fromRight
local notation "M" => coherentCospanNativeCommonFiberOutput F X Y Z C b
local notation "D" => functorSpaceDown (vertexFiber pF b) (vertexFiber pZ b)
local notation "tl" => congrArg SSet.HomotopyCategory.mk
  (coherentCospanNativeCommonFiberOutput_target_left F X Y Z C b)
local notation "tr" => congrArg SSet.HomotopyCategory.mk
  (coherentCospanNativeCommonFiberOutput_target_right F X Y Z C b)
local instance : KanComplex (vertexFiber pZ b) := vertexFiber_kanComplex_of_leftFibration _ _

/-- 同じ共通長辺の指定像の下降は、旧 native 指定 path の値を保持する。 -/
lemma coherentCospanNativeSectionFiberPathDownIso_heq_native :
    HEq (coherentCospanNativeSectionFiberPathDownIso F X Y Z C b)
      (coherentCospanNativeFiberPathIso F X Y Z C b) := by
  rw [coherentCospanNativeSectionFiberPathDownIso, functorIsoDown_eq_mapIso,
    coherentCospanNativeSectionFiberPathIso_eq_common_image]
  have hn := isoNormalizeEndpoints_map_heq D
    (VertexIso.map (coherentCospanNativeCommonLongPathIso F X Y Z C b) M) tl tr
  have hf := coherentPrismFiberFunctor_eq_direct F Z b
    (coherentCospanNativeLongBase F X Y Z C b)
    (coherentCospanNativeLongBase_initial F X Y Z C b)
    (coherentCospanPrismEndpoint_projection F X Y Z C b)
  have hm : HEq ((coherentCospanPrismFiberFunctor F X Y Z C b).mapIso
      (coherentCospanNativeCommonLongPathIso F X Y Z C b))
      ((D).mapIso (VertexIso.map (coherentCospanNativeCommonLongPathIso F X Y Z C b) M)) := by
    exact mapIso_heq_of_functor_eq_levels hf
      (coherentCospanNativeCommonLongPathIso F X Y Z C b)
  exact hn.trans (hm.symm.trans (iso_endpoints_heq
    (coherentCospanNativePrismFiberPathIso F X Y Z C b)
    (coherentCospanPrismFiber_obj_nativeLongLeft F X Y Z C b)
    (coherentCospanPrismFiber_obj_nativeLongRight F X Y Z C b)).symm)

/-- 明示した実 fiber の合成式で端点を揃えると、新旧の native 指定 path は厳密に一致。 -/
lemma coherentCospanNativeSectionFiberPathDownIso_eq_native :
    functorIsoOfEq (coherentCospanNativeSectionFiberPathDownIso F X Y Z C b)
      (vertexFiberMap_comp pF pX pZ cl cf
        (coherentTransformationTotalMap_projection F X C.toLeft)
        (coherentTransformationTotalMap_projection X Z C.fromLeft) b)
      (vertexFiberMap_comp pF pY pZ cr cg
        (coherentTransformationTotalMap_projection F Y C.toRight)
        (coherentTransformationTotalMap_projection Y Z C.fromRight) b) =
      coherentCospanNativeFiberPathIso F X Y Z C b := by
  exact eq_of_heq ((functorIsoOfEq_heq _ _ _).trans
    (coherentCospanNativeSectionFiberPathDownIso_heq_native F X Y Z C b))

/-- 実際の模型 fiber 比較の可換同型は、同じ切断模型の指定 path の下降である。 -/
lemma coherentCospanModelFiberPathIso_eq_section_down :
    functorIsoOfEq ((intervalPullbackPathIso (vertexFiberMap (cf ≫ pZ) pZ cf rfl b)
      (vertexFiberMap (cg ≫ pZ) pZ cg rfl b)).precomp
        (coherentCospanConeTotalModelFiberComparison F X Y Z C b))
      (coherentCospanConeFiberComparisonPath_left F X Y Z C b)
      (coherentCospanConeFiberComparisonPath_right F X Y Z C b) =
    functorIsoOfEq (coherentCospanNativeSectionFiberPathDownIso F X Y Z C b)
      (vertexFiberMap_comp pF pX pZ cl cf
        (coherentTransformationTotalMap_projection F X C.toLeft)
        (coherentTransformationTotalMap_projection X Z C.fromLeft) b)
      (vertexFiberMap_comp pF pY pZ cr cg
        (coherentTransformationTotalMap_projection F Y C.toRight)
        (coherentTransformationTotalMap_projection Y Z C.fromRight) b) := by
  exact (coherentCospanModelFiberPathIso_eq_native F X Y Z C b).trans
    (coherentCospanNativeSectionFiberPathDownIso_eq_native F X Y Z C b).symm

end SerrePositivity.InfinityCategories.F2
