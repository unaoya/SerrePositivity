module

public import SerrePositivity.InfinityCategories.F2.CoherentCospanNativeCommonFiberImage
public import SerrePositivity.InfinityCategories.F2.CoherentCospanNativeCommonFiberEndpoints
public import SerrePositivity.InfinityCategories.F2.CoherentCospanNativeSectionFiberPath

/-!
概要：切断模型の指定 path を、同じ共通長辺の指定 path の直接 fiber 像へ同定する。
方針：四つの実頂点の等式で左右を補正し、共通始点の補正の相殺と指定像の合成則を使う。
規約：元の指定 path の値を保持。使われ方：既存の模型 fiber 比較との最終照合。
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
local notation "M" => coherentCospanNativeCommonFiberOutput F X Y Z C b
local notation "sl" => congrArg SSet.HomotopyCategory.mk
  (coherentCospanNativeCommonFiberOutput_source_left F X Y Z C b)
local notation "sr" => congrArg SSet.HomotopyCategory.mk
  (coherentCospanNativeCommonFiberOutput_source_right F X Y Z C b)
local notation "tl" => congrArg SSet.HomotopyCategory.mk
  (coherentCospanNativeCommonFiberOutput_target_left F X Y Z C b)
local notation "tr" => congrArg SSet.HomotopyCategory.mk
  (coherentCospanNativeCommonFiberOutput_target_right F X Y Z C b)

/-- 左最終 fiber 同型は、共通長辺の指定像を元の実端点で補正した値。 -/
lemma coherentCospanNativeLeftFinalFiberIso_eq_common_image :
    coherentCospanNativeLeftFinalFiberIso F X Y Z C b =
      isoNormalizeEndpoints
        (VertexIso.map (coherentCospanNativeLeftCommonLongComparison F X Y Z C b) M) sl tl := by
  exact (isoNormalizeEndpoints_eq_of_heq _ _ sl tl
    (coherentCospanNativeLeftFinalFiberIso_heq_common_image F X Y Z C b).symm).symm

/-- 右最終 fiber 同型にも同じ共通出力と元の実端点を使う。 -/
lemma coherentCospanNativeRightFinalFiberIso_eq_common_image :
    coherentCospanNativeRightFinalFiberIso F X Y Z C b =
      isoNormalizeEndpoints
        (VertexIso.map (coherentCospanNativeRightCommonLongComparison F X Y Z C b) M) sr tr := by
  exact (isoNormalizeEndpoints_eq_of_heq _ _ sr tr
    (coherentCospanNativeRightFinalFiberIso_heq_common_image F X Y Z C b).symm).symm

/-- 元の切断模型の指定 path は、共通長辺の同じ指定 path の直接像である。 -/
lemma coherentCospanNativeSectionFiberPathIso_eq_common_image :
    coherentCospanNativeSectionFiberPathIso F X Y Z C b =
      isoNormalizeEndpoints
        (VertexIso.map (coherentCospanNativeCommonLongPathIso F X Y Z C b) M) tl tr := by
  let hmid := congrArg (SSet.mapHomotopyCategory M).obj
    (congrArg SSet.HomotopyCategory.mk (coherentCospanNativeCommonLongSource_eq F X Y Z C b))
  unfold coherentCospanNativeSectionFiberPathIso
  rw [coherentCospanNativeLeftFinalFiberIso_eq_common_image,
    coherentCospanNativeRightFinalFiberIso_eq_common_image,
    isoNormalizeEndpoints_span _ _ hmid sl sr tl tr _]
  have h := functor_mapIso_span (SSet.mapHomotopyCategory M)
    (coherentCospanNativeLeftCommonLongComparison F X Y Z C b)
    (coherentCospanNativeRightCommonLongComparison F X Y Z C b)
    (congrArg SSet.HomotopyCategory.mk (coherentCospanNativeCommonLongSource_eq F X Y Z C b))
  exact congrArg (fun e => isoNormalizeEndpoints e tl tr) h.symm

end SerrePositivity.InfinityCategories.F2
