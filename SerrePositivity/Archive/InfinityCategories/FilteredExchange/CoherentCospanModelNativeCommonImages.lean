module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCospanModelLeftCorrectionImage
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCospanNativeLegFinalEquality
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCospanModelFinalTargetMaps
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerAlgebra

/-!
概要：実模型と native 切断の二脚の指定同型を、共通点で元の最終 fiber 同型へ比較する。
方針：四つの実端点の式と補正円柱の指定像を、後合成と指定合成の交換に適用する。
規約：元の指定値を保持。使われ方：二脚の底の整合と全体の貼り合わせ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z) (b : B _⦋0⦌)
local notation "c" => coherentCospanConePointwiseCone F X Y Z C b
local notation "d" => joinInr Δ[0] (horn 2 2) ≫ Subtype.val c
local notation "f" => relativeFunctorOverPre pointedSpaceProjection (relativeCospanLeftTarget d)
local notation "g" => relativeFunctorOverPre pointedSpaceProjection (relativeCospanRightTarget d)
local notation "I" => coherentCospanNativeCommonPointFiberIso F X Y Z C b
local instance : HomotopicalAlgebra.Fibration f :=
  relativeCospanLeftTarget_fibration pointedSpaceProjection d

/-- 左脚の共通点像は、元の左最終 fiber 同型に元の native 指定 path を続けたもの。 -/
lemma coherentCospanModelNativeLeftCommonImage_heq :
    HEq (((coherentCospanModelNativeLeftIso F X Y Z C b).postcomp f).postcomp (I).hom)
      (coherentCospanNativeLeftFinalFiberIso F X Y Z C b ≪≫
        coherentCospanNativeSectionFiberPathIso F X Y Z C b) := by
  unfold coherentCospanModelNativeLeftIso
  dsimp only
  rw [functorIso_postcomp_trans, functorIso_postcomp_trans]
  refine functorIso_trans_heq_of_heq _ _ _ _
    (coherentCospanNativeLeftFinalSourceMap F X Y Z C b)
    (coherentCospanNativeLeftFinalTargetMap F X Y Z C b)
    (coherentCospanModelLeftFinalTargetMap F X Y Z C b)
    (coherentCospanNativeLeftLegFinalImage_heq F X Y Z C b) ?_
  refine (functorIsoOfEq_postcomp_postcomp_heq _ _ _ _ _).trans ?_
  exact (heq_of_eq (functorIso_postcomp_postcomp _ _ _).symm).trans
    (coherentCospanModelLeftCorrectionIso_image F X Y Z C b)

/-- 右脚の共通点像は、元の右全三角形の同じ最終 fiber 同型。 -/
lemma coherentCospanModelNativeRightCommonImage_heq :
    HEq (((coherentCospanModelNativeRightIso F X Y Z C b).postcomp g).postcomp (I).hom)
      (coherentCospanNativeRightFinalFiberIso F X Y Z C b) := by
  unfold coherentCospanModelNativeRightIso
  refine (functorIsoOfEq_postcomp_postcomp_heq _ _ _ _ _).trans ?_
  exact (heq_of_eq (functorIso_postcomp_postcomp _ _ _).symm).trans
    (coherentCospanNativeRightLegFinalImage_heq F X Y Z C b)

end SerrePositivity.InfinityCategories.F2
