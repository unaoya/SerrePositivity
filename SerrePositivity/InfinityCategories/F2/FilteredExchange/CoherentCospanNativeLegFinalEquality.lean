module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCospanNativeFinalSourceMaps
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCospanNativeFinalTargetMaps

/-!
概要：native 二脚の共通終点での指定像を、実端点の式で補正して最終 fiber 同型へ同定する。
方針：元の切断族・fiber 二作用から証明した四端点の等式で、既存の型付き一致を輸送する。
規約：端点を指定して値を比較。使われ方：元の指定 path の合成式の厳密な適用。
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
local notation "c" => coherentCospanConePointwiseCone F X Y Z C b
local notation "d" => joinInr Δ[0] (horn 2 2) ≫ Subtype.val c
local notation "f" => relativeFunctorOverPre pointedSpaceProjection (relativeCospanLeftTarget d)
local notation "g" => relativeFunctorOverPre pointedSpaceProjection (relativeCospanRightTarget d)
local notation "I" => coherentCospanNativeCommonPointFiberIso F X Y Z C b

/-- 四端点のうち左の二端点を実射の式で補正すると、元の最終 fiber 同型に一致。 -/
lemma coherentCospanNativeLeftLegFinalImage_eq :
    functorIsoOfEq
      (((coherentCospanNativeLeftFiberSectionsIso F X Y Z C b).postcomp f).postcomp (I).hom)
      (coherentCospanNativeLeftFinalSourceMap F X Y Z C b)
      (coherentCospanNativeLeftFinalTargetMap F X Y Z C b) =
        coherentCospanNativeLeftFinalFiberIso F X Y Z C b :=
  eq_of_heq ((functorIsoOfEq_heq _ _ _).trans
    (coherentCospanNativeLeftLegFinalImage_heq F X Y Z C b))

/-- 右側でも元の同じ二端点の実射の式による補正を使う。 -/
lemma coherentCospanNativeRightLegFinalImage_eq :
    functorIsoOfEq
      (((coherentCospanNativeRightFiberSectionsIso F X Y Z C b).postcomp g).postcomp (I).hom)
      (coherentCospanNativeRightFinalSourceMap F X Y Z C b)
      (coherentCospanNativeRightFinalTargetMap F X Y Z C b) =
        coherentCospanNativeRightFinalFiberIso F X Y Z C b :=
  eq_of_heq ((functorIsoOfEq_heq _ _ _).trans
    (coherentCospanNativeRightLegFinalImage_heq F X Y Z C b))

end SerrePositivity.InfinityCategories.F2
