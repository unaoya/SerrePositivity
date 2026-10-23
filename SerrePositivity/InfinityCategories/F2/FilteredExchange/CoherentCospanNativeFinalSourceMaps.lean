module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCospanNativeLegFinalImages

/-!
概要：native 二脚の共通点像の始点を、元の全三角形の最終 fiber 射へ明示して同定する。
方針：元の図式辺の切断射の等式と、全三角形の終点評価の等式を合成する。
規約：同型の HEq から射の等式を取り出さない。使われ方：指定 path の合成式の輸送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z) (b : B _⦋0⦌)
local notation "c" => coherentCospanConePointwiseCone F X Y Z C b
local notation "d" => joinInr Δ[0] (horn 2 2) ≫ Subtype.val c
local notation "s" => coherentCospanFiberPointedSource F b
local notation "hs" => coherentCospanFiberPointedSource_projection F X Y Z C b
local notation "el" => SSet.yonedaEquiv horn₂₂.ι₀₂
local notation "er" => SSet.yonedaEquiv horn₂₂.ι₁₂
local notation "Dl" => SSet.yonedaEquiv.symm (nativeConeTriangle c el)
local notation "Dr" => SSet.yonedaEquiv.symm (nativeConeTriangle c er)
local notation "vl" => pointedTriangleFaceSections Dl (nativePointedConeTriangleLift c s hs el)
  (nativePointedConeTriangleLift_projection c s hs el) 0
local notation "vr" => pointedTriangleFaceSections Dr (nativePointedConeTriangleLift c s hs er)
  (nativePointedConeTriangleLift_projection c s hs er) 0
local notation "f" => relativeFunctorOverPre pointedSpaceProjection (relativeCospanLeftTarget d)
local notation "g" => relativeFunctorOverPre pointedSpaceProjection (relativeCospanRightTarget d)
local notation "I" => coherentCospanNativeCommonPointFiberIso F X Y Z C b
local notation "N" => coherentCospanNativeSectionPullback F X Y Z C b

/-- 元の native 左脚を共通点で評価すると、同じ全三角形の最終 fiber 射になる。 -/
lemma coherentCospanNativeLeftFinalSourceMap :
    ((N ≫ pullback.fst f g) ≫ f) ≫ (I).hom =
      coherentCospanNativeLeftFinalFiberMap F X Y Z C b := by
  have h := congrArg (fun k => (k ≫ f) ≫ (I).hom)
    (coherentCospanNativeLeftDiagramSections_eq F X Y Z C b).symm
  refine h.trans ?_
  change ((vl ≫ eqToHom (congrArg (relativeFunctorSpace pointedSpaceProjection)
    (nativeConeTriangle_diagram_edge c el))) ≫ f) ≫ (I).hom =
      vl ≫ coherentCospanNativeLeftTargetFiberEvaluation F X Y Z C b
  simpa only [Category.assoc] using congrArg (fun k => vl ≫ k)
    (coherentCospanNativeLeftTargetEvaluation_comparison F X Y Z C b)

/-- 右脚も元の同じ切断族と右全三角形の最終 fiber 射を厳密に保つ。 -/
lemma coherentCospanNativeRightFinalSourceMap :
    ((N ≫ pullback.snd f g) ≫ g) ≫ (I).hom =
      coherentCospanNativeRightFinalFiberMap F X Y Z C b := by
  have h := congrArg (fun k => (k ≫ g) ≫ (I).hom)
    (coherentCospanNativeRightDiagramSections_eq F X Y Z C b).symm
  refine h.trans ?_
  change ((vr ≫ eqToHom (congrArg (relativeFunctorSpace pointedSpaceProjection)
    (nativeConeTriangle_diagram_edge c er))) ≫ g) ≫ (I).hom =
      vr ≫ coherentCospanNativeRightTargetFiberEvaluation F X Y Z C b
  simpa only [Category.assoc] using congrArg (fun k => vr ≫ k)
    (coherentCospanNativeRightTargetEvaluation_comparison F X Y Z C b)

end SerrePositivity.InfinityCategories.F2
