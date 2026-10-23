module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCospanNativeFinalFiberIso
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.TriangleTargetFiberCoordinates

/-!
概要：左右の native 三角形の最終頂点は、元の同じ Z の小さい fiber 内で厳密に一致する。
方針：同じ全錐の共通長辺を終点で評価し、明示した fiber 同型と包含の単射性を使う。
規約：元の全錐と全パラメータを保持。使われ方：指定終点比較の合成と path への接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z) (b : B _⦋0⦌)
local notation "a" => coherentNativeTriangleFiberParameters F b
local notation "c" => coherentCospanConePointwiseCone F X Y Z C b
local notation "s" => coherentCospanFiberPointedSource F b
local notation "hs" => coherentCospanFiberPointedSource_projection F X Y Z C b
local notation "el" => SSet.yonedaEquiv horn₂₂.ι₀₂
local notation "er" => SSet.yonedaEquiv horn₂₂.ι₁₂
local notation "Dl" => SSet.yonedaEquiv.symm (nativeConeTriangle c el)
local notation "Dr" => SSet.yonedaEquiv.symm (nativeConeTriangle c er)
local notation "Nl" => nativePointedConeTriangleLift c s hs el
local notation "Nr" => nativePointedConeTriangleLift c s hs er

/-- 同じ全錐の左右三角形の最後の頂点の全族は、pointed 全空間で厳密に一致。 -/
lemma coherentCospanNativeFinalPointed_eq :
    prismEndpoint 1 a ≫ (stdSimplex.δ (0 : Fin 3) ▷ a) ≫ Nl =
      prismEndpoint 1 a ≫ (stdSimplex.δ (0 : Fin 3) ▷ a) ≫ Nr := by
  have he : prismEndpoint 1 a ≫ (stdSimplex.δ (0 : Fin 3) ▷ a) =
      prismEndpoint 1 a ≫ (stdSimplex.δ (1 : Fin 3) ▷ a) := by
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    intro z
    apply Prod.ext
    · apply SSet.stdSimplex.ext
      intro i
      rfl
    · rfl
  have h := congrArg (fun k => prismEndpoint 1 a ≫ k)
    (coherentCospanPointedConeLift_common_long F X Y Z C b)
  change prismEndpoint 1 a ≫ (stdSimplex.δ (1 : Fin 3) ▷ a) ≫ Nl =
    prismEndpoint 1 a ≫ (stdSimplex.δ (1 : Fin 3) ▷ a) ≫ Nr at h
  simpa only [← Category.assoc, ← he] using h

/-- 左右の評価射は、元の同じ Z の小さい fiber 内でも厳密に一致する。 -/
lemma coherentCospanNativeFinalFiberMap_eq :
    coherentCospanNativeLeftFinalFiberMap F X Y Z C b =
      coherentCospanNativeRightFinalFiberMap F X Y Z C b := by
  apply (cancel_mono ((coherentFiberPointedSourceIso Z b).hom ≫
    vertexFiberι pointedSpaceProjection (Z.app (Opposite.op ⦋0⦌) (ULift.up b)))).1
  have hl := pointedTriangleTargetFiberEvaluation_pointed F X Z C.toLeft C.fromLeft
    C.leftTriangle b Dl (coherentCospanNativeLeftTriangleDiagram_eq F X Y Z C b) Nl
    (nativePointedConeTriangleLift_projection c s hs el)
  have hr := pointedTriangleTargetFiberEvaluation_pointed F Y Z C.toRight C.fromRight
    C.rightTriangle b Dr (coherentCospanNativeRightTriangleDiagram_eq F X Y Z C b) Nr
    (nativePointedConeTriangleLift_projection c s hs er)
  simpa only [coherentCospanNativeLeftFinalFiberMap, coherentCospanNativeRightFinalFiberMap,
    coherentCospanNativeLeftTargetFiberEvaluation, coherentCospanNativeRightTargetFiberEvaluation,
    Category.assoc] using hl.trans ((coherentCospanNativeFinalPointed_eq F X Y Z C b).trans hr.symm)

end SerrePositivity.InfinityCategories.F2
