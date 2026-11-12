module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCospanNativeFinalFiberIso
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionCurryIsoImage
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeTriangleFinalFiberOutput
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoTransport

/-!
概要：左右の native 最終 fiber 同型を、元の全三角形比較の単一の指定像として表示する。
方針：切断族の端点補正と最後の fiber への後合成を、元の豊穣作用へ戻す。
規約：左右とも元の全三角形比較を保持。使われ方：共通長辺の指定像との合成の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
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
local notation "i" => scaffoldFirstVertex 2 ▷ a
local notation "v" => snd Δ[0] a ≫ s
local notation "hl" => coherentTriangleTargetFiber_vertex F X Z C.toLeft C.fromLeft
  C.leftTriangle b Dl (coherentCospanNativeLeftTriangleDiagram_eq F X Y Z C b)
local notation "hr" => coherentTriangleTargetFiber_vertex F Y Z C.toRight C.fromRight
  C.rightTriangle b Dr (coherentCospanNativeRightTriangleDiagram_eq F X Y Z C b)

/-- 左の最終 fiber 出力の元の全延長空間からの豊穣作用。 -/
def coherentCospanNativeLeftFinalFiberOutput :=
  relativeTriangleFinalFiberOutput Z b Dl i v (nativePointedConeTriangle_initial c s hs el) 0 hl

/-- 右も同じ元の全三角形比較を写す最終 fiber 出力。 -/
def coherentCospanNativeRightFinalFiberOutput :=
  relativeTriangleFinalFiberOutput Z b Dr i v (nativePointedConeTriangle_initial c s hs er) 0 hr

/-- 左の端点補正済み同型は、元の全三角形比較による同じ指定像。 -/
lemma coherentCospanNativeLeftFinalFiberIso_heq_image :
    HEq (coherentCospanNativeLeftFinalFiberIso F X Y Z C b)
      (VertexIso.map (coherentCospanNativeLeftTriangleComparison F X Y Z C b)
        (coherentCospanNativeLeftFinalFiberOutput F X Y Z C b)) := by
  unfold coherentCospanNativeLeftFinalFiberIso
  refine (functorIsoOfEq_heq _ _ _).trans ?_
  exact relativeExtensionCurryRestrictionIso_postcomp_heq_map pointedSpaceProjection
    (fst Δ[2] a ≫ Dl) i v (nativePointedConeTriangle_initial c s hs el)
    (stdSimplex.δ (0 : Fin 3) ▷ a) (stdSimplex.δ (0 : Fin 3) ≫ Dl)
    (by rw [← Category.assoc, whiskerRight_fst, Category.assoc])
    (nativePointedConeTriangleLift c s hs el)
    (coherentSmallFiberPointedTriangle F X Z C.toLeft C.fromLeft C.leftTriangle b)
    (nativePointedConeTriangleLift_projection c s hs el)
    (coherentCospanPointedFiberTriangle_left_projection F b X Y Z C)
    (nativePointedConeTriangleLift_initial c s hs el)
    (coherentSmallFiberPointedTriangle_initial F X Z C.toLeft C.fromLeft C.leftTriangle b)
    (coherentCospanNativeLeftTriangleComparison F X Y Z C b)
    (coherentCospanNativeLeftTargetFiberEvaluation F X Y Z C b)

/-- 右の端点補正済み同型も同じ全三角形比較の指定像を保持する。 -/
lemma coherentCospanNativeRightFinalFiberIso_heq_image :
    HEq (coherentCospanNativeRightFinalFiberIso F X Y Z C b)
      (VertexIso.map (coherentCospanNativeRightTriangleComparison F X Y Z C b)
        (coherentCospanNativeRightFinalFiberOutput F X Y Z C b)) := by
  unfold coherentCospanNativeRightFinalFiberIso
  refine (functorIsoOfEq_heq _ _ _).trans ?_
  exact relativeExtensionCurryRestrictionIso_postcomp_heq_map pointedSpaceProjection
    (fst Δ[2] a ≫ Dr) i v (nativePointedConeTriangle_initial c s hs er)
    (stdSimplex.δ (0 : Fin 3) ▷ a) (stdSimplex.δ (0 : Fin 3) ≫ Dr)
    (by rw [← Category.assoc, whiskerRight_fst, Category.assoc])
    (nativePointedConeTriangleLift c s hs er)
    (coherentSmallFiberPointedTriangle F Y Z C.toRight C.fromRight C.rightTriangle b)
    (nativePointedConeTriangleLift_projection c s hs er)
    (coherentCospanPointedFiberTriangle_right_projection F b X Y Z C)
    (nativePointedConeTriangleLift_initial c s hs er)
    (coherentSmallFiberPointedTriangle_initial F Y Z C.toRight C.fromRight C.rightTriangle b)
    (coherentCospanNativeRightTriangleComparison F X Y Z C b)
    (coherentCospanNativeRightTargetFiberEvaluation F X Y Z C b)

end SerrePositivity.InfinityCategories.F2
