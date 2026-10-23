module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCospanNativeCommonPointFiber
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCospanNativeTargetFiberEvaluation
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedTargetFiberTransport
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCospanNativeFaceSections

/-!
概要：共通点の同型による終点評価を、元の全三角形の終点 fiber 評価と照合する。
方針：図式辺の指定等式を保って終点評価を輸送する。
規約：元の同じ Z の fiber で比較。使われ方：native 二脚の共通終点像の整合。
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
local notation "el" => SSet.yonedaEquiv horn₂₂.ι₀₂
local notation "er" => SSet.yonedaEquiv horn₂₂.ι₁₂
local notation "Dl" => SSet.yonedaEquiv.symm (nativeConeTriangle c el)
local notation "Dr" => SSet.yonedaEquiv.symm (nativeConeTriangle c er)
local notation "f" => relativeFunctorOverPre pointedSpaceProjection (relativeCospanLeftTarget d)
local notation "g" => relativeFunctorOverPre pointedSpaceProjection (relativeCospanRightTarget d)
local notation "E" => coherentCospanNativeCommonPointFiberIso F X Y Z C b

/-- 左図式辺の表示輸送と共通点評価の合成は、元の全三角形の終点 fiber 評価。 -/
lemma coherentCospanNativeLeftTargetEvaluation_comparison :
    eqToHom (congrArg (relativeFunctorSpace pointedSpaceProjection)
      (nativeConeTriangle_diagram_edge c el)) ≫ f ≫ (E).hom =
        coherentCospanNativeLeftTargetFiberEvaluation F X Y Z C b := by
  have h := coherentCospanNativeCommonPointFiberIso_left F X Y Z C b
  exact (congrArg (fun k => eqToHom (congrArg (relativeFunctorSpace pointedSpaceProjection)
    (nativeConeTriangle_diagram_edge c el)) ≫ k) h).trans
      (pointedSectionTargetFiber_transport Z b (nativeConeTriangle_diagram_edge c el)
        (coherentTriangleTargetFiber_vertex F X Z C.toLeft C.fromLeft C.leftTriangle b Dl
          (coherentCospanNativeLeftTriangleDiagram_eq F X Y Z C b))
        (coherentCospanNativeLeftDiagramTarget_vertex F X Y Z C b))

/-- 右でも同じ共通点の同型と、同じ元の終点 fiber を使う。 -/
lemma coherentCospanNativeRightTargetEvaluation_comparison :
    eqToHom (congrArg (relativeFunctorSpace pointedSpaceProjection)
      (nativeConeTriangle_diagram_edge c er)) ≫ g ≫ (E).hom =
        coherentCospanNativeRightTargetFiberEvaluation F X Y Z C b := by
  have h := coherentCospanNativeCommonPointFiberIso_right F X Y Z C b
  exact (congrArg (fun k => eqToHom (congrArg (relativeFunctorSpace pointedSpaceProjection)
    (nativeConeTriangle_diagram_edge c er)) ≫ k) h).trans
      (pointedSectionTargetFiber_transport Z b (nativeConeTriangle_diagram_edge c er)
        (coherentTriangleTargetFiber_vertex F Y Z C.toRight C.fromRight C.rightTriangle b Dr
          (coherentCospanNativeRightTriangleDiagram_eq F X Y Z C b))
        (coherentCospanNativeRightDiagramTarget_vertex F X Y Z C b))

end SerrePositivity.InfinityCategories.F2
