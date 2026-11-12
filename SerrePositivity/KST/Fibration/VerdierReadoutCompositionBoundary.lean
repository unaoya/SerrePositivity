module
public import SerrePositivity.KST.Fibration.VerdierReadoutRelativeComposition

/-!
概要：同じ相対合成の長辺を、元の直接端・動く合成端へ全族で厳密に戻す。
方針：同じ実合成二単体の面一を境界へ制限し、元の二端点図式を評価する。
規約：元の下側読出しと全 S• 比較を保持し、厳密切断を使わない。
使われ方：K-6 c4 の動く上側短辺と整合する全長 Hom 入力の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u})
  (L : (Δ[1] : SSet.{u + 1}) ⟶ (ihom ((SSet.uliftFunctor.{u + 1, u}).obj
    (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u}))).obj (verdierLowerNativeLongHomTarget d))
  (hL : VerdierLowerNativeReadoutRecovery d L)
  (hfull : L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
    (ULift.up (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath.{u})) =
      verdierLowerReconstructionCompositeFamily d Δ[1])

section CompositionData
variable
  (H : SSet.Homotopy
    ((SSet.uliftFunctor.{u + 1, u}).map (verdierOriginalNativeHomFamily d 0))
    (SSet.const (X := (SSet.uliftFunctor.{u + 1, u}).obj (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u}))
      (verdierNativeCompositePoint d 1)))
  (T : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle (verdierReadoutUpperComparison d)
    (verdierLowerNativeReadoutHomotopy d L hL) H)
  (hT : T.diagram ≫ (pre verdierReadoutPathBoundary.{u}).app _ =
    curry (verdierReadoutBoundaryDiagram d L hL hfull))
include hT

/-- 概要：相対合成の長辺は同じ境界二単体の長辺族を厳密に回収する。
方針：元の実二単体族の面一を、同じ境界制限等式へ代入する。
規約：native path 境界の全単体での等式。
使われ方：同じ全長 Hom 合成の両端成分を回収する。 -/
theorem verdierReadoutComposition_boundary :
    (verdierReadoutPathBoundary.{u} ▷ (Δ[1] : SSet.{u + 1})) ≫ H.h =
      ((boundary 1 : SSet.{u + 1}) ◁ stdSimplex.δ (1 : Fin 3)) ≫
        verdierReadoutBoundaryDiagram d L hL hfull := by
  apply curry_injective
  rw [← curry_pre_app, curry_natural_left, ← T.face_one, Category.assoc, hT]

/-- 概要：同じ合成長辺の全境界は、元の読出し直接端と全 S• 比較合成端の図式。
方針：境界面の回収と元の指定二単体の長辺回収をつなぐ。
規約：二成分の点ごとの同型ではなく全境界写像の厳密等式。
使われ方：直接端を固定し動く第二短辺を保持する実長 Hom 入力。 -/
theorem verdierReadoutComposition_longBoundary :
    (verdierReadoutPathBoundary.{u} ▷ (Δ[1] : SSet.{u + 1})) ≫ H.h =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram
        (SSet.yonedaEquiv.symm
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (verdierLowerNativeReadoutHomotopy d L hL)
            (ULift.up (ComposableArrows.mk₀ coherentTriangleDirectPath.{u}))).edge)
        (SSet.yonedaEquiv.symm
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (verdierReadoutUpperComparison d)
            (ULift.up (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath.{u}))).edge) :=
  (verdierReadoutComposition_boundary d L hL hfull H T hT).trans
    (verdierReadoutBoundaryDiagram_long d L hL hfull)

/-- 概要：同じ合成の直接端は元の同じ下側読出しの実成分そのもの。
方針：全境界を零端で評価し、元の所有する直接 path へ戻す。
規約：全一単体の厳密等式。
使われ方：元の下側共有対角の全族を保持する。 -/
theorem verdierReadoutComposition_direct :
    lift (SSet.const (ULift.up (ComposableArrows.mk₀ coherentTriangleDirectPath.{u})))
      (𝟙 (Δ[1] : SSet.{u + 1})) ≫ H.h =
      SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (verdierLowerNativeReadoutHomotopy d L hL)
          (ULift.up (ComposableArrows.mk₀ coherentTriangleDirectPath.{u}))).edge := by
  have h := congrArg (fun f => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint 0 (Δ[1] : SSet.{u + 1}) ≫ f)
    (verdierReadoutComposition_longBoundary d L hL hfull H T hT)
  simpa only [← Category.assoc, verdierReadoutPathBoundary_zero,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_zero] using h

/-- 概要：同じ合成の全 path 端は元の全 S• 比較の実合成端成分そのもの。
方針：全境界を一端で評価し、同じ全合成 path を回収する。
規約：動く合成端の非退化一単体を含む厳密等式。
使われ方：動く上側第二短辺と同じ全長 Hom 合成端を照合する。 -/
theorem verdierReadoutComposition_full :
    lift (SSet.const (ULift.up (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath.{u})))
      (𝟙 (Δ[1] : SSet.{u + 1})) ≫ H.h =
      SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (verdierReadoutUpperComparison d)
          (ULift.up (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath.{u}))).edge := by
  have h := congrArg (fun f => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint 1 (Δ[1] : SSet.{u + 1}) ≫ f)
    (verdierReadoutComposition_longBoundary d L hL hfull H T hT)
  simpa only [← Category.assoc, verdierReadoutPathBoundary_one,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_one] using h
end CompositionData

end SerrePositivity.KST.Fibration
