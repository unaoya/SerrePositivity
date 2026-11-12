module
public import SerrePositivity.KST.Fibration.VerdierMovingUpperCanonical
public import SerrePositivity.KST.Fibration.VerdierReadoutBoundaryTriangles

/-!
概要：動く上側短辺の合成は、元の全 S• 比較の同じ実合成端成分である。
方針：固定包含での豊穣合成を core 制限へ戻し、元の同じ比較円柱を評価する。
規約：独立な core 比較を選ばず、元の非退化一単体を保持する。
使われ方：K-6 c4 の同じ相対合成から上側長 Hom 入力を構成する。
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

/-- 概要：元の二短辺の全豊穣合成は、同じ動く全 S• 辺の core 制限。
方針：元の定値包含の豊穣作用を全次数で計算する。
規約：全入力の写像の厳密等式。使われ方：長 Hom の全合成端条件。 -/
theorem verdierMovingUpperCompositeFamily_core (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
  verdierMovingUpperCompositeFamily d =
    verdierMovingUpperLastFamily d ≫ (SSet.uliftFunctor.{u+1,u}).map
      ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (coreSFullRealizationInclusion (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.left)))).app
        (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.right)).obj) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  rfl
/-- 概要：元の比較の全 path 成分は同じ動く短辺の実豊穣合成。
方針：同じ全円柱の合成端回収を宇宙持ち上げの実一単体へ代入する。
規約：群作用や同型類へ弱めない。使われ方：同じ相対合成の全 path 端の照合。 -/
theorem verdierMovingUpperCompositeFamily_component (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
  SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (verdierReadoutUpperComparison d)
    (ULift.up (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath.{u}))).edge =
      verdierMovingUpperCompositeFamily d := by
  rw [verdierMovingUpperCompositeFamily_core]
  apply SSet.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply]
  have hc := congrArg (fun f => f.app (Opposite.op ⦋1⦌) _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge)
    (verdierOriginalFullSCoreHomotopy_composite d 0 1)
  change ULift.up _ = ULift.up _
  apply congrArg ULift.up
  change (verdierOriginalFullSCoreHomotopy d 0 1).h.app (Opposite.op ⦋1⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (ComposableArrows.mk₀ coherentTriangleFullPath.{u}) 1,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge) = _ at hc
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one, coherentTriangleFullPath_eq_univ] at hc
  have hi : SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge := by
    apply SSet.stdSimplex.ext
    intro j
    fin_cases j <;> rfl
  change (verdierOriginalFullSCoreHomotopy d 0 1).h.app (Opposite.op ⦋1⦌)
    ((Truncated.Edge.id (X := (truncation 2).obj (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u}))
      (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath.{u})).edge, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge) =
      ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (coreSFullRealizationInclusion (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.left)))).app
        (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.right)).obj).app
          (Opposite.op ⦋1⦌) ((verdierOriginalFullSCompositePath d 0 1).app
            (Opposite.op ⦋1⦌) (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u}))))
  rw [hi]
  exact hc

end SerrePositivity.KST.Fibration
