module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CosliceHomotopyRealization
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.EvaluationLimitCone
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.InitialTransport
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting
/-!
概要：可逆な全評価の coslice 実現の各値は、同じ coslice の実始対象。
方針：保持した全 prism の成分を左ファイブレーションで反映し、恒等錐から始対象性を移す。
規約：別の各点の表示を選ばない。使われ方：商側三角形の全添字空間の弱可縮性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
/-- 可逆な全ホモトピーの coslice 表示の各値は、元の同じ coslice の始対象。 -/
lemma CosliceHomotopyRealization.isInitialVertex {K X : SSet.{u}} [Quasicategory X]
    {x : X _⦋0⦌} {f : K ⟶ X} {H : SSet.Homotopy (SSet.const x) f}
    (R : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.CosliceHomotopyRealization x f H)
    (hH : ∀ a, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H a).toTruncated)
    (a : K _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (R.diagram.app (Opposite.op ⦋0⦌) a) := by
  let J := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.prismHomotopy R.prism R.start R.finish
  let e := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge J a).toTruncated
  have he : (e.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)))).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H a).edge := by
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)).app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge J a).edge = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.prismHomotopy_vertical]
    have hb := congrArg (fun t : (Δ[1] : SSet.{u}) ⊗ K ⟶ X =>
      t.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant a 1)) R.base
    exact hb.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.evaluationHomotopyPrism_vertical H a)
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge
      (e.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)))) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr he).mpr (hH a)
  have ei := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.leftFibration_reflects_invertibleEdge
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)) e hi
  have : IsIso (Truncated.HomotopyCategory.homMk e) := ei
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.cosliceIdentityCone_isInitialVertex x).of_vertexIso
    (asIso (Truncated.HomotopyCategory.homMk e))
end SerrePositivity.InfinityCategories.Project.DerivedCategories
