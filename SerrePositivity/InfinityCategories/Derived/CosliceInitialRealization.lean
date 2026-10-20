module
public import SerrePositivity.InfinityCategories.Derived.CosliceHomotopyRealization
public import SerrePositivity.InfinityCategories.Derived.EvaluationLimitCone
public import SerrePositivity.InfinityCategories.Stable.InitialTransport
public import SerrePositivity.InfinityCategories.Core.InvertibleEdgeLifting
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
/-- 可逆な全ホモトピーの coslice 表示の各値は、元の同じ coslice の始対象。 -/
lemma CosliceHomotopyRealization.isInitialVertex {K X : SSet.{u}} [Quasicategory X]
    {x : X _⦋0⦌} {f : K ⟶ X} {H : SSet.Homotopy (SSet.const x) f}
    (R : CosliceHomotopyRealization x f H)
    (hH : ∀ a, IsInvertibleEdge (simplicialHomotopyVertexEdge H a).toTruncated)
    (a : K _⦋0⦌) : IsInitialVertex (R.diagram.app (Opposite.op ⦋0⦌) a) := by
  let J := F2.prismHomotopy R.prism R.start R.finish
  let e := (simplicialHomotopyVertexEdge J a).toTruncated
  have he : (e.map ((truncation 2).map (sliceUnderProjection (SSet.yonedaEquiv.symm x)))).edge =
      (simplicialHomotopyVertexEdge H a).edge := by
    change (sliceUnderProjection (SSet.yonedaEquiv.symm x)).app (Opposite.op ⦋1⦌)
      (simplicialHomotopyVertexEdge J a).edge = _
    rw [F2.prismHomotopy_vertical]
    have hb := congrArg (fun t : (Δ[1] : SSet.{u}) ⊗ K ⟶ X =>
      t.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant a 1)) R.base
    exact hb.trans (evaluationHomotopyPrism_vertical H a)
  have hi : IsInvertibleEdge
      (e.map ((truncation 2).map (sliceUnderProjection (SSet.yonedaEquiv.symm x)))) :=
    (isInvertibleEdge_congr he).mpr (hH a)
  have ei := leftFibration_reflects_invertibleEdge
    (sliceUnderProjection (SSet.yonedaEquiv.symm x)) e hi
  have : IsIso (Truncated.HomotopyCategory.homMk e) := ei
  exact (cosliceIdentityCone_isInitialVertex x).of_vertexIso
    (asIso (Truncated.HomotopyCategory.homMk e))
end SerrePositivity.InfinityCategories
