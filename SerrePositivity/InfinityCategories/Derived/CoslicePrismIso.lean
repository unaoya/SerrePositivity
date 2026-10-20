module
public import SerrePositivity.InfinityCategories.Derived.CosliceInitialRealization
/-!
概要：可逆な全ホモトピーの coslice 実現の全 prism は、一つの全関手同型を与える。
方針：同じ全底を持つ各実成分の可逆性を左ファイブレーションで反映する。
規約：全添字の prism を再選択しない。使われ方：標準右 Kan 錐の全錐の同型比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
/-- 同じ全底の可逆ホモトピーの coslice 表示は、恒等錐の定値全族と全関手圏で同型。 -/
def CosliceHomotopyRealization.prismIso {K X : SSet.{u}} [Quasicategory X]
    {x : X _⦋0⦌} {f : K ⟶ X} {H : SSet.Homotopy (SSet.const x) f}
    (R : CosliceHomotopyRealization x f H)
    (hH : ∀ a, IsInvertibleEdge (simplicialHomotopyVertexEdge H a).toTruncated) :
    FunctorIso (SSet.const (cosliceIdentityCone x)) R.diagram := by
  let J := F2.prismHomotopy R.prism R.start R.finish
  apply functorIsoOfPointwiseInvertibleHomotopy J
  intro a
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
  exact leftFibration_reflects_invertibleEdge
    (sliceUnderProjection (SSet.yonedaEquiv.symm x)) e ((isInvertibleEdge_congr he).mpr (hH a))
end SerrePositivity.InfinityCategories
