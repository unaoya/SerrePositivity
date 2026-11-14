module
public import SerrePositivity.KST.Fibration.DGRelativeFiberComparison
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SliceSquareDiagramEvaluation

/-! # 元の K 頂点と同じ零角を持つ実 fiber 頂点への比較

錐の頂点の表示だけを移す。右辺や係数点を変更しない。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.Fibration
variable (A : Type u) [CommRing A] (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.RelativeVerdierDiagram (dgKInputNu.{u, v} A))

/-- 比較元の錐頂点は、元の相対 K 四角形の K(D) 頂点そのもの。 -/
theorem dgRelativeFiberComparison_source :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone (d.square ≫ dgKInputK A)).vertex =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (d.square ≫ dgKInputK A) 0 0 := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone.vertex_eq]
  change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[0] (horn 2 2) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.hom ≫ (d.square ≫ dgKInputK A))) = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cospanConeSquareIso_initialPoint,
    SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  rfl

/-- 比較先の錐頂点は、同じ元の零角と右辺を持つ fiber 四角形の fiber。 -/
theorem dgRelativeFiberComparison_target :
    (dgRelativeKLimitCone A d).vertex = (dgRelativeCanonicalFiberSquare A d).fiber := by
  have h := congrArg (fun f => f.app (Opposite.op ⦋0⦌) (dgRelativeKLimitCone A d))
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.sliceSquareDiagramMap_sourceEvaluation
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (d.square ≫ dgKInputK A)))
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := Sp.{max (u + 1) v})
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (𝟙 ((Δ[1] : SSet.{max (u + 1) v + 1}) ⊗ Δ[1])) 0 0)).app
      (Opposite.op ⦋0⦌) ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.sliceSquareDiagramMap _).app (Opposite.op ⦋0⦌)
        (dgRelativeKLimitCone A d)) = _ at h
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.sliceSquareDiagramMap_vertex] at h
  exact h.symm

/-- 元の K(D) から、元の零角と右辺を持つ実 fiber への同じ全一単体。 -/
def dgRelativeFiberVertexComparison :
    SSet.Edge (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (d.square ≫ dgKInputK A) 0 0)
      (dgRelativeCanonicalFiberSquare A d).fiber :=
  (SSet.Edge.ofTruncated (dgRelativeFiberComparison A d)).ofEq
    (dgRelativeFiberComparison_source A d) (dgRelativeFiberComparison_target A d)

/-- 頂点表示の移送は元の比較の全一単体を変えない。 -/
theorem dgRelativeFiberVertexComparison_edge :
    (dgRelativeFiberVertexComparison A d).edge = (dgRelativeFiberComparison A d).edge := rfl

/-- 元の K 四角形の引き戻し性を、元の K(D) からの同じ実辺で判定する。 -/
theorem dgRelativeK_isPullback_iff_fiberVertexComparison_isInvertible :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (d.square ≫ dgKInputK A) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (dgRelativeFiberVertexComparison A d) :=
  (dgRelativeK_isPullback_iff_fiberComparison_isInvertible A d).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (dgRelativeFiberVertexComparison_edge A d)).symm

end SerrePositivity.KST.Fibration
