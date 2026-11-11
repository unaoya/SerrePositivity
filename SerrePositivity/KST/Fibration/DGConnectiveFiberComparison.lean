module
public import SerrePositivity.KST.Fibration.DGRelativeFiberComparisonVertices
public import SerrePositivity.KST.LocalizingInvariants.SpectrumEdgePi

/-!
概要：固定 dg 四角形から実 Sp fiber への比較を、ν の Verdier 認証なしで構成する。
方針：元の四角形の全錐を同じ cospan の実極限錐へ送り、同じ全比較辺を射影する。
規約：K 像の零角を明示入力とする。非負次数の全単射性や Sp 引き戻し性は仮定済み成果にしない。
使われ方：連結版 K-6 d と、全段の Sp 引き戻し性を使わない K-7 の構造射。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories

open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable (A : Type u) [CommRing A]
  (F : (Δ[1] ⊗ Δ[1] : SSet.{max (u + 1) v + 1}) ⟶ dgKInputInfinity.{u, v} A)
  (hz : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (F ≫ dgKInputK A) 0 1))

/-- 元の K 四角形の右辺と上辺をそのまま底とする、Sp の構成済み極限錐。 -/
def dgConnectiveKLimitCone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (F ≫ dgKInputK A)) :=
  OmegaSpectrum.CoherentPullback.infinityCone _

theorem dgConnectiveKLimitCone_isLimit : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (dgConnectiveKLimitCone A F) :=
  OmegaSpectrum.CoherentPullback.infinityCone_isLimit _

/-- 元の零角と右辺を変えず、左下の頂点を実 fiber に置き換えた四角形。 -/
def dgConnectiveCanonicalFiberSquare : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FiberSquare
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareRightArrow (F ≫ dgKInputK A)) where
  square := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare (dgConnectiveKLimitCone A F)
  zero_corner := by
    have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare (dgConnectiveKLimitCone A F) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ (F ≫ dgKInputK A) := by
      rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare_top]
      exact congrArg (fun q => q ≫ (F ≫ dgKInputK A))
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary_topEdge
    have hcorner : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare (dgConnectiveKLimitCone A F)) 0 1 =
        _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (F ≫ dgKInputK A) 0 1 := by
      rw [← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareTopEdge_source, ht, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareTopEdge_source]
    rw [hcorner]
    exact hz
  right_edge := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare_right]
    change horn₂₂.ι₀₂ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (F ≫ dgKInputK A) = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary_rightEdge]
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareRightArrow_edge]
    exact (SSet.yonedaEquiv.symm_apply_apply
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ (F ≫ dgKInputK A))).symm
  isPullback := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare_isPullback _ (dgConnectiveKLimitCone_isLimit A F)

/-- 比較元は元の K 四角形の全錐、比較先は同じ cospan の実極限錐。 -/
def dgConnectiveFiberConeComparison :
    SSet.Truncated.Edge (X := (truncation 2).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (F ≫ dgKInputK A))))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone (F ≫ dgKInputK A)) (dgConnectiveKLimitCone A F) :=
  Classical.choice ((dgConnectiveKLimitCone_isLimit A F).nonempty_edge _)

/-- 全錐の同じ比較を頂点へ射影した、元の K 頂点から実 fiber への辺。 -/
def dgConnectiveFiberComparison :
    SSet.Truncated.Edge (X := (truncation 2).obj Sp.{max (u + 1) v})
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone (F ≫ dgKInputK A)).vertex (dgConnectiveKLimitCone A F).vertex :=
  (dgConnectiveFiberConeComparison A F).map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection _))

/-- 同じ比較辺と、比較元・比較先の各元の脚の実合成三角形。 -/
def dgConnectiveFiberComparisonLegTriangle
    (k : (horn 2 2 : SSet.{max (u + 1) v + 1}) _⦋0⦌) :
    SSet.Truncated.Edge.CompStruct (dgConnectiveFiberComparison A F)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg (dgConnectiveKLimitCone A F) k)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone (F ≫ dgKInputK A)) k) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeConeComparisonLegTriangle (dgConnectiveFiberConeComparison A F) k


/-- 比較元の錐頂点は、元の相対 K 四角形の K(D) 頂点そのもの。 -/
theorem dgConnectiveFiberComparison_source :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone (F ≫ dgKInputK A)).vertex =
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (F ≫ dgKInputK A) 0 0 := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone.vertex_eq]
  change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[0] (horn 2 2) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.hom ≫ (F ≫ dgKInputK A))) = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cospanConeSquareIso_initialPoint,
    SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  rfl

/-- 比較先の錐頂点は、同じ元の零角と右辺を持つ fiber 四角形の fiber。 -/
theorem dgConnectiveFiberComparison_target :
    (dgConnectiveKLimitCone A F).vertex = (dgConnectiveCanonicalFiberSquare A F hz).fiber := by
  have h := congrArg (fun f => f.app (Opposite.op ⦋0⦌) (dgConnectiveKLimitCone A F))
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.sliceSquareDiagramMap_sourceEvaluation
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (F ≫ dgKInputK A)))
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := Sp.{max (u + 1) v})
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (𝟙 ((Δ[1] : SSet.{max (u + 1) v + 1}) ⊗ Δ[1])) 0 0)).app
      (Opposite.op ⦋0⦌) ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.sliceSquareDiagramMap _).app (Opposite.op ⦋0⦌)
        (dgConnectiveKLimitCone A F)) = _ at h
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.sliceSquareDiagramMap_vertex] at h
  exact h.symm

/-- 元の K(D) から、元の零角と右辺を持つ実 fiber への同じ全一単体。 -/
def dgConnectiveFiberVertexComparison :
    SSet.Edge (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (F ≫ dgKInputK A) 0 0)
      (dgConnectiveCanonicalFiberSquare A F hz).fiber :=
  (SSet.Edge.ofTruncated (dgConnectiveFiberComparison A F)).ofEq
    (dgConnectiveFiberComparison_source A F) (dgConnectiveFiberComparison_target A F hz)

/-- 頂点表示の移送は元の比較の全一単体を変えない。 -/
theorem dgConnectiveFiberVertexComparison_edge :
    (dgConnectiveFiberVertexComparison A F hz).edge = (dgConnectiveFiberComparison A F).edge := rfl


/-- 明示零角の下で、元の実 fiber 比較辺の整数 π 作用。Verdier 認証は使わない。 -/
def dgConnectiveFiberComparisonPi (j : ℤ) :=
  (SpectrumHo.piFunctor j).map (Truncated.HomotopyCategory.homMk
    (dgConnectiveFiberVertexComparison A F hz).toTruncated)

/-- 非負次数の実 fiber 比較が全単射という条件の下で、同じ比較射を順方向とする群同型。 -/
def dgConnectiveFiberComparison_nonnegativeEquiv
    (h : ∀ j : ℤ, 0 ≤ j → Function.Bijective (dgConnectiveFiberComparisonPi A F hz j).hom)
    (j : ℤ) (hj : 0 ≤ j) :=
  MulEquiv.ofBijective (dgConnectiveFiberComparisonPi A F hz j).hom (h j hj)

end SerrePositivity.KST.Fibration
