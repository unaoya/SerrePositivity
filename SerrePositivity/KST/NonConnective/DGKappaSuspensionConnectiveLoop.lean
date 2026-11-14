module
public import SerrePositivity.KST.NonConnective.DGKappaSuspensionKRoof
public import SerrePositivity.KST.Fibration.DGConnectiveFiberComparison
public import SerrePositivity.KST.Spectra.SpectrumNativeLoopFunctor
public import SerrePositivity.KST.Spectra.SpectrumLoopSquares

/-!
概要：元の固定 dg 四角形と cone の K 零性から、懸垂の実 loop 比較を作る。
方針：ν の Verdier 認証を使わない同じ canonical fiber を、元の懸垂の loop として保持する。
規約：実四角形・K 零角・指定三頂点に条件付き。元の K 四角形の Sp 引き戻し性は仮定しない。
使われ方：K-7 c5 の一般経路。連結版 fibration の非負次数比較を接続する始点。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
open SerrePositivity.KST.Fibration SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.NonConnective

local instance connectiveLoopSpectrumCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory
local instance connectiveLoopSpectrumHomKan (X Y : OmegaSpectrum.{w}) :
    KanComplex (SimplicialCategory.sHom X Y) := OmegaSpectrum.mappingSpace_kanComplex X Y

variable (R : Type u) [CommRing R] (D : Type (max (u + 1) v)) [DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ) (Z : DGKappaZeroInput R D I)
  (F : (Δ[1] ⊗ Δ[1] : SSet.{max (u + 1) v + 1}) ⟶
    dgKInputInfinity.{u, max (u + 1) v} R)
  (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (F ≫ dgKInputK R) 0 1))
  (hMiddle : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex F 1 0 = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKappaResolvedConeKInput R D I))
  (hRight : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex F 1 1 = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKappaSuspensionKInput R D I))

private lemma canonicalFiber_right :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ (dgConnectiveCanonicalFiberSquare R F hz).square =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ (F ≫ dgKInputK R) := by
  rw [(dgConnectiveCanonicalFiberSquare R F hz).right_edge, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareRightArrow_edge]
  exact SSet.yonedaEquiv.symm_apply_apply _

include Z hMiddle in
/-- 明示相対屋根に条件付きで、元の同じ K 四角形の右辺の始点は、同じ平坦 cone の固定 K 零頂点である。 -/
theorem dgKappaSuspensionConnective_middle_isZero :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (F ≫ dgKInputK R) 1 0) := by
  have he := congrArg ((dgKInputK R).app (Opposite.op ⦋0⦌)) hMiddle
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (F ≫ dgKInputK R) 1 0 = _ at he
  rw [dgKInputK_vertex] at he
  exact he.symm ▸ dgKappaResolvedConeK_isZeroVertex R D I Z

/-- 同じ元の右辺を持つ canonical fiber は、同じ固定 K 懸垂頂点の実 loop 四角形。 -/
def dgKappaSuspensionConnectiveLoopSquare :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopSquare (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKInputSpectrum R (dgKappaSuspensionKInput R D I))) where
  toZeroTriangle := (dgConnectiveCanonicalFiberSquare R F hz).toZeroTriangle
  target_eq := by
    have he := congrArg ((dgKInputK R).app (Opposite.op ⦋0⦌)) hRight
    change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (F ≫ dgKInputK R) 1 1 = _ at he
    rw [dgKInputK_vertex] at he
    have ht : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (dgConnectiveCanonicalFiberSquare R F hz).square 1 1 =
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (F ≫ dgKInputK R) 1 1 := by
      rw [← _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareRightEdge_target, canonicalFiber_right R F hz, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareRightEdge_target]
    exact ht.trans he
  other_zero := by
    have hs : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (dgConnectiveCanonicalFiberSquare R F hz).square 1 0 =
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (F ≫ dgKInputK R) 1 0 := by
      rw [← _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareRightEdge_source, canonicalFiber_right R F hz, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareRightEdge_source]
    exact hs.symm ▸ dgKappaSuspensionConnective_middle_isZero R D I Z F hMiddle
  isPullback := (dgConnectiveCanonicalFiberSquare R F hz).isPullback

variable (A : PerfDGInput.{u, max (u + 1) v} R)
  (hLeft : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex F 0 0 = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A)

/-- 元の厳密 dg 核入力の固定 K から、同じ実懸垂の実 loop 頂点への元の全比較辺。 -/
def dgKappaSuspensionConnectiveLoopComparison :
    SSet.Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKInputSpectrum R A))
      (dgKappaSuspensionConnectiveLoopSquare R D I Z F hz hMiddle hRight).vertex :=
  (dgConnectiveFiberVertexComparison R F hz).ofEq (by
    have he := congrArg ((dgKInputK R).app (Opposite.op ⦋0⦌)) hLeft
    change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (F ≫ dgKInputK R) 0 0 = _ at he
    rw [dgKInputK_vertex] at he
    exact he) rfl

/-- 明示相対屋根に条件付きで、頂点座標を戻しても、元の比較辺の全一単体そのものを保持する。 -/
theorem dgKappaSuspensionConnectiveLoopComparison_edge :
    (dgKappaSuspensionConnectiveLoopComparison R D I Z F hz hMiddle hRight A hLeft).edge =
      (dgConnectiveFiberVertexComparison R F hz).edge := rfl

end SerrePositivity.KST.NonConnective
