module
public import SerrePositivity.KST.NonConnective.DGKappaSuspensionKRoof
public import SerrePositivity.KST.Fibration.DGRelativeFiberComparisonVertices
public import SerrePositivity.KST.Spectra.SpectrumLoopSquares

/-!
概要：同じ dg 懸垂の実相対四角形から、固定 K の元の頂点を実 loop 頂点へ送る。
方針：K-6 の同じ canonical fiber を使い、同じ cone の固定 K 零性で loop 四角形とする。
規約：元の相対四角形は明示入力。元の右辺を保持し、K の局所化性を仮定しない。
使われ方：反復懸垂の構造射。実相対四角形の供給後に元の各段へ特殊化する。
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

local instance : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory
local instance (X Y : OmegaSpectrum.{w}) :
    KanComplex (SimplicialCategory.sHom X Y) := OmegaSpectrum.mappingSpace_kanComplex X Y

variable (R : Type u) [CommRing R] (D : Type (max (u + 1) v)) [DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ) (Z : DGKappaZeroInput R D I)
  (d : RelativeVerdierDiagram (dgKInputNu.{u, max (u + 1) v} R))
  (hMiddle : squareVertex d.square 1 0 = coherentNerveVertex (dgKappaResolvedConeKInput R D I))
  (hRight : squareVertex d.square 1 1 = coherentNerveVertex (dgKappaSuspensionKInput R D I))

private lemma canonicalFiber_right :
    squareRightEdge ≫ (dgRelativeCanonicalFiberSquare R d).square =
      squareRightEdge ≫ (d.square ≫ dgKInputK R) := by
  rw [(dgRelativeCanonicalFiberSquare R d).right_edge, squareRightArrow_edge]
  exact SSet.yonedaEquiv.symm_apply_apply _

include Z hMiddle in
/-- 元の同じ K 四角形の右辺の始点は、同じ平坦 cone の固定 K 零頂点である。 -/
theorem dgKappaSuspensionRelative_middle_isZero :
    IsZeroVertex (squareVertex (d.square ≫ dgKInputK R) 1 0) := by
  have he := congrArg ((dgKInputK R).app (Opposite.op ⦋0⦌)) hMiddle
  change squareVertex (d.square ≫ dgKInputK R) 1 0 = _ at he
  rw [dgKInputK_vertex] at he
  exact he.symm ▸ dgKappaResolvedConeK_isZeroVertex R D I Z

/-- 同じ元の右辺を持つ canonical fiber は、同じ固定 K 懸垂頂点の実 loop 四角形。 -/
def dgKappaSuspensionLoopSquare :
    LoopSquare (coherentNerveVertex (dgKInputSpectrum R (dgKappaSuspensionKInput R D I))) where
  toZeroTriangle := (dgRelativeCanonicalFiberSquare R d).toZeroTriangle
  target_eq := by
    have he := congrArg ((dgKInputK R).app (Opposite.op ⦋0⦌)) hRight
    change squareVertex (d.square ≫ dgKInputK R) 1 1 = _ at he
    rw [dgKInputK_vertex] at he
    have ht : squareVertex (dgRelativeCanonicalFiberSquare R d).square 1 1 =
        squareVertex (d.square ≫ dgKInputK R) 1 1 := by
      rw [← squareRightEdge_target, canonicalFiber_right R d, squareRightEdge_target]
    exact ht.trans he
  other_zero := by
    have hs : squareVertex (dgRelativeCanonicalFiberSquare R d).square 1 0 =
        squareVertex (d.square ≫ dgKInputK R) 1 0 := by
      rw [← squareRightEdge_source, canonicalFiber_right R d, squareRightEdge_source]
    exact hs.symm ▸ dgKappaSuspensionRelative_middle_isZero R D I Z d hMiddle
  isPullback := (dgRelativeCanonicalFiberSquare R d).isPullback

variable (A : PerfDGInput.{u, max (u + 1) v} R)
  (hLeft : squareVertex d.square 0 0 = coherentNerveVertex A)

/-- 元の厳密 dg 核入力の固定 K から、同じ実懸垂の実 loop 頂点への元の全比較辺。 -/
def dgKappaSuspensionLoopComparison :
    SSet.Edge (coherentNerveVertex (dgKInputSpectrum R A))
      (dgKappaSuspensionLoopSquare R D I Z d hMiddle hRight).vertex :=
  (dgRelativeFiberVertexComparison R d).ofEq (by
    have he := congrArg ((dgKInputK R).app (Opposite.op ⦋0⦌)) hLeft
    change squareVertex (d.square ≫ dgKInputK R) 0 0 = _ at he
    rw [dgKInputK_vertex] at he
    exact he) rfl

/-- 頂点座標を戻しても、元の比較辺の全一単体そのものを保持する。 -/
theorem dgKappaSuspensionLoopComparison_edge :
    (dgKappaSuspensionLoopComparison R D I Z d hMiddle hRight A hLeft).edge =
      (dgRelativeFiberVertexComparison R d).edge := rfl

/-- 同じ実 loop 比較が可逆であることは、元の相対 K 四角形の引き戻し性と同値。 -/
theorem dgKappaSuspensionLoopComparison_isInvertible_iff :
    IsInvertibleEdge (dgKappaSuspensionLoopComparison R D I Z d hMiddle hRight A hLeft) ↔
      IsPullbackSquare (d.square ≫ dgKInputK R) := by
  exact (isInvertibleEdge_congr (dgKappaSuspensionLoopComparison_edge R D I Z d
    hMiddle hRight A hLeft)).trans
      (dgRelativeK_isPullback_iff_fiberVertexComparison_isInvertible R d).symm

end SerrePositivity.KST.NonConnective
