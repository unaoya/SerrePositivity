module

public import SerrePositivity.KST.Spectra.SpectrumCircleSquareVertices
public import SerrePositivity.InfinityCategories.Stable.SuspensionSquare

/-!
概要：円評価四角形の cospan を、二本とも元の一点スペクトルからの射へ厳密に固定する。
方針：一点からの通常の射の一意性を coherent 辺の同値へ移し、ホーンの二辺で照合する。
規約：錐のホモトピー情報を保持した cast のみ。使われ方：元の固定図式上の極限性の検査。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.InfinityCategories.HomotopyLimits
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
local instance circleSquareCospanSpectrumSimplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory

/-- 一点スペクトルから指定した BF 対象への coherent な辺は一意。 -/
lemma fromPoint_coherentEdge_unique (Y : OmegaSpectrum.{u})
    (e : Sp.{u}.Edge (coherentNerveVertex spectrumPoint) (coherentNerveVertex Y)) :
    e = coherentNerveEdge (fromPoint Y) := by
  apply (coherentNerveEdgeEquiv spectrumPoint Y).injective
  exact point_isInitial.hom_ext _ _

/-- 始点・終点を指定した区間図式も、一点からの元の射の coherent な表示へ厳密一致。 -/
lemma fromPoint_interval_unique (Y : OmegaSpectrum.{u}) (f : (Δ[1] : SSet.{u + 1}) ⟶ Sp.{u})
    (hs : Sp.{u}.δ 1 (SSet.yonedaEquiv f) = pointZeroVertex.vertex)
    (ht : Sp.{u}.δ 0 (SSet.yonedaEquiv f) = coherentNerveVertex Y) :
    f = SSet.yonedaEquiv.symm (coherentNerveEdge (fromPoint Y)).edge := by
  let e : Sp.{u}.Edge (coherentNerveVertex spectrumPoint) (coherentNerveVertex Y) :=
    SSet.Edge.mk (SSet.yonedaEquiv f) hs ht
  apply SSet.yonedaEquiv.injective
  erw [Equiv.apply_symm_apply]
  exact congrArg (fun a ↦ a.edge) (fromPoint_coherentEdge_unique Y e)

/-- 点ごとの円評価四角形の右辺は、元の一点からの射そのもの。 -/
lemma nativeCircleEvaluationSquare_right (z : Sp.{u} _⦋0⦌) :
    squareRightEdge ≫ nativeCircleEvaluationSquare z = SSet.yonedaEquiv.symm
      (coherentNerveEdge
        (fromPoint (nativeCotensorInput PointedSimplicialSet.circle z).val)).edge := by
  apply fromPoint_interval_unique
  · rw [squareRightEdge_source]
    exact nativeCircleEvaluationSquare_zeroCorner z 1
  · rw [squareRightEdge_target, nativeCircleEvaluationSquare_target]

/-- 円評価四角形の上辺の終点は、右上の頂点。 -/
lemma circleSquare_top_target (z : Sp.{u} _⦋0⦌) :
    Sp.{u}.δ 0 (SSet.yonedaEquiv (squareTopEdge ≫ nativeCircleEvaluationSquare z)) =
      squareVertex (nativeCircleEvaluationSquare z) 1 1 := by
  rw [← stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc, SSet.yonedaEquiv_comp]
  apply congrArg (fun s : ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1]) _⦋0⦌ ↦
    (nativeCircleEvaluationSquare z).app _ s)
  apply Prod.ext <;> decide

/-- 点ごとの円評価四角形の上辺も、同じ元の一点からの射そのもの。 -/
lemma nativeCircleEvaluationSquare_top (z : Sp.{u} _⦋0⦌) :
    squareTopEdge ≫ nativeCircleEvaluationSquare z = SSet.yonedaEquiv.symm
      (coherentNerveEdge
        (fromPoint (nativeCotensorInput PointedSimplicialSet.circle z).val)).edge := by
  apply fromPoint_interval_unique
  · rw [squareTopEdge_source]
    exact nativeCircleEvaluationSquare_zeroCorner z 0
  · rw [circleSquare_top_target, nativeCircleEvaluationSquare_target]

/-- 二本とも実際の一点 BF スペクトルからの射である、固定された loop の cospan。 -/
def pointLoopCospan (Y : OmegaSpectrum.{u}) : (horn 2 2 : SSet.{u + 1}) ⟶ Sp.{u} :=
  edgeCospan (coherentNerveEdge (fromPoint Y)).toTruncated
    (coherentNerveEdge (fromPoint Y)).toTruncated

/-- 円評価四角形の実際の cospan は、逆射が選んだ入力の固定された cospan に一致。 -/
lemma nativeCircleEvaluationSquare_cospan (z : Sp.{u} _⦋0⦌) :
    pullbackCospan (nativeCircleEvaluationSquare z) =
      pointLoopCospan (nativeCotensorInput PointedSimplicialSet.circle z).val := by
  apply horn₂₂.isPushout.hom_ext
  · rw [pullbackCospan, ← Category.assoc, cospanSquareBoundary_rightEdge,
      nativeCircleEvaluationSquare_right, pointLoopCospan]
    exact (edgeCospan_left _ _).symm
  · rw [pullbackCospan, ← Category.assoc, cospanSquareBoundary_topEdge,
      nativeCircleEvaluationSquare_top, pointLoopCospan]
    exact (edgeCospan_right _ _).symm

/-- 円評価四角形の全ホモトピー情報を保持した、固定された loop 図式上の実際の錐。 -/
def nativeCirclePointLoopCone (z : Sp.{u} _⦋0⦌) :
    JoinCone (pointLoopCospan (nativeCotensorInput PointedSimplicialSet.circle z).val) :=
  (pullbackCone (nativeCircleEvaluationSquare z)).cast (nativeCircleEvaluationSquare_cospan z)

end SerrePositivity.KST.Spectra.OmegaSpectrum
