module
public import SerrePositivity.KST.SConstruction.PerfectLaxQuotientRectangleLift

/-! # 比較長方形の外周と元の商・完備化の列
概要：同じ長方形の外周に、元の包含と完備化後の商射・零角を厳密に回収する。
方針：指定した上下の合成三角形の対角と、元の左面の包含を使う。
規約：新しい正方形を選び直さない。使われ方：不変量の二つの fiber 列の消去。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories LocalizingInvariants
open scoped Simplicial
namespace PerfectLaxQuotient
variable {C D B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D B}
  (d : PerfectLaxQuotient p q)

/-- 元の全長方形の外周を、Verdier 列の向きへ転置する。 -/
def rawOuterSquare : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} :=
  (β_ (Δ[1] : SSet.{u + 1}) Δ[1]).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare d.rawRectangle.diagram 1

/-- 外周の下辺は、元の包含そのもの。 -/
lemma rawOuterSquare_bottom : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ d.rawOuterSquare =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow d.inclusion).edge := by
  rw [rawOuterSquare, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.square_transpose_bottom, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare_outer_leftEdge,
    d.rawRectangle.left_eq, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.square_transpose_left, d.universalRawSquare_edges.1]

/-- 外周の右辺は、元の実商と完備化の合成そのもの。 -/
lemma rawOuterSquare_right : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ d.rawOuterSquare =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow d.sequence.projection).edge := by
  rw [rawOuterSquare, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.square_transpose_right, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare_topEdge,
    d.rawRectangle.top_eq, stdSimplex.δ_comp_yonedaEquiv_symm,
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalDifferenceSquare.quotientCompositionTriangle p q d.sequence.projection).d₁]
  rfl

/-- 外周の左辺は、元の左端から元の零圏への射。 -/
lemma rawOuterSquare_left : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ d.rawOuterSquare =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory d.left)).edge := by
  rw [rawOuterSquare, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.square_transpose_left, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare_bottomEdge,
    d.rawRectangle.bottom_eq, stdSimplex.δ_comp_yonedaEquiv_symm,
    (LaxUniversalDifference.zeroCompositionTriangle p q d.inclusion d.sequence.projection).d₁]

/-- 外周の四角は、元の左端・lax 圏・完備化先と元の零圏。 -/
lemma rawOuterSquare_vertices :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex d.rawOuterSquare 0 0 = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex d.left ∧
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex d.rawOuterSquare 1 0 = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex (laxCategory p q) ∧
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex d.rawOuterSquare 1 1 = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex d.sequence.right ∧
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex d.rawOuterSquare 0 1 = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory.{u} := by
  constructor
  · have h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareBottomEdge_source d.rawOuterSquare
    rw [d.rawOuterSquare_bottom, Equiv.apply_symm_apply, (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow d.inclusion).src_eq] at h
    exact h.symm
  constructor
  · have h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareBottomEdge_target d.rawOuterSquare
    rw [d.rawOuterSquare_bottom, Equiv.apply_symm_apply, (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow d.inclusion).tgt_eq] at h
    exact h.symm
  constructor
  · have h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareRightEdge_target d.rawOuterSquare
    rw [d.rawOuterSquare_right, Equiv.apply_symm_apply,
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow d.sequence.projection).tgt_eq] at h
    exact h.symm
  · have h := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareLeftEdge_target d.rawOuterSquare
    rw [d.rawOuterSquare_left, Equiv.apply_symm_apply,
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory d.left)).tgt_eq] at h
    exact h.symm

/-- Cat^perf の同じ長方形の外周。 -/
def outerSquare : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ perfectStableInfinity.{u} :=
  (β_ (Δ[1] : SSet.{u + 1}) Δ[1]).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare d.rectangleDiagram 1

/-- 外周の持ち上げも、元の安定圏値の全外周を回収する。 -/
lemma outerSquare_inclusion : d.outerSquare ≫ perfectStableInfinityInclusion =
    d.rawOuterSquare := by
  change _ ≫ (_ ≫ (d.rectangleDiagram ≫ perfectStableInfinityInclusion)) = _
  rw [d.rectangleDiagram_inclusion]
  rfl

/-- 同じ外周は、元の実商と完備化を持つ列の coherent 提示そのもの。 -/
def outerDiagram : PerfectVerdierDiagram.{u} where
  toPerfectVerdierSequence := d.sequence
  square := d.outerSquare
  left_eq := by
    apply Subtype.ext
    exact d.rawOuterSquare_vertices.1
  middle_eq := by
    apply Subtype.ext
    exact d.rawOuterSquare_vertices.2.1
  right_eq := by
    apply Subtype.ext
    exact d.rawOuterSquare_vertices.2.2.1
  bottom_edge := by
    rw [d.outerSquare_inclusion]
    exact d.rawOuterSquare_bottom
  right_edge := by
    rw [d.outerSquare_inclusion]
    exact d.rawOuterSquare_right
  zero_corner := by
    change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex d.rawOuterSquare 0 1))
    rw [d.rawOuterSquare_vertices.2.2.2, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject_vertex]
    exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory_isZero

end PerfectLaxQuotient
end SerrePositivity.KST.SConstruction
