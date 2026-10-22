module
public import SerrePositivity.KST.SConstruction.PerfectLaxQuotientUniversalLift
public import SerrePositivity.KST.SConstruction.PerfectIdentityLaxSequence
public import SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifferenceRectangle

/-! # 完備化後の元の商を保持する比較長方形
概要：指定した普遍差の比較正方形と恒等 lax 差の正方形を、同じ三角形で貼る。
方針：元の零合成・完備化後の商射への比較三角形を固定して内ホーンを充填する。
規約：完備化後の射に厳密商性を課さない。使われ方：Cat^perf 内の pullback 消去則。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories LocalizingInvariants
open scoped Simplicial
namespace PerfectLaxQuotient
variable {C D B : StableCategory.{u}} {p : ExactMap C B} {q : ExactMap D B}
  (d : PerfectLaxQuotient p q)

/-- 普遍差の比較と恒等差の実正方形を、元の両合成三角形を保って貼る。 -/
def rawRectangle : SquarePastingRectangle
    ((β_ (Δ[1] : SSet.{u + 1}) Δ[1]).hom ≫ d.universalRawSquare)
    ((β_ (Δ[1] : SSet.{u + 1}) Δ[1]).hom ≫
      perfectVerdierRawSquare
        (perfectIdentityLaxSequence d.sequence.right d.sequence.right_complete))
    (SSet.yonedaEquiv.symm (LaxUniversalDifference.zeroCompositionTriangle p q
      d.inclusion d.sequence.projection).simplex)
    (SSet.yonedaEquiv.symm (LaxUniversalDifference.quotientCompositionTriangle p q
      d.sequence.projection).simplex) := by
  have hc := d.universalRawSquare_edges
  have hi := perfectIdentityLaxRawSquare_edges d.sequence.right d.sequence.right_complete
  apply Classical.choice
  apply nonempty_squarePastingRectangle
  · rw [square_transpose_right, square_transpose_left, hc.2.1, hi.1]
  · rw [square_transpose_bottom, hc.2.2.1, stdSimplex.δ_comp_yonedaEquiv_symm,
      (LaxUniversalDifference.zeroCompositionTriangle p q d.inclusion d.sequence.projection).d₂]
  · rw [square_transpose_bottom, hi.2.2.1, stdSimplex.δ_comp_yonedaEquiv_symm,
      (LaxUniversalDifference.zeroCompositionTriangle p q d.inclusion d.sequence.projection).d₀]
  · rw [square_transpose_top, hc.2.2.2, stdSimplex.δ_comp_yonedaEquiv_symm,
      (LaxUniversalDifference.quotientCompositionTriangle p q d.sequence.projection).d₂]
  · rw [square_transpose_top, hi.2.2.2, stdSimplex.δ_comp_yonedaEquiv_symm,
      (LaxUniversalDifference.quotientCompositionTriangle p q d.sequence.projection).d₀]

end PerfectLaxQuotient
end SerrePositivity.KST.SConstruction
