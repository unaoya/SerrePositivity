module
public import SerrePositivity.KST.SConstruction.PerfectLaxQuotientProductNormalization
public import SerrePositivity.KST.LocalizingInvariants.BinaryProductCospanNormalized

/-! # 元の四辺を固定した実積正方形と二脚の pullback 入力
概要：同じ境界変形で固定した実 BF 四辺を回収し、積射・対角の入力の向きへ移す。
方針：元の境界の等式を読み、同じ全正方形を転置する。
規約：元の二脚・射対を固定する。使われ方：Cat^perf の二脚の実 pullback 錐。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet Spectra
open SerrePositivity.InfinityCategories LocalizingInvariants
open scoped Simplicial
namespace PerfectLaxQuotient
local instance productBoundarySimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
variable {C D B : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} {p : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap C B} {q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap D B}
  (d : PerfectLaxQuotient p q)
  {F : perfectStableInfinity.{u} ⟶ Sp.{u}} (hF : IsPerfectLocalizingInvariant F)

/-- 同じ境界変形の bottom 辺は、元の同じ実 BF 射そのもの。 -/
lemma normalizedProductSquare_bottom : squareBottomEdge ≫ d.normalizedProductSquare hF =
    SSet.yonedaEquiv.symm (coherentNerveEdge (d.valueProductInclusion F)).edge :=
  _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquareFrame.square_bottom_of_boundary _ (d.normalizedProductSquare_boundary hF)

/-- 同じ境界変形の top 辺は、元の同じ実 BF 射そのもの。 -/
lemma normalizedProductSquare_top : squareTopEdge ≫ d.normalizedProductSquare hF =
    SSet.yonedaEquiv.symm (coherentNerveEdge (Binary.lift
      (𝟙 (perfectInvariantSpectrum F d.sequence.rightVertex))
      (𝟙 (perfectInvariantSpectrum F d.sequence.rightVertex)))).edge :=
  _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquareFrame.square_top_of_boundary _ (d.normalizedProductSquare_boundary hF)

/-- 同じ境界変形の left 辺は、元の同じ実 BF 射そのもの。 -/
lemma normalizedProductSquare_left : squareLeftEdge ≫ d.normalizedProductSquare hF =
    SSet.yonedaEquiv.symm (coherentNerveEdge (d.valueKernelMap F)).edge :=
  _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquareFrame.square_left_of_boundary _ (d.normalizedProductSquare_boundary hF)

/-- 同じ境界変形の right 辺は、元の同じ実 BF 射そのもの。 -/
lemma normalizedProductSquare_right : squareRightEdge ≫ d.normalizedProductSquare hF =
    SSet.yonedaEquiv.symm (coherentNerveEdge (d.productLegMap F)).edge :=
  _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquareFrame.square_right_of_boundary _ (d.normalizedProductSquare_boundary hF)

/-- 同じ全引き戻し正方形を、積射・対角の cospan 入力の向きへ転置する。 -/
def productCospanInputSquare : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ Sp.{u} :=
  (β_ (Δ[1] : SSet.{u + 1}) Δ[1]).hom ≫ d.normalizedProductSquare hF

/-- 同じ転置後の全正方形も、実 Sp の引き戻し。 -/
lemma productCospanInputSquare_isPullback : IsPullbackSquare (d.productCospanInputSquare hF) :=
  (isPullbackSquare_iff_transpose _).mp (d.normalizedProductSquare_isPullback hF)

/-- 同じ入力正方形の上辺は、元の完備化後の二脚の実積射。 -/
lemma productCospanInputSquare_top : squareTopEdge ≫ d.productCospanInputSquare hF =
    SSet.yonedaEquiv.symm
      (coherentNerveEdge (Binary.map (d.valueCLeg F) (d.valueDLeg F))).edge := by
  rw [productCospanInputSquare, _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.square_transpose_top, d.normalizedProductSquare_right]
  rfl

/-- 同じ入力正方形の右辺は、元の完備化先の値の実対角。 -/
lemma productCospanInputSquare_right : squareRightEdge ≫ d.productCospanInputSquare hF =
    SSet.yonedaEquiv.symm (coherentNerveEdge
      (BinaryGraph.diagonal (perfectInvariantSpectrum F d.sequence.rightVertex))).edge := by
  rw [productCospanInputSquare, _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.square_transpose_right, d.normalizedProductSquare_top]
  rfl

/-- 同じ入力正方形の左辺は、元の C・D への同じ実射対。 -/
lemma productCospanInputSquare_left : squareLeftEdge ≫ d.productCospanInputSquare hF =
    SSet.yonedaEquiv.symm
      (coherentNerveEdge (Binary.lift (d.valueCSource F) (d.valueDSource F))).edge := by
  rw [productCospanInputSquare, _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.square_transpose_left, d.normalizedProductSquare_bottom]
  rfl

end PerfectLaxQuotient
end SerrePositivity.KST.SConstruction
