module

public import SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifferenceSquare
public import SerrePositivity.KST.LocalizingInvariants.SquarePastingRectangle
public import SerrePositivity.KST.LocalizingInvariants.SquareTransposeEdges
public import SerrePositivity.KST.LocalizingInvariants.VerdierPresentation

/-!
概要：一般商の比較正方形を恒等 lax 差の Verdier 正方形へ貼った実長方形。
方針：零圏への合成と元の商 r への合成三角形を指定して内ホーンを充填する。
規約：元の包含・商の辺を外周に保持。使われ方：不変量の pullback 性の消去則。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference
variable {C D E A Q : StableCategory.{u}} (p : ExactMap C E) (q : ExactMap D E)
  (i : ExactMap A (laxCategory p q)) (r : ExactMap (laxCategory p q) Q)
  (h : IsVerdierSequence i r)

def identityDiagram (Q : StableCategory.{u}) : VerdierDiagram.{u} :=
  (IdentityLax.verdierSequence Q).presentation

lemma identityDiagram_bottom (Q : StableCategory.{u}) :
    squareBottomEdge ≫ (identityDiagram Q).square =
      SSet.yonedaEquiv.symm (stableArrow (IdentityLax.exactDiagonal Q)).edge :=
  (identityDiagram Q).bottom_edge

lemma identityDiagram_right (Q : StableCategory.{u}) :
    squareRightEdge ≫ (identityDiagram Q).square =
      SSet.yonedaEquiv.symm (stableArrow (exactLaxDifference (𝟙 Q) (𝟙 Q))).edge :=
  (identityDiagram Q).right_edge

lemma identityDiagram_left (Q : StableCategory.{u}) :
    squareLeftEdge ≫ (identityDiagram Q).square =
      SSet.yonedaEquiv.symm (stableArrow (toZeroCategory Q)).edge :=
  (IdentityLax.verdierSequence Q).presentation_left

def zeroComposite : A ⟶ zeroCategory.{u} := kernelMap p q i r ≫ toZeroCategory Q

def zeroCompositeIso : FunctorIso (zeroComposite p q i r).hom (toZeroCategory A).hom :=
  zeroDiagramFunctorIso _ _ (fun _ => zeroCategory_isZero _) (fun _ => zeroCategory_isZero _)

def zeroCompositionTriangle : SSet.Edge.CompStruct (stableArrow (kernelMap p q i r))
    (stableArrow (toZeroCategory Q)) (stableArrow (toZeroCategory A)) := by
  let s := coherentNerveCompStruct (C := StableQCat.{u}) (kernelMap p q i r) (toZeroCategory Q)
  exact (compositionDiagonalTransport s (exactMapComparisonTriangle (F := toZeroCategory A)
    (G := zeroComposite p q i r) (zeroCompositeIso p q i r).symm)).triangle

def rectangle : SquarePastingRectangle
    ((β_ (Δ[1] : SSet.{u + 1}) Δ[1]).hom ≫ comparisonSquare p q i r h)
    ((β_ (Δ[1] : SSet.{u + 1}) Δ[1]).hom ≫ (identityDiagram Q).square)
    (SSet.yonedaEquiv.symm (zeroCompositionTriangle p q i r).simplex)
    (SSet.yonedaEquiv.symm (quotientCompositionTriangle p q r).simplex) := by
  apply Classical.choice
  apply nonempty_squarePastingRectangle
  · rw [square_transpose_right, square_transpose_left,
      comparisonSquare_top, identityDiagram_bottom]
  · rw [square_transpose_bottom, comparisonSquare_left, stdSimplex.δ_comp_yonedaEquiv_symm,
      (zeroCompositionTriangle p q i r).d₂]
  · rw [square_transpose_bottom, identityDiagram_left,
      stdSimplex.δ_comp_yonedaEquiv_symm, (zeroCompositionTriangle p q i r).d₀]
  · rw [square_transpose_top, comparisonSquare_right, stdSimplex.δ_comp_yonedaEquiv_symm,
      (quotientCompositionTriangle p q r).d₂]
  · rw [square_transpose_top, identityDiagram_right, stdSimplex.δ_comp_yonedaEquiv_symm,
      (quotientCompositionTriangle p q r).d₀]

end SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference
