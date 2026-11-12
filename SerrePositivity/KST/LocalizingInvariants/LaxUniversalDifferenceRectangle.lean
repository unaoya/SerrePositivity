module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalDifferenceSquare
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.SquarePastingRectangle
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareTransposeEdges
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
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference
variable {C D E A Q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)
  (i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A (laxCategory p q)) (r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (laxCategory p q) Q)
  (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i r)

def identityDiagram (Q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u} :=
  (_root_.SerrePositivity.KST.LocalizingInvariants.VerdierSequence.presentation (IdentityLax.verdierSequence Q))

lemma identityDiagram_bottom (Q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ (identityDiagram Q).square =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (IdentityLax.exactDiagonal Q)).edge :=
  (identityDiagram Q).bottom_edge

lemma identityDiagram_right (Q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ (identityDiagram Q).square =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (exactLaxDifference (𝟙 Q) (𝟙 Q))).edge :=
  (identityDiagram Q).right_edge

lemma identityDiagram_left (Q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ (identityDiagram Q).square =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory Q)).edge :=
  (_root_.SerrePositivity.KST.LocalizingInvariants.VerdierSequence.presentation_left (IdentityLax.verdierSequence Q))

def zeroComposite : A ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory.{u} := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalDifferenceSquare.kernelMap p q i r ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory Q

def zeroCompositeIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (zeroComposite p q i r).hom (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory A).hom :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroDiagramFunctorIso _ _ (fun _ => _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory_isZero _) (fun _ => _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory_isZero _)

def zeroCompositionTriangle : SSet.Edge.CompStruct (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalDifferenceSquare.kernelMap p q i r))
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory Q)) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory A)) := by
  let s := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalDifferenceSquare.kernelMap p q i r) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory Q)
  exact (compositionDiagonalTransport s (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.exactMapComparisonTriangle (F := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory A)
    (G := zeroComposite p q i r) (zeroCompositeIso p q i r).symm)).triangle

def rectangle : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.SquarePastingRectangle
    ((β_ (Δ[1] : SSet.{u + 1}) Δ[1]).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalDifferenceSquare.comparisonSquare p q i r h)
    ((β_ (Δ[1] : SSet.{u + 1}) Δ[1]).hom ≫ (identityDiagram Q).square)
    (SSet.yonedaEquiv.symm (zeroCompositionTriangle p q i r).simplex)
    (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalDifferenceSquare.quotientCompositionTriangle p q r).simplex) := by
  apply Classical.choice
  apply _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.nonempty_squarePastingRectangle
  · rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.square_transpose_right, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.square_transpose_left,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalDifferenceSquare.comparisonSquare_top, identityDiagram_bottom]
  · rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.square_transpose_bottom, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalDifferenceSquare.comparisonSquare_left, stdSimplex.δ_comp_yonedaEquiv_symm,
      (zeroCompositionTriangle p q i r).d₂]
  · rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.square_transpose_bottom, identityDiagram_left,
      stdSimplex.δ_comp_yonedaEquiv_symm, (zeroCompositionTriangle p q i r).d₀]
  · rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.square_transpose_top, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalDifferenceSquare.comparisonSquare_right, stdSimplex.δ_comp_yonedaEquiv_symm,
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalDifferenceSquare.quotientCompositionTriangle p q r).d₂]
  · rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.square_transpose_top, identityDiagram_right, stdSimplex.δ_comp_yonedaEquiv_symm,
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalDifferenceSquare.quotientCompositionTriangle p q r).d₀]

end SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference
