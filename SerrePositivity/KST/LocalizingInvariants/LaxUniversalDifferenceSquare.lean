module

public import SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifferenceKernel
public import SerrePositivity.KST.LocalizingInvariants.IdentityLaxVerdier
public import SerrePositivity.KST.LocalizingInvariants.ExactMapPinchedPath
public import SerrePositivity.KST.LocalizingInvariants.PathComparisonSquare

/-!
概要：一般商の列と恒等 lax 差の列を結ぶ、指定比較道を保持した実正方形。
方針：包含上の対角同型を合成三角形へ移し、元の二つの合成三角形を貼る。
規約：四辺は元の完全関手。極限性は後続工程。使われ方：Verdier 長方形の左面。
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

def kernelMap : A ⟶ Q := ⟨i.hom ≫ first p q r, inferInstance⟩

def inclusionComposite : A ⟶ laxCategory (𝟙 Q) (𝟙 Q) := i ≫ exactLift p q r

def diagonalComposite : A ⟶ laxCategory (𝟙 Q) (𝟙 Q) :=
  kernelMap p q i r ≫ IdentityLax.exactDiagonal Q

def quotientComposite : laxCategory p q ⟶ Q :=
  exactLift p q r ≫ exactLaxDifference (𝟙 Q) (𝟙 Q)

def lower : SSet.Edge.CompStruct (stableArrow i) (stableArrow (exactLift p q r))
    (stableArrow (inclusionComposite p q i r)) :=
  coherentNerveCompStruct (C := StableQCat.{u}) i (exactLift p q r)

def upper : SSet.Edge.CompStruct (stableArrow (kernelMap p q i r))
    (stableArrow (IdentityLax.exactDiagonal Q))
    (stableArrow (diagonalComposite p q i r)) :=
  coherentNerveCompStruct (C := StableQCat.{u}) (kernelMap p q i r) (IdentityLax.exactDiagonal Q)

def diagonalComparisonTriangle : SSet.Edge.CompStruct (SSet.Edge.id (stableVertex A))
    (stableArrow (inclusionComposite p q i r))
    (stableArrow (diagonalComposite p q i r)) :=
  exactMapComparisonTriangle (F := diagonalComposite p q i r)
    (G := inclusionComposite p q i r) (inclusionDiagonalIso p q i r h).symm

def comparisonSquare : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ StableInfinity.{u} :=
  PathComparisonSquare.square (lower p q i r) (upper p q i r)
    (diagonalComparisonTriangle p q i r h)

lemma comparisonSquare_bottom : squareBottomEdge ≫ comparisonSquare p q i r h =
    SSet.yonedaEquiv.symm (stableArrow i).edge :=
  PathComparisonSquare.square_bottom _ _ _

lemma comparisonSquare_right : squareRightEdge ≫ comparisonSquare p q i r h =
    SSet.yonedaEquiv.symm (stableArrow (exactLift p q r)).edge :=
  PathComparisonSquare.square_right _ _ _

lemma comparisonSquare_left : squareLeftEdge ≫ comparisonSquare p q i r h =
    SSet.yonedaEquiv.symm (stableArrow (kernelMap p q i r)).edge :=
  PathComparisonSquare.square_left _ _ _

lemma comparisonSquare_top : squareTopEdge ≫ comparisonSquare p q i r h =
    SSet.yonedaEquiv.symm (stableArrow (IdentityLax.exactDiagonal Q)).edge :=
  PathComparisonSquare.square_top _ _ _

def quotientCompositionTriangle : SSet.Edge.CompStruct (stableArrow (exactLift p q r))
    (stableArrow (exactLaxDifference (𝟙 Q) (𝟙 Q))) (stableArrow r) := by
  let s := coherentNerveCompStruct (C := StableQCat.{u})
    (exactLift p q r) (exactLaxDifference (𝟙 Q) (𝟙 Q))
  have e : FunctorIso (quotientComposite p q r).hom r.hom :=
    differenceIso p q r
  exact (compositionDiagonalTransport s (exactMapComparisonTriangle (F := r)
    (G := quotientComposite p q r) e.symm)).triangle

end SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference
