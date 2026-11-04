module

public import SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeLegComparison
public import SerrePositivity.InfinityCategories.Stable.Exact.ExactMapPinchedPath
public import SerrePositivity.KST.LocalizingInvariants.PathComparisonSquare
public import SerrePositivity.KST.LocalizingInvariants.ValueHomotopy

/-!
概要：元の cofiber・suspension 比較の道を保つ StableInfinity 内の二脚の正方形。
方針：完全関手の比較の道を指定二単体として対角移送し、二つの合成三角形を貼る。
規約：E の像も同じ全図式。極限性は未主張。使われ方：実 product fiber との比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.LaxQuotientRelativeSquare
local instance : SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
variable {C D E A Q : StableCategory.{u}} (p : ExactMap C E) (q : ExactMap D E)
  (i : ExactMap A (laxCategory p q)) (r : ExactMap (laxCategory p q) Q)
  (h : IsVerdierSequence i r)

def cSource : A ⟶ C := i ≫ laxFst p q
def dSource : A ⟶ D := i ≫ laxSnd p q
def cComposite : A ⟶ Q := cSource p q i ≫ laxQuotientCLeg p q r
def dComposite : A ⟶ Q := dSource p q i ≫ laxQuotientDLeg p q r

def legsIso : FunctorIso (cComposite p q i r).hom (dComposite p q i r).hom := by
  change FunctorIso
    ((i.hom ≫ (laxFst p q).hom) ≫ (laxQuotientCLeg p q r).hom)
    ((i.hom ≫ (laxSnd p q).hom) ≫ (laxQuotientDLeg p q r).hom)
  exact laxQuotientRelativeLegsIso p q i r h

def lower : SSet.Edge.CompStruct (stableArrow (cSource p q i))
    (stableArrow (laxQuotientCLeg p q r)) (stableArrow (cComposite p q i r)) :=
  coherentNerveCompStruct (C := StableQCat.{u}) (cSource p q i) (laxQuotientCLeg p q r)

def upper : SSet.Edge.CompStruct (stableArrow (dSource p q i))
    (stableArrow (laxQuotientDLeg p q r)) (stableArrow (dComposite p q i r)) :=
  coherentNerveCompStruct (C := StableQCat.{u}) (dSource p q i) (laxQuotientDLeg p q r)

def comparisonTriangle : SSet.Edge.CompStruct (SSet.Edge.id (stableVertex A))
    (stableArrow (cComposite p q i r)) (stableArrow (dComposite p q i r)) :=
  exactMapComparisonTriangle (legsIso p q i r h).symm

def square : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ StableInfinity.{u} :=
  PathComparisonSquare.square (lower p q i r) (upper p q i r) (comparisonTriangle p q i r h)

lemma square_bottom : squareBottomEdge ≫ square p q i r h =
    SSet.yonedaEquiv.symm (stableArrow (cSource p q i)).edge :=
  PathComparisonSquare.square_bottom _ _ _

lemma square_right : squareRightEdge ≫ square p q i r h =
    SSet.yonedaEquiv.symm (stableArrow (laxQuotientCLeg p q r)).edge :=
  PathComparisonSquare.square_right _ _ _

lemma square_left : squareLeftEdge ≫ square p q i r h =
    SSet.yonedaEquiv.symm (stableArrow (dSource p q i)).edge :=
  PathComparisonSquare.square_left _ _ _

lemma square_top : squareTopEdge ≫ square p q i r h =
    SSet.yonedaEquiv.symm (stableArrow (laxQuotientDLeg p q r)).edge :=
  PathComparisonSquare.square_top _ _ _

lemma square_upper : squareTriangle 0 ≫ square p q i r h =
    SSet.yonedaEquiv.symm (upper p q i r).simplex :=
  PathComparisonSquare.square_upper _ _ _

lemma square_lower : squareTriangle 1 ≫ square p q i r h =
    SSet.yonedaEquiv.symm (compositionDiagonalTransport
      (lower p q i r) (comparisonTriangle p q i r h)).triangle.simplex :=
  PathComparisonSquare.square_lower _ _ _

def valueSquare (Φ : StableInfinity.{u} ⟶ Sp.{u}) :
    (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ Sp.{u} := square p q i r h ≫ Φ

lemma valueSquare_bottom (Φ : StableInfinity.{u} ⟶ Sp.{u}) :
    squareBottomEdge ≫ valueSquare p q i r h Φ =
      SSet.yonedaEquiv.symm (coherentNerveEdge (valueMap Φ (cSource p q i))).edge := by
  rw [valueSquare, ← Category.assoc, square_bottom,
    SSet.yonedaEquiv_symm_comp, ← valueMap_edge]
  rfl

lemma valueSquare_right (Φ : StableInfinity.{u} ⟶ Sp.{u}) :
    squareRightEdge ≫ valueSquare p q i r h Φ =
      SSet.yonedaEquiv.symm (coherentNerveEdge (valueMap Φ (laxQuotientCLeg p q r))).edge := by
  rw [valueSquare, ← Category.assoc, square_right,
    SSet.yonedaEquiv_symm_comp, ← valueMap_edge]
  rfl

lemma valueSquare_left (Φ : StableInfinity.{u} ⟶ Sp.{u}) :
    squareLeftEdge ≫ valueSquare p q i r h Φ =
      SSet.yonedaEquiv.symm (coherentNerveEdge (valueMap Φ (dSource p q i))).edge := by
  rw [valueSquare, ← Category.assoc, square_left,
    SSet.yonedaEquiv_symm_comp, ← valueMap_edge]
  rfl

lemma valueSquare_top (Φ : StableInfinity.{u} ⟶ Sp.{u}) :
    squareTopEdge ≫ valueSquare p q i r h Φ =
      SSet.yonedaEquiv.symm (coherentNerveEdge (valueMap Φ (laxQuotientDLeg p q r))).edge := by
  rw [valueSquare, ← Category.assoc, square_top,
    SSet.yonedaEquiv_symm_comp, ← valueMap_edge]
  rfl

lemma valueSquare_upper (Φ : StableInfinity.{u} ⟶ Sp.{u}) :
    squareTriangle 0 ≫ valueSquare p q i r h Φ =
      SSet.yonedaEquiv.symm (upper p q i r).simplex ≫ Φ := by
  rw [valueSquare, ← Category.assoc, square_upper]

lemma valueSquare_lower (Φ : StableInfinity.{u} ⟶ Sp.{u}) :
    squareTriangle 1 ≫ valueSquare p q i r h Φ =
      SSet.yonedaEquiv.symm (compositionDiagonalTransport
        (lower p q i r) (comparisonTriangle p q i r h)).triangle.simplex ≫ Φ := by
  rw [valueSquare, ← Category.assoc, square_lower]

end SerrePositivity.KST.LocalizingInvariants.LaxQuotientRelativeSquare
