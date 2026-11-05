module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

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
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.LaxQuotientRelativeSquare
end SerrePositivity.KST.LocalizingInvariants.LaxQuotientRelativeSquare
namespace SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.LocalizingInvariants.LaxQuotientRelativeSquare
local instance instSimplicialCategoryOmegaSpectrum : SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
variable {C D E A Q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap D E)
  (i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A (laxCategory p q)) (r : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap (laxCategory p q) Q)
  (h : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence i r)

def cSource : A ⟶ C := i ≫ laxFst p q
def dSource : A ⟶ D := i ≫ laxSnd p q
def cComposite : A ⟶ Q := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.cSource p q i ≫ _root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientCLeg p q r
def dComposite : A ⟶ Q := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.dSource p q i ≫ _root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientDLeg p q r

def legsIso : FunctorIso (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.cComposite p q i r).hom (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.dComposite p q i r).hom := by
  change FunctorIso
    ((i.hom ≫ (laxFst p q).hom) ≫ (_root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientCLeg p q r).hom)
    ((i.hom ≫ (laxSnd p q).hom) ≫ (_root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientDLeg p q r).hom)
  exact _root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientRelativeLegsIso p q i r h

def lower : SSet.Edge.CompStruct (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.cSource p q i))
    (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow (_root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientCLeg p q r)) (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.cComposite p q i r)) :=
  coherentNerveCompStruct (C := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableQCat.{u}) (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.cSource p q i) (_root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientCLeg p q r)

def upper : SSet.Edge.CompStruct (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.dSource p q i))
    (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow (_root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientDLeg p q r)) (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.dComposite p q i r)) :=
  coherentNerveCompStruct (C := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableQCat.{u}) (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.dSource p q i) (_root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientDLeg p q r)

def comparisonTriangle : SSet.Edge.CompStruct (SSet.Edge.id (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableVertex A))
    (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.cComposite p q i r)) (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.dComposite p q i r)) :=
  _root_.SerrePositivity.InfinityCategories.Stable.Exact.exactMapComparisonTriangle (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.legsIso p q i r h).symm

def square : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableInfinity.{u} :=
  PathComparisonSquare.square (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.lower p q i r) (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.upper p q i r) (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.comparisonTriangle p q i r h)

lemma square_bottom : squareBottomEdge ≫ _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.square p q i r h =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.cSource p q i)).edge :=
  PathComparisonSquare.square_bottom _ _ _

lemma square_right : squareRightEdge ≫ _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.square p q i r h =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow (_root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientCLeg p q r)).edge :=
  PathComparisonSquare.square_right _ _ _

lemma square_left : squareLeftEdge ≫ _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.square p q i r h =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.dSource p q i)).edge :=
  PathComparisonSquare.square_left _ _ _

lemma square_top : squareTopEdge ≫ _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.square p q i r h =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow (_root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientDLeg p q r)).edge :=
  PathComparisonSquare.square_top _ _ _

lemma square_upper : squareTriangle 0 ≫ _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.square p q i r h =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.upper p q i r).simplex :=
  PathComparisonSquare.square_upper _ _ _

lemma square_lower : squareTriangle 1 ≫ _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.square p q i r h =
    SSet.yonedaEquiv.symm (compositionDiagonalTransport
      (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.lower p q i r) (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.comparisonTriangle p q i r h)).triangle.simplex :=
  PathComparisonSquare.square_lower _ _ _

def valueSquare (Φ : _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableInfinity.{u} ⟶ Sp.{u}) :
    (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ Sp.{u} := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.square p q i r h ≫ Φ

lemma valueSquare_bottom (Φ : _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableInfinity.{u} ⟶ Sp.{u}) :
    squareBottomEdge ≫ _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.valueSquare p q i r h Φ =
      SSet.yonedaEquiv.symm (coherentNerveEdge (valueMap Φ (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.cSource p q i))).edge := by
  rw [_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.valueSquare, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.square_bottom,
    SSet.yonedaEquiv_symm_comp, ← valueMap_edge]
  rfl

lemma valueSquare_right (Φ : _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableInfinity.{u} ⟶ Sp.{u}) :
    squareRightEdge ≫ _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.valueSquare p q i r h Φ =
      SSet.yonedaEquiv.symm (coherentNerveEdge (valueMap Φ (_root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientCLeg p q r))).edge := by
  rw [_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.valueSquare, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.square_right,
    SSet.yonedaEquiv_symm_comp, ← valueMap_edge]
  rfl

lemma valueSquare_left (Φ : _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableInfinity.{u} ⟶ Sp.{u}) :
    squareLeftEdge ≫ _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.valueSquare p q i r h Φ =
      SSet.yonedaEquiv.symm (coherentNerveEdge (valueMap Φ (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.dSource p q i))).edge := by
  rw [_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.valueSquare, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.square_left,
    SSet.yonedaEquiv_symm_comp, ← valueMap_edge]
  rfl

lemma valueSquare_top (Φ : _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableInfinity.{u} ⟶ Sp.{u}) :
    squareTopEdge ≫ _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.valueSquare p q i r h Φ =
      SSet.yonedaEquiv.symm (coherentNerveEdge (valueMap Φ (_root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientDLeg p q r))).edge := by
  rw [_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.valueSquare, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.square_top,
    SSet.yonedaEquiv_symm_comp, ← valueMap_edge]
  rfl

lemma valueSquare_upper (Φ : _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableInfinity.{u} ⟶ Sp.{u}) :
    squareTriangle 0 ≫ _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.valueSquare p q i r h Φ =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.upper p q i r).simplex ≫ Φ := by
  rw [_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.valueSquare, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.square_upper]

lemma valueSquare_lower (Φ : _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableInfinity.{u} ⟶ Sp.{u}) :
    squareTriangle 1 ≫ _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.valueSquare p q i r h Φ =
      SSet.yonedaEquiv.symm (compositionDiagonalTransport
        (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.lower p q i r) (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.comparisonTriangle p q i r h)).triangle.simplex ≫ Φ := by
  rw [_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.valueSquare, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.square_lower]

end SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.cComposite (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxQuotientRelativeSquare.cComposite := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.cComposite

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.cSource (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxQuotientRelativeSquare.cSource := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.cSource

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.comparisonTriangle (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxQuotientRelativeSquare.comparisonTriangle := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.comparisonTriangle

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.dComposite (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxQuotientRelativeSquare.dComposite := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.dComposite

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.dSource (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxQuotientRelativeSquare.dSource := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.dSource

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.instSimplicialCategoryOmegaSpectrum (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxQuotientRelativeSquare.instSimplicialCategoryOmegaSpectrum := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.instSimplicialCategoryOmegaSpectrum

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.legsIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxQuotientRelativeSquare.legsIso := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.legsIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.lower (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxQuotientRelativeSquare.lower := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.lower

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.square (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxQuotientRelativeSquare.square := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.square

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxQuotientRelativeSquare.square_bottom := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.square_bottom

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxQuotientRelativeSquare.square_left := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.square_left

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxQuotientRelativeSquare.square_lower := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.square_lower

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxQuotientRelativeSquare.square_right := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.square_right

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxQuotientRelativeSquare.square_top := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.square_top

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxQuotientRelativeSquare.square_upper := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.square_upper

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.upper (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxQuotientRelativeSquare.upper := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.upper

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.valueSquare (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxQuotientRelativeSquare.valueSquare := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.valueSquare

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxQuotientRelativeSquare.valueSquare_bottom := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.valueSquare_bottom

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxQuotientRelativeSquare.valueSquare_left := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.valueSquare_left

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxQuotientRelativeSquare.valueSquare_lower := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.valueSquare_lower

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxQuotientRelativeSquare.valueSquare_right := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.valueSquare_right

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxQuotientRelativeSquare.valueSquare_top := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.valueSquare_top

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxQuotientRelativeSquare.valueSquare_upper := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.valueSquare_upper

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxQuotientRelativeSquare.valueSquare.eq_1 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.valueSquare.eq_1
