module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Stable.Exact.ExactMapPinchedPath
public import SerrePositivity.KST.LocalizingInvariants.IdentityLaxDiagonal
public import SerrePositivity.KST.LocalizingInvariants.IdentityLaxVerdier
public import SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifferenceKernel
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
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference
end SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference
namespace SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference
variable {C D E A Q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap D E)
  (i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A (laxCategory p q)) (r : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap (laxCategory p q) Q)
  (h : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence i r)

def kernelMap : A ⟶ Q := ⟨i.hom ≫ first p q r, inferInstance⟩

def inclusionComposite : A ⟶ laxCategory (𝟙 Q) (𝟙 Q) := i ≫ exactLift p q r

def diagonalComposite : A ⟶ laxCategory (𝟙 Q) (𝟙 Q) :=
  _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.kernelMap p q i r ≫ IdentityLax.exactDiagonal Q

def quotientComposite : laxCategory p q ⟶ Q :=
  exactLift p q r ≫ exactLaxDifference (𝟙 Q) (𝟙 Q)

def lower : SSet.Edge.CompStruct (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow i) (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow (exactLift p q r))
    (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.inclusionComposite p q i r)) :=
  coherentNerveCompStruct (C := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableQCat.{u}) i (exactLift p q r)

def upper : SSet.Edge.CompStruct (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.kernelMap p q i r))
    (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow (IdentityLax.exactDiagonal Q))
    (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.diagonalComposite p q i r)) :=
  coherentNerveCompStruct (C := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableQCat.{u}) (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.kernelMap p q i r) (IdentityLax.exactDiagonal Q)

def diagonalComparisonTriangle : SSet.Edge.CompStruct (SSet.Edge.id (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableVertex A))
    (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.inclusionComposite p q i r))
    (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.diagonalComposite p q i r)) :=
  _root_.SerrePositivity.InfinityCategories.Stable.Exact.exactMapComparisonTriangle (F := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.diagonalComposite p q i r)
    (G := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.inclusionComposite p q i r) (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.inclusionDiagonalIso p q i r h).symm

def comparisonSquare : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableInfinity.{u} :=
  PathComparisonSquare.square (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.lower p q i r) (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.upper p q i r)
    (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.diagonalComparisonTriangle p q i r h)

lemma comparisonSquare_bottom : squareBottomEdge ≫ _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.comparisonSquare p q i r h =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow i).edge :=
  PathComparisonSquare.square_bottom _ _ _

lemma comparisonSquare_right : squareRightEdge ≫ _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.comparisonSquare p q i r h =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow (exactLift p q r)).edge :=
  PathComparisonSquare.square_right _ _ _

lemma comparisonSquare_left : squareLeftEdge ≫ _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.comparisonSquare p q i r h =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.kernelMap p q i r)).edge :=
  PathComparisonSquare.square_left _ _ _

lemma comparisonSquare_top : squareTopEdge ≫ _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.comparisonSquare p q i r h =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow (IdentityLax.exactDiagonal Q)).edge :=
  PathComparisonSquare.square_top _ _ _

def quotientCompositionTriangle : SSet.Edge.CompStruct (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow (exactLift p q r))
    (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow (exactLaxDifference (𝟙 Q) (𝟙 Q))) (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow r) := by
  let s := coherentNerveCompStruct (C := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableQCat.{u})
    (exactLift p q r) (exactLaxDifference (𝟙 Q) (𝟙 Q))
  have e : FunctorIso (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.quotientComposite p q r).hom r.hom :=
    differenceIso p q r
  exact (compositionDiagonalTransport s (_root_.SerrePositivity.InfinityCategories.Stable.Exact.exactMapComparisonTriangle (F := r)
    (G := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.quotientComposite p q r) e.symm)).triangle

end SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.comparisonSquare (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference.comparisonSquare := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.comparisonSquare

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference.comparisonSquare_bottom := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.comparisonSquare_bottom

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference.comparisonSquare_left := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.comparisonSquare_left

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference.comparisonSquare_right := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.comparisonSquare_right

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference.comparisonSquare_top := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.comparisonSquare_top

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.diagonalComparisonTriangle (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference.diagonalComparisonTriangle := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.diagonalComparisonTriangle

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.diagonalComposite (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference.diagonalComposite := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.diagonalComposite

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.inclusionComposite (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference.inclusionComposite := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.inclusionComposite

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.kernelMap (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference.kernelMap := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.kernelMap

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.lower (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference.lower := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.lower

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.quotientComposite (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference.quotientComposite := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.quotientComposite

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.quotientCompositionTriangle (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference.quotientCompositionTriangle := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.quotientCompositionTriangle

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.upper (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference.upper := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.upper

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference.kernelMap._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.kernelMap._proof_1
