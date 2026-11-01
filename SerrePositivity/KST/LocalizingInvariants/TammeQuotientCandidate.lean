module

public import SerrePositivity.KST.LocalizingInvariants.LocalizationFactorization
public import SerrePositivity.KST.LocalizingInvariants.LaxDifferenceExact
public import SerrePositivity.InfinityCategories.Stable.Verdier.AdjointVerdier

/-!
概要：一般の lax pullback の商の実 quasicategory と、元の差の coherent な因子化を構成。
方針：通常 pullback の像を cofiber に持つ辺を局所化し、全関手圏の普遍性で差を下ろす。
規約：右随伴は要求しない。安定性・完全性・核の同定は後続。
使われ方：Land–Tamme の一般の差の項の実構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable {C D E : StableCategory.{u}} (p : ExactMap C E) (q : ExactMap D E)

def tammeLocalizingEdges : Set ((laxCategory p q).obj _⦋1⦌) :=
  cofiberLocalizingEdges (essentialImage (pullbackInclusion p q))

lemma tammeLocalizingEdges_eq : tammeLocalizingEdges p q = invertedEdges (laxDifference p q) :=
  (invertedEdges_eq_cofiber_kernel (pullbackInclusion p q) (exactLaxDifference p q)
    (exactLaxDifference_kernel p q)).symm

def tammeQuotient : SSet.{u} := edgeLocalization (laxCategory p q).obj (tammeLocalizingEdges p q)

instance tammeQuotient_quasicategory : Quasicategory (tammeQuotient p q) :=
  edgeLocalization_quasicategory _ _

def tammeQuotientMap : (laxCategory p q).obj ⟶ tammeQuotient p q := edgeLocalizationMap _ _

lemma tammeQuotient_isLocalization : IsLocalization (tammeQuotientMap p q)
    (tammeLocalizingEdges p q) := edgeLocalization_isLocalization _ _

lemma tammeDifference_inverts : InvertsEdges (laxDifference p q) (tammeLocalizingEdges p q) := by
  rw [tammeLocalizingEdges_eq]
  exact Set.Subset.refl _

def tammeQuotientComparison : tammeQuotient p q ⟶ E.obj :=
  localizationDescend (tammeQuotientMap p q) (tammeLocalizingEdges p q)
    (tammeQuotient_isLocalization p q) (laxDifference p q) (tammeDifference_inverts p q)

/-- 元の全単体上の差の関手との coherent な因子化同型。 -/
def tammeQuotientComparisonIso :
    FunctorIso (tammeQuotientMap p q ≫ tammeQuotientComparison p q) (laxDifference p q) :=
  localizationDescendIso (tammeQuotientMap p q) (tammeLocalizingEdges p q)
    (tammeQuotient_isLocalization p q) (laxDifference p q) (tammeDifference_inverts p q)

end SerrePositivity.KST.LocalizingInvariants
