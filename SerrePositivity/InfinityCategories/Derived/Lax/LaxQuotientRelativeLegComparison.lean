module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Stable.Exact.CofiberZeroTargetDiagrams
public import SerrePositivity.InfinityCategories.Stable.Exact.SuspensionExactFunctor
public import SerrePositivity.KST.LocalizingInvariants.CofiberZeroTargetDiagrams
public import SerrePositivity.InfinityCategories.Derived.Lax.LaxCounitSelectedRightCompatibility
public import SerrePositivity.KST.LocalizingInvariants.LaxInclusions
public import SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientLegComparison

/-!
概要：一般商の二脚を、元の cofiber 図式と始点固定 suspension 図式の比較で結ぶ。
方針：C 単位を保つ比較と、同じ始点の suspension 図式比較を合成して shift を消す。
規約：任意の別の図式実現に置き換えない。使われ方：値の正方形の二胞体。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.LocalizingInvariants.LaxCounit
end SerrePositivity.KST.LocalizingInvariants.LaxCounit
namespace SerrePositivity.InfinityCategories.Derived.Lax
open SerrePositivity.KST.LocalizingInvariants
variable {C D E A Q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap D E)
  (i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A (laxCategory p q)) (r : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap (laxCategory p q) Q)
  (h : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence i r)

namespace LaxCounit
open SerrePositivity.KST.LocalizingInvariants.LaxCounit

def quotientSuspensionDiagramComparison :=
  CofiberFamily.zeroTargetDiagramComparison Q.obj (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientArrow p q i r)
    (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientArrow_zero_target p q i r h)

def quotientCofiber_DSuspRelativeIso :
    FunctorIso (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.cofiber Q.obj (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientArrow p q i r))
      (((i.hom ≫ (laxSnd p q).hom) ≫ (_root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientDLeg p q r).hom) ≫
        _root_.SerrePositivity.InfinityCategories.Stable.Exact.SuspensionExact.map Q.obj) := by
  have e := CofiberFamily.zeroTargetRelativeIso Q.obj (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientArrow p q i r)
    (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientArrow_zero_target p q i r h)
  rw [_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientArrow_source] at e
  exact e

end LaxCounit

def laxQuotientRelativeLegsIso : FunctorIso
    ((i.hom ≫ (laxFst p q).hom) ≫ (_root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientCLeg p q r).hom)
    ((i.hom ≫ (laxSnd p q).hom) ≫ (_root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientDLeg p q r).hom) := by
  apply ((_root_.SerrePositivity.InfinityCategories.Stable.Exact.SuspensionExact.equivalence Q.obj).isQCatEquivalence.postcompose A.obj
    ).isFullyFaithful.preimageVertexIso
  change FunctorIso
    (((i.hom ≫ (laxFst p q).hom) ≫ (_root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientCLeg p q r).hom) ≫ _root_.SerrePositivity.InfinityCategories.Stable.Exact.SuspensionExact.map Q.obj)
    (((i.hom ≫ (laxSnd p q).hom) ≫ (_root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientDLeg p q r).hom) ≫ _root_.SerrePositivity.InfinityCategories.Stable.Exact.SuspensionExact.map Q.obj)
  have ec : FunctorIso
      (((i.hom ≫ (laxFst p q).hom) ≫ (_root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientCLeg p q r).hom) ≫ _root_.SerrePositivity.InfinityCategories.Stable.Exact.SuspensionExact.map Q.obj)
      ((i.hom ≫ ((laxFst p q).hom ≫ LaxInclusion.fromC p q)) ≫ r.hom) := by
    have e := FunctorIso.precomp (_root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientCLeg_suspensionIso p q r)
      (i.hom ≫ (laxFst p q).hom)
    simpa only [Category.assoc] using e
  exact ec ≪≫ (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientSelectedCIso p q i r).symm ≪≫
    _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientCofiber_DSuspRelativeIso p q i r h

end SerrePositivity.InfinityCategories.Derived.Lax

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientRelativeLegsIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.laxQuotientRelativeLegsIso := _root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientRelativeLegsIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientCofiber_DSuspRelativeIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit.quotientCofiber_DSuspRelativeIso := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientCofiber_DSuspRelativeIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientSuspensionDiagramComparison (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit.quotientSuspensionDiagramComparison := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientSuspensionDiagramComparison

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.laxQuotientRelativeLegsIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientRelativeLegsIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.laxQuotientRelativeLegsIso._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientRelativeLegsIso._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.laxQuotientRelativeLegsIso._proof_3 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientRelativeLegsIso._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.laxQuotientRelativeLegsIso._proof_4 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientRelativeLegsIso._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit.quotientCofiber_DSuspRelativeIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientCofiber_DSuspRelativeIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit.quotientCofiber_DSuspRelativeIso._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientCofiber_DSuspRelativeIso._proof_2
