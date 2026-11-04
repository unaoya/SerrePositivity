module

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
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable {C D E A Q : StableCategory.{u}} (p : ExactMap C E) (q : ExactMap D E)
  (i : ExactMap A (laxCategory p q)) (r : ExactMap (laxCategory p q) Q)
  (h : IsVerdierSequence i r)

namespace LaxCounit

def quotientSuspensionDiagramComparison :=
  CofiberFamily.zeroTargetDiagramComparison Q.obj (quotientArrow p q i r)
    (quotientArrow_zero_target p q i r h)

def quotientCofiber_DSuspRelativeIso :
    FunctorIso (CofiberFamily.cofiber Q.obj (quotientArrow p q i r))
      (((i.hom ≫ (laxSnd p q).hom) ≫ (laxQuotientDLeg p q r).hom) ≫
        SuspensionExact.map Q.obj) := by
  have e := CofiberFamily.zeroTargetRelativeIso Q.obj (quotientArrow p q i r)
    (quotientArrow_zero_target p q i r h)
  rw [quotientArrow_source] at e
  exact e

end LaxCounit

def laxQuotientRelativeLegsIso : FunctorIso
    ((i.hom ≫ (laxFst p q).hom) ≫ (laxQuotientCLeg p q r).hom)
    ((i.hom ≫ (laxSnd p q).hom) ≫ (laxQuotientDLeg p q r).hom) := by
  apply ((SuspensionExact.equivalence Q.obj).isQCatEquivalence.postcompose A.obj
    ).isFullyFaithful.preimageVertexIso
  change FunctorIso
    (((i.hom ≫ (laxFst p q).hom) ≫ (laxQuotientCLeg p q r).hom) ≫ SuspensionExact.map Q.obj)
    (((i.hom ≫ (laxSnd p q).hom) ≫ (laxQuotientDLeg p q r).hom) ≫ SuspensionExact.map Q.obj)
  have ec : FunctorIso
      (((i.hom ≫ (laxFst p q).hom) ≫ (laxQuotientCLeg p q r).hom) ≫ SuspensionExact.map Q.obj)
      ((i.hom ≫ ((laxFst p q).hom ≫ LaxInclusion.fromC p q)) ≫ r.hom) := by
    have e := FunctorIso.precomp (laxQuotientCLeg_suspensionIso p q r)
      (i.hom ≫ (laxFst p q).hom)
    simpa only [Category.assoc] using e
  exact ec ≪≫ (LaxCounit.quotientSelectedCIso p q i r).symm ≪≫
    LaxCounit.quotientCofiber_DSuspRelativeIso p q i r h

end SerrePositivity.KST.LocalizingInvariants
