module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Derived.Lax.LaxCounitQuotientRightComparison
public import SerrePositivity.KST.LocalizingInvariants.LaxInclusions

/-!
概要：C 単位を保つ元の比較を包含と商で写し、選択された cofiber に接続する。
方針：同じ二胞体を前後合成し、全図式比較から得た cofiber 同型を合成する。
規約：元の右辺の像との等式を保持する。使われ方：不変量への coherent な移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.LaxCounit
end SerrePositivity.KST.LocalizingInvariants.LaxCounit
namespace SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit
open SerrePositivity.KST.LocalizingInvariants.LaxCounit
variable {C D E A Q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap D E)
  (i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A (laxCategory p q)) (r : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap (laxCategory p q) Q)

def quotientOriginalRightImage := homPost r.hom (homPre i.hom (rightHom p q))

def quotientOriginalCImage :=
  homPost r.hom (homPre i.hom (rightCompatibleFromCIso p q).hom)

def quotientCUnitImage :=
  homPost r.hom (homPre i.hom (LaxInclusion.fromCAdjunction p q).unitHom)

lemma quotientOriginalRightImage_unit :
    _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientOriginalRightImage p q i r ≫ _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientOriginalCImage p q i r =
      _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientCUnitImage p q i r := by
  unfold _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientOriginalRightImage _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientOriginalCImage _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientCUnitImage
  rw [← homPost_homComp, ← homPre_homComp, rightCompatibleFromCIso_right]

def quotientOriginalCImageIso : FunctorIso ((i.hom ≫ cofiber p q) ≫ r.hom)
    ((i.hom ≫ ((laxFst p q).hom ≫ LaxInclusion.fromC p q)) ≫ r.hom) := by
  have hi : IsIso (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientOriginalCImage p q i r) := by
    unfold _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientOriginalCImage homPost homPre
    infer_instance
  exact asIso (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientOriginalCImage p q i r)

def quotientSelectedCIso : FunctorIso
    (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.cofiber Q.obj (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientArrow p q i r))
    ((i.hom ≫ ((laxFst p q).hom ≫ LaxInclusion.fromC p q)) ≫ r.hom) :=
  (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientCofiberRelativeIso p q i r).symm ≪≫ _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientOriginalCImageIso p q i r

end SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientCUnitImage (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit.quotientCUnitImage := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientCUnitImage

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientOriginalCImage (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit.quotientOriginalCImage := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientOriginalCImage

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientOriginalCImageIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit.quotientOriginalCImageIso := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientOriginalCImageIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientOriginalRightImage (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit.quotientOriginalRightImage := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientOriginalRightImage

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit.quotientOriginalRightImage_unit := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientOriginalRightImage_unit

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientSelectedCIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit.quotientSelectedCIso := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientSelectedCIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit.quotientCUnitImage._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientCUnitImage._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit.quotientOriginalCImageIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientOriginalCImageIso._proof_1
