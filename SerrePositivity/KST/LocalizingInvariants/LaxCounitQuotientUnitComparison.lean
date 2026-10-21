module

public import SerrePositivity.KST.LocalizingInvariants.LaxCounitQuotientRightComparison

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
variable {C D E A Q : StableCategory.{u}} (p : ExactMap C E) (q : ExactMap D E)
  (i : ExactMap A (laxCategory p q)) (r : ExactMap (laxCategory p q) Q)

def quotientOriginalRightImage := homPost r.hom (homPre i.hom (rightHom p q))

def quotientOriginalCImage :=
  homPost r.hom (homPre i.hom (rightCompatibleFromCIso p q).hom)

def quotientCUnitImage :=
  homPost r.hom (homPre i.hom (LaxInclusion.fromCAdjunction p q).unitHom)

lemma quotientOriginalRightImage_unit :
    quotientOriginalRightImage p q i r ≫ quotientOriginalCImage p q i r =
      quotientCUnitImage p q i r := by
  unfold quotientOriginalRightImage quotientOriginalCImage quotientCUnitImage
  rw [← homPost_homComp, ← homPre_homComp, rightCompatibleFromCIso_right]

def quotientOriginalCImageIso : FunctorIso ((i.hom ≫ cofiber p q) ≫ r.hom)
    ((i.hom ≫ ((laxFst p q).hom ≫ LaxInclusion.fromC p q)) ≫ r.hom) := by
  have hi : IsIso (quotientOriginalCImage p q i r) := by
    unfold quotientOriginalCImage homPost homPre
    infer_instance
  exact asIso (quotientOriginalCImage p q i r)

def quotientSelectedCIso : FunctorIso
    (CofiberFamily.cofiber Q.obj (quotientArrow p q i r))
    ((i.hom ≫ ((laxFst p q).hom ≫ LaxInclusion.fromC p q)) ≫ r.hom) :=
  (quotientCofiberRelativeIso p q i r).symm ≪≫ quotientOriginalCImageIso p q i r

end SerrePositivity.KST.LocalizingInvariants.LaxCounit
