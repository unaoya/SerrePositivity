module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams
public import SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamilyRightHom
public import SerrePositivity.InfinityCategories.Stable.Quasicategory.ArrowFamilyHomNaturality
public import SerrePositivity.KST.LocalizingInvariants.LaxCounitQuotientRightImage
public import SerrePositivity.KST.LocalizingInvariants.LaxInclusions

/-!
概要：選択された商の cofiber の C 比較は、指定された右辺を C 単位の像へ送る。
方針：全図式比較の自然性・始点の恒等性・元の右辺の像を、端点輸送込みで合成する。
規約：既存の任意の比較同型に整合性を仮定しない。使われ方：商の二脚の二次の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.LaxCounit
end SerrePositivity.KST.LocalizingInvariants.LaxCounit
namespace SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit
open SerrePositivity.KST.LocalizingInvariants.LaxCounit
variable {C D E A Q : StableCategory.{u}} (p : ExactMap C E) (q : ExactMap D E)
  (i : ExactMap A (laxCategory p q)) (r : ExactMap (laxCategory p q) Q)

def quotientSelectedRight : FunctorHom (i.hom ≫ r.hom)
    (CofiberFamily.cofiber Q.obj (quotientArrow p q i r)) :=
  eqToHom (congrArg (fun f => HomotopyCategory.mk (functorVertex f))
    (quotientArrow_target p q i r).symm) ≫
      CofiberFamily.rightHom Q.obj (quotientArrow p q i r)

lemma quotientSelectedDiagrams_right :
    CofiberDiagrams.lift Q.obj (quotientArrow p q i r) ≫ CofiberDiagrams.right Q.obj =
      CofiberFamily.rightArrow Q.obj (quotientArrow p q i r) := by
  rw [CofiberDiagrams.right, ← Category.assoc, CofiberDiagrams.lift_inclusion]
  rfl

lemma quotientSelectedRight_arrow : Arrow.mk (quotientSelectedRight p q i r) =
    Arrow.mk (arrowFamilyHom (CofiberDiagrams.lift Q.obj (quotientArrow p q i r) ≫
      CofiberDiagrams.right Q.obj)) := by
  rw [quotientSelectedDiagrams_right]
  unfold quotientSelectedRight
  rw [arrow_mk_eqToHom_comp]
  exact CofiberFamily.rightHom_arrow _ _

lemma quotientSelectedRight_relative_arrow :
    Arrow.mk (quotientOriginalRightImage p q i r ≫ (quotientCofiberRelativeIso p q i r).hom) =
      Arrow.mk (quotientSelectedRight p q i r) := by
  have hn := congrArg Arrow.mk (quotientRightComparison_naturality p q i r)
  have hs := arrow_mk_comp_of_identity (quotientRightSourceComparison p q i r)
    (arrowFamilyHom (CofiberDiagrams.lift Q.obj (quotientArrow p q i r) ≫
      CofiberDiagrams.right Q.obj)) (quotientRightSourceComparison_arrow p q i r)
  have he := arrow_mk_comp_congr (quotientOriginalRightImage_arrow p q i r)
    (quotientCofiberRelativeIso_arrow p q i r)
  exact he.trans (hn.symm.trans (hs.trans (quotientSelectedRight_arrow p q i r).symm))

lemma quotientSelectedCIso_right :
    quotientSelectedRight p q i r ≫ (quotientSelectedCIso p q i r).hom =
      quotientCUnitImage p q i r := by
  have he := arrow_mk_comp_congr (quotientSelectedRight_relative_arrow p q i r).symm
    (rfl : Arrow.mk (quotientSelectedCIso p q i r).hom =
      Arrow.mk (quotientSelectedCIso p q i r).hom)
  have hc : (quotientOriginalRightImage p q i r ≫ (quotientCofiberRelativeIso p q i r).hom) ≫
      (quotientSelectedCIso p q i r).hom = quotientCUnitImage p q i r := by
    change (_ ≫ (quotientCofiberRelativeIso p q i r).hom) ≫
      ((quotientCofiberRelativeIso p q i r).inv ≫ quotientOriginalCImage p q i r) = _
    calc
      _ = quotientOriginalRightImage p q i r ≫
          ((quotientCofiberRelativeIso p q i r).hom ≫
            (quotientCofiberRelativeIso p q i r).inv ≫ quotientOriginalCImage p q i r) :=
        Category.assoc _ _ _
      _ = quotientOriginalRightImage p q i r ≫ quotientOriginalCImage p q i r :=
        congrArg (fun f => quotientOriginalRightImage p q i r ≫ f)
          (Iso.hom_inv_id_assoc _ _)
      _ = _ := quotientOriginalRightImage_unit p q i r
  exact hom_eq_of_arrow_mk_eq (he.trans (congrArg Arrow.mk hc))

end SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit.quotientSelectedCIso_right := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientSelectedCIso_right

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit.quotientSelectedDiagrams_right := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientSelectedDiagrams_right

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientSelectedRight (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit.quotientSelectedRight := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientSelectedRight

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit.quotientSelectedRight_arrow := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientSelectedRight_arrow

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit.quotientSelectedRight_relative_arrow := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientSelectedRight_relative_arrow

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit.quotientSelectedRight._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientSelectedRight._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit.quotientSelectedRight._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientSelectedRight._proof_2
