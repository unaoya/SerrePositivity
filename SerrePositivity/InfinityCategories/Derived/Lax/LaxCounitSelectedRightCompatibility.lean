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
variable {C D E A Q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap D E)
  (i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A (laxCategory p q)) (r : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap (laxCategory p q) Q)

def quotientSelectedRight : FunctorHom (i.hom ≫ r.hom)
    (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.cofiber Q.obj (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientArrow p q i r)) :=
  eqToHom (congrArg (fun f => HomotopyCategory.mk (functorVertex f))
    (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientArrow_target p q i r).symm) ≫
      _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.rightHom Q.obj (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientArrow p q i r)

lemma quotientSelectedDiagrams_right :
    CofiberDiagrams.lift Q.obj (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientArrow p q i r) ≫ _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.right Q.obj =
      _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.rightArrow Q.obj (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientArrow p q i r) := by
  rw [_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.right, ← Category.assoc, CofiberDiagrams.lift_inclusion]
  rfl

lemma quotientSelectedRight_arrow : Arrow.mk (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientSelectedRight p q i r) =
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.arrowFamilyHom (CofiberDiagrams.lift Q.obj (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientArrow p q i r) ≫
      _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.right Q.obj)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientSelectedDiagrams_right]
  unfold _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientSelectedRight
  rw [arrow_mk_eqToHom_comp]
  exact CofiberFamily.rightHom_arrow _ _

lemma quotientSelectedRight_relative_arrow :
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientOriginalRightImage p q i r ≫ (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientCofiberRelativeIso p q i r).hom) =
      Arrow.mk (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientSelectedRight p q i r) := by
  have hn := congrArg Arrow.mk (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientRightComparison_naturality p q i r)
  have hs := arrow_mk_comp_of_identity (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientRightSourceComparison p q i r)
    (_root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.arrowFamilyHom (CofiberDiagrams.lift Q.obj (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientArrow p q i r) ≫
      _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.right Q.obj)) (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientRightSourceComparison_arrow p q i r)
  have he := arrow_mk_comp_congr (quotientOriginalRightImage_arrow p q i r)
    (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientCofiberRelativeIso_arrow p q i r)
  exact he.trans (hn.symm.trans (hs.trans (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientSelectedRight_arrow p q i r).symm))

lemma quotientSelectedCIso_right :
    _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientSelectedRight p q i r ≫ (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientSelectedCIso p q i r).hom =
      _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientCUnitImage p q i r := by
  have he := arrow_mk_comp_congr (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientSelectedRight_relative_arrow p q i r).symm
    (rfl : Arrow.mk (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientSelectedCIso p q i r).hom =
      Arrow.mk (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientSelectedCIso p q i r).hom)
  have hc : (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientOriginalRightImage p q i r ≫ (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientCofiberRelativeIso p q i r).hom) ≫
      (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientSelectedCIso p q i r).hom = _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientCUnitImage p q i r := by
    change (_ ≫ (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientCofiberRelativeIso p q i r).hom) ≫
      ((_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientCofiberRelativeIso p q i r).inv ≫ _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientOriginalCImage p q i r) = _
    calc
      _ = _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientOriginalRightImage p q i r ≫
          ((_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientCofiberRelativeIso p q i r).hom ≫
            (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientCofiberRelativeIso p q i r).inv ≫ _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientOriginalCImage p q i r) :=
        Category.assoc _ _ _
      _ = _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientOriginalRightImage p q i r ≫ _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientOriginalCImage p q i r :=
        congrArg (fun f => _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientOriginalRightImage p q i r ≫ f)
          (Iso.hom_inv_id_assoc _ _)
      _ = _ := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientOriginalRightImage_unit p q i r
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
