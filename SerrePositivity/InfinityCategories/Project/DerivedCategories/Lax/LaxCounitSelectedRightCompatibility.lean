module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberFamilyRightHom
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.ArrowFamilyHomNaturality
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax
open _root_.SerrePositivity.KST.LocalizingInvariants
open _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit
variable {C D E A Q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)
  (i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A (laxCategory p q)) (r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (laxCategory p q) Q)

def quotientSelectedRight : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (i.hom ≫ r.hom)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberSquareFamily.cofiber Q.obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientArrow p q i r)) :=
  eqToHom (congrArg (fun f => HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientArrow_target p q i r).symm) ≫
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.rightHom Q.obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientArrow p q i r)

lemma quotientSelectedDiagrams_right :
    CofiberDiagrams.lift Q.obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientArrow p q i r) ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.right Q.obj =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.rightArrow Q.obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientArrow p q i r) := by
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.right, ← Category.assoc, CofiberDiagrams.lift_inclusion]
  rfl

lemma quotientSelectedRight_arrow : Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientSelectedRight p q i r) =
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.arrowFamilyHom (CofiberDiagrams.lift Q.obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientArrow p q i r) ≫
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.right Q.obj)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientSelectedDiagrams_right]
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientSelectedRight
  rw [arrow_mk_eqToHom_comp]
  exact CofiberFamily.rightHom_arrow _ _

lemma quotientSelectedRight_relative_arrow :
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientOriginalRightImage p q i r ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientCofiberRelativeIso p q i r).hom) =
      Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientSelectedRight p q i r) := by
  have hn := congrArg Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientRightComparison_naturality p q i r)
  have hs := arrow_mk_comp_of_identity (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientRightSourceComparison p q i r)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.arrowFamilyHom (CofiberDiagrams.lift Q.obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientArrow p q i r) ≫
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.right Q.obj)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientRightSourceComparison_arrow p q i r)
  have he := arrow_mk_comp_congr (quotientOriginalRightImage_arrow p q i r)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientCofiberRelativeIso_arrow p q i r)
  exact he.trans (hn.symm.trans (hs.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientSelectedRight_arrow p q i r).symm))

lemma quotientSelectedCIso_right :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientSelectedRight p q i r ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientSelectedCIso p q i r).hom =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientCUnitImage p q i r := by
  have he := arrow_mk_comp_congr (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientSelectedRight_relative_arrow p q i r).symm
    (rfl : Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientSelectedCIso p q i r).hom =
      Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientSelectedCIso p q i r).hom)
  have hc : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientOriginalRightImage p q i r ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientCofiberRelativeIso p q i r).hom) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientSelectedCIso p q i r).hom = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientCUnitImage p q i r := by
    change (_ ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientCofiberRelativeIso p q i r).hom) ≫
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientCofiberRelativeIso p q i r).inv ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientOriginalCImage p q i r) = _
    calc
      _ = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientOriginalRightImage p q i r ≫
          ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientCofiberRelativeIso p q i r).hom ≫
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientCofiberRelativeIso p q i r).inv ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientOriginalCImage p q i r) :=
        Category.assoc _ _ _
      _ = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientOriginalRightImage p q i r ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientOriginalCImage p q i r :=
        congrArg (fun f => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientOriginalRightImage p q i r ≫ f)
          (Iso.hom_inv_id_assoc _ _)
      _ = _ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientOriginalRightImage_unit p q i r
  exact hom_eq_of_arrow_mk_eq (he.trans (congrArg Arrow.mk hc))

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit.quotientSelectedCIso_right := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientSelectedCIso_right

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit.quotientSelectedDiagrams_right := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientSelectedDiagrams_right

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientSelectedRight (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit.quotientSelectedRight := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientSelectedRight

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit.quotientSelectedRight_arrow := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientSelectedRight_arrow

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit.quotientSelectedRight_relative_arrow := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientSelectedRight_relative_arrow

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit.quotientSelectedRight._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientSelectedRight._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit.quotientSelectedRight._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientSelectedRight._proof_2
