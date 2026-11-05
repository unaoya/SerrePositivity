module

public import SerrePositivity.InfinityCategories.Derived.Lax.LaxCounitQuotientUnitComparison

/-!
概要：商での全図式比較に現れる右辺は、元の指定右辺の前後合成そのもの。
方針：prism の一致と端点の輸送を Arrow の等号として保持する。
規約：各点や整数 π での一致に弱めない。使われ方：商の右辺と C 単位の接続。
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

lemma CofiberFamily.rightHom_arrow (X : SSet.{u}) [Quasicategory X] [IsStable X]
    {A : SSet.{u}} (a : A ⟶ (ihom (Δ[1] : SSet.{u})).obj X) :
    Arrow.mk (CofiberFamily.rightHom X a) =
      Arrow.mk (arrowFamilyHom (CofiberFamily.rightArrow X a)) := by
  apply Truncated.HomotopyCategory.congr_arrowMk_homMk
  rfl

namespace LaxCounit
variable {C D E A Q : StableCategory.{u}} (p : ExactMap C E) (q : ExactMap D E)
  (i : ExactMap A (laxCategory p q)) (r : ExactMap (laxCategory p q) Q)

lemma rightHom_arrow : Arrow.mk (rightHom p q) =
    Arrow.mk (arrowFamilyHom (CofiberFamily.rightArrow (laxCategory p q).obj (arrow p q))) := by
  unfold rightHom
  rw [arrow_mk_eqToHom_comp]
  exact CofiberFamily.rightHom_arrow _ _

lemma quotientOriginalRightImage_arrow :
    Arrow.mk (quotientOriginalRightImage p q i r) =
      Arrow.mk (arrowFamilyHom (quotientOriginalDiagrams p q i r ≫
        CofiberDiagrams.right Q.obj)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientOriginalDiagrams_right, arrowFamilyHom_postcomp, arrowFamilyHom_precomp]
  let F := (hoFunctor.map ((pre i.hom).app (laxCategory p q).obj)).toFunctor ⋙
    (hoFunctor.map ((ihom A.obj).map r.hom)).toFunctor
  have he := congrArg F.mapArrow.obj (rightHom_arrow p q)
  exact he

end LaxCounit
end SerrePositivity.KST.LocalizingInvariants
