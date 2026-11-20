module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxCounitQuotientRightComparison
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax
open _root_.SerrePositivity.KST.LocalizingInvariants
open _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit
variable {C D E A Q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)
  (i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A (laxCategory p q)) (r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (laxCategory p q) Q)

def quotientOriginalRightImage := homPost r.hom (homPre i.hom (rightHom p q))

def quotientOriginalCImage :=
  homPost r.hom (homPre i.hom (rightCompatibleFromCIso p q).hom)

def quotientCUnitImage :=
  homPost r.hom (homPre i.hom (LaxInclusion.fromCAdjunction p q).unitHom)

lemma quotientOriginalRightImage_unit :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientOriginalRightImage p q i r ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientOriginalCImage p q i r =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientCUnitImage p q i r := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientOriginalRightImage _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientOriginalCImage _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientCUnitImage
  rw [← homPost_homComp, ← homPre_homComp, rightCompatibleFromCIso_right]

def quotientOriginalCImageIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((i.hom ≫ cofiber p q) ≫ r.hom)
    ((i.hom ≫ ((laxFst p q).hom ≫ LaxInclusion.fromC p q)) ≫ r.hom) := by
  have hi : IsIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientOriginalCImage p q i r) := by
    unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientOriginalCImage homPost homPre
    infer_instance
  exact asIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientOriginalCImage p q i r)

def quotientSelectedCIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberSquareFamily.cofiber Q.obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientArrow p q i r))
    ((i.hom ≫ ((laxFst p q).hom ≫ LaxInclusion.fromC p q)) ≫ r.hom) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientCofiberRelativeIso p q i r).symm ≪≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientOriginalCImageIso p q i r

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
