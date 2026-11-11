module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Iso
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.IsoEndpointNormalization

/-!
分割で生成：docstring を書き直すこと
 # 元の初頂点 under 比較を、同じ切断比較と元の under 制限成分に分解する
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w v' w'
open CategoryTheory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Straightening
open _root_.SerrePositivity.KST.Fibration
variable {B : SSet.{u}}

private lemma _root_.SerrePositivity.InfinityCategories.Stable.Straightening.StraighteningUnderSectionChart.normalizeComposition {C : Type v} [Category.{w} C]
    {a b c b' c' : C} (l : a ≅ b) (e : b ≅ c) (hb : b = b') (hc : c = c') :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.isoNormalizeEndpoints (l ≪≫ e) rfl hc =
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.isoNormalizeEndpoints l rfl hb ≪≫ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.isoNormalizeEndpoints e hb hc := by
  subst b' c'
  simp only [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.isoNormalizeEndpoints, eqToIso_refl, Iso.refl_symm, Iso.refl_trans,
    Iso.trans_refl]

lemma mapNormalizeComposition {C : Type v} [Category.{w} C]
    {Z : Type v'} [Category.{w'} Z] (F : C ⥤ Z) {a b c : C} {b' c' : Z}
    (l : a ≅ b) (e : b ≅ c) (d : a ≅ c) (hd : d = l ≪≫ e)
    (hb : F.obj b = b') (hc : F.obj c = c') :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.isoNormalizeEndpoints (F.mapIso d) rfl hc =
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.isoNormalizeEndpoints (F.mapIso l) rfl hb ≪≫
        _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.isoNormalizeEndpoints (F.mapIso e) hb hc := by
  subst d
  rw [Functor.mapIso_trans]
  exact _root_.SerrePositivity.InfinityCategories.Stable.Straightening.StraighteningUnderSectionChart.normalizeComposition _ _ hb hc

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Straightening

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.mapNormalizeComposition := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Straightening.mapNormalizeComposition
