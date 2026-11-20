module

public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Iso
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.IsoEndpointNormalization

/-!
分割で生成：docstring を書き直すこと
 # 元の under 実現比較全体を、元の共同比較の同じ指定成分として回収する
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

private lemma _root_.SerrePositivity.InfinityCategories.Stable.Straightening.StraighteningUnderRealizationChart.normalizeComposition {C : Type v} [Category.{w} C]
    {a b c a' b' c' : C} (l : a ≅ b) (e : b ≅ c)
    (ha : a = a') (hb : b = b') (hc : c = c') :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.isoNormalizeEndpoints (l ≪≫ e) ha hc =
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.isoNormalizeEndpoints l ha hb ≪≫ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.isoNormalizeEndpoints e hb hc := by
  subst a' b' c'
  simp only [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.isoNormalizeEndpoints, eqToIso_refl, Iso.refl_symm, Iso.refl_trans,
    Iso.trans_refl]

lemma mapNormalizeCompositionWithEq {C : Type v} [Category.{w} C]
    {Z : Type v'} [Category.{w'} Z] (F : C ⥤ Z) {a b b₀ c : C} {a' b' c' : Z}
    (l : a ≅ b) (e : b₀ ≅ c) (h : b = b₀) (d : a ≅ c)
    (hd : d = l ≪≫ eqToIso h ≪≫ e)
    (ha : F.obj a = a') (hb : F.obj b = b') (hb₀ : F.obj b₀ = b')
    (hc : F.obj c = c') :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.isoNormalizeEndpoints (F.mapIso d) ha hc =
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.isoNormalizeEndpoints (F.mapIso l) ha hb ≪≫
        _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.isoNormalizeEndpoints (F.mapIso e) hb₀ hc := by
  subst d b₀
  simp only [eqToIso_refl, Iso.refl_trans, Functor.mapIso_trans]
  exact _root_.SerrePositivity.InfinityCategories.Stable.Straightening.StraighteningUnderRealizationChart.normalizeComposition _ _ ha hb hc

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Straightening

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
