module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.KanHomMap
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.NatTransRecovery

/-!
概要：左右 Kan の比較写像の全単射性を nerve と通常の圏で比較する。
方針：自然変換の全単射で可換な正方形を挟む。
規約：各比較関手を指定した全単射性。
使われ方：B5 の通常の Kan 拡張の回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison

/-- 概要：左 Kan の指定比較写像の全単射性は通常の自然変換で判定できる。
方針：可換正方形の両側に自然変換の全単射を使う。
規約：元の単位を保つ比較。
使われ方：大域的な左 Kan 普遍性の比較。 -/
lemma nerve_leftKanHomMap_bijective_iff {K C D : Type u}
    [Category.{u} K] [Category.{u} C] [Category.{u} D]
    (L : K ⥤ C) {F₀ : K ⥤ D} {F : C ⥤ D} (β : F₀ ⟶ L ⋙ F) (G : C ⥤ D) :
    Function.Bijective (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanHomMap (F₀ := nerveMap F₀) (F := nerveMap F) (nerveMap L)
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHom (F := F₀) (G := L ⋙ F) β) (nerveMap G)) ↔
        Function.Bijective (fun η : F ⟶ G ↦ β ≫ Functor.whiskerLeft L η) := by
  have hh : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanHomMap (F₀ := nerveMap F₀) (F := nerveMap F) (nerveMap L)
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHom (F := F₀) (G := L ⋙ F) β) (nerveMap G)) ∘
        _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomEquiv F G =
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomEquiv F₀ (L ⋙ G) ∘
        (fun η : F ⟶ G ↦ β ≫ Functor.whiskerLeft L η) := by
    funext η
    exact _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerve_leftKanHomMap L β η
  have h := Equiv.bijective_comp (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomEquiv F G)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanHomMap (F₀ := nerveMap F₀) (F := nerveMap F) (nerveMap L)
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHom (F := F₀) (G := L ⋙ F) β) (nerveMap G))
  rw [hh] at h
  erw [Equiv.comp_bijective] at h
  exact h.symm

/-- 概要：右 Kan の指定比較写像の全単射性は通常の比較写像と同値。
方針：前後に自然変換の全単射を合成する。
規約：指定された余単位の比較写像。
使われ方：大域的な右 Kan 普遍性の比較。 -/
lemma nerve_rightKanHomMap_bijective_iff {K C D : Type u}
    [Category.{u} K] [Category.{u} C] [Category.{u} D]
    (L : K ⥤ C) {F₀ : K ⥤ D} {F : C ⥤ D} (α : L ⋙ F ⟶ F₀) (G : C ⥤ D) :
    Function.Bijective (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanHomMap (F₀ := nerveMap F₀) (F := nerveMap F) (nerveMap L)
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHom (F := L ⋙ F) (G := F₀) α) (nerveMap G)) ↔
        Function.Bijective (fun η : G ⟶ F ↦ Functor.whiskerLeft L η ≫ α) := by
  have hh : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanHomMap (F₀ := nerveMap F₀) (F := nerveMap F) (nerveMap L)
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHom (F := L ⋙ F) (G := F₀) α) (nerveMap G)) ∘
        _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomEquiv G F =
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomEquiv (L ⋙ G) F₀ ∘
        (fun η : G ⟶ F ↦ Functor.whiskerLeft L η ≫ α) := by
    funext η
    exact _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerve_rightKanHomMap L α η
  have h := Equiv.bijective_comp (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomEquiv G F)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanHomMap (F₀ := nerveMap F₀) (F := nerveMap F) (nerveMap L)
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHom (F := L ⋙ F) (G := F₀) α) (nerveMap G))
  rw [hh] at h
  erw [Equiv.comp_bijective] at h
  exact h.symm

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
