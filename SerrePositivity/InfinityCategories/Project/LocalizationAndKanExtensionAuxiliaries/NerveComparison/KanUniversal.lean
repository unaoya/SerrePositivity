module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.ClassicalHomUniversal
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.KanHomBijective
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightHomUniversal

/-!
概要：nerve の大域的 Kan 普遍性と通常の Kan 拡張を比較する。
方針：比較写像の全単射性と nerve の充満性で全ての関手を回収する。
規約：pointwise 条件からは通常の普遍性への含意だけを主張する。
使われ方：B5 の Kan の回収と局所錐比較への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison

/-- 概要：nerve の左 Hom 普遍性は通常の指定単位の左 Kan 拡張と同値。
方針：通常の関手に対する比較と nerve の充満性を使う。
規約：一般の大域的 Kan 条件の比較。
使われ方：pointwise Kan と区別した古典比較。 -/
lemma nerve_leftKanHomUniversal_iff {K C D : Type u}
    [Category.{u} K] [Category.{u} C] [Category.{u} D]
    (L : K ⥤ C) {F₀ : K ⥤ D} {F : C ⥤ D} (β : F₀ ⟶ L ⋙ F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanHomUniversal (F₀ := nerveMap F₀) (F := nerveMap F) (nerveMap L)
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHom (F := F₀) (G := L ⋙ F) β) ↔ F.IsLeftKanExtension β := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.kanClassical_isLeftKanExtension_iff_bijective L F₀ F β]
  constructor
  · intro h G
    exact (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerve_leftKanHomMap_bijective_iff L β G).mp (h (nerveMap G))
  · intro h G
    let H := (nerveFunctor.preimage (X := Cat.of C) (Y := Cat.of D) G).toFunctor
    have hH : nerveMap H = G := nerveFunctor.map_preimage (X := Cat.of C) (Y := Cat.of D) G
    rw [← hH]
    exact (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerve_leftKanHomMap_bijective_iff L β H).mpr (h H)

/-- 概要：nerve の右 Hom 普遍性は通常の指定余単位の右 Kan 拡張と同値。
方針：全ての nerve 間の関手を通常の関手として復元する。
規約：通常の大域的な右 Kan 拡張。
使われ方：右 Kan の古典比較。 -/
lemma nerve_rightKanHomUniversal_iff {K C D : Type u}
    [Category.{u} K] [Category.{u} C] [Category.{u} D]
    (L : K ⥤ C) {F₀ : K ⥤ D} {F : C ⥤ D} (α : L ⋙ F ⟶ F₀) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanHomUniversal (F₀ := nerveMap F₀) (F := nerveMap F) (nerveMap L)
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHom (F := L ⋙ F) (G := F₀) α) ↔ F.IsRightKanExtension α := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.kanClassical_isRightKanExtension_iff_bijective L F₀ F α]
  constructor
  · intro h G
    exact (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerve_rightKanHomMap_bijective_iff L α G).mp (h (nerveMap G))
  · intro h G
    let H := (nerveFunctor.preimage (X := Cat.of C) (Y := Cat.of D) G).toFunctor
    have hH : nerveMap H = G := nerveFunctor.map_preimage (X := Cat.of C) (Y := Cat.of D) G
    rw [← hH]
    exact (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerve_rightKanHomMap_bijective_iff L α H).mpr (h H)


/-- 概要：nerve 上の点ごとの左 Kan 条件から通常の左 Kan 拡張を得る。
方針：既存の Hom 普遍性を通常の自然変換の普遍性に移す。
規約：逆方向は局所錐の比較が別途必要。
使われ方：B5 の点ごとの条件からの帰結。 -/
lemma nerve_isLeftKanExtension_of_pointwise {K C D : Type u}
    [Category.{u} K] [Category.{u} C] [Category.{u} D]
    (L : K ⥤ C) {F₀ : K ⥤ D} {F : C ⥤ D} (β : F₀ ⟶ L ⋙ F)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtensionHom (nerveMap L) (nerveMap F₀) (nerveMap F)
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHom (F := F₀) (G := L ⋙ F) β)) : F.IsLeftKanExtension β :=
  (nerve_leftKanHomUniversal_iff L β).mp (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftKanExtensionHom_homUniversal _ _ _ _ h)

/-- 概要：nerve 上の点ごとの右 Kan 条件は通常の右 Kan 拡張を与える。
方針：右 Hom 普遍性の古典比較を使う。
規約：pointwise 条件と大域的普遍性を同一視しない。
使われ方：点ごとの右 Kan 条件の古典的帰結。 -/
lemma nerve_isRightKanExtension_of_pointwise {K C D : Type u}
    [Category.{u} K] [Category.{u} C] [Category.{u} D]
    (L : K ⥤ C) {F₀ : K ⥤ D} {F : C ⥤ D} (α : L ⋙ F ⟶ F₀)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRightKanExtensionHom (nerveMap L) (nerveMap F₀) (nerveMap F)
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHom (F := L ⋙ F) (G := F₀) α)) : F.IsRightKanExtension α :=
  (nerve_rightKanHomUniversal_iff L α).mp (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRightKanExtensionHom_homUniversal _ _ _ _ h)

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
