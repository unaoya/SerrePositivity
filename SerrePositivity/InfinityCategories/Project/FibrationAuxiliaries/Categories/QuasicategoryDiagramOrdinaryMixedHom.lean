module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryDiagramNaturalHom
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryDiagramMixedHom

/-!
概要：元の自然変換と底の射の混合評価は、同じ通常の成分と底の射の合成。
方針：core の豊穣単位からの射を零単体で評価する。
規約：元の自然変換と同じ向きの混合作用を保持する。
使われ方：strict 図式の射の実現を既存の prism と比較する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories

/-- 元の自然変換の豊穣表示を混合評価すると、同じ成分と底の射の合成になる。 -/
lemma quasicategoryDiagramHom_mixed {C : Type u} [Category.{u} C]
    {F G : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryDiagramCategory C}
    (η : F.val ⋙ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryObjectForget ⟶ G.val ⋙ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryObjectForget)
    {c d : C} (f : c ⟶ d) :
    eHomEquiv SSet.{u} (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryDiagramHom η) ≫
      _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryDiagramMixedHom f F G =
    eHomEquiv SSet.{u} (show _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryDiagramValue F c ⟶ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryDiagramValue G d
      from η.app c ≫ G.val.map f) := by
  apply (SSet.unitHomEquiv _).injective
  apply Subtype.ext
  change ((ihom ((F.val ⋙ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryObjectForget).obj c)).map
    ((G.val ⋙ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryObjectForget).map f)).app _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (η.app c)) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (η.app c ≫ G.val.map f)
  rfl

/-- 恒等変換と底の任意の射の混合評価は、その同じ元の図式の射。 -/
lemma quasicategoryDiagramMixedHom_ordinary_id {C : Type u} [Category.{u} C]
    (F : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryDiagramCategory C) {c d : C} (f : c ⟶ d) :
    eHomEquiv SSet.{u} (𝟙 F) ≫ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryDiagramMixedHom f F F =
      eHomEquiv SSet.{u} (show _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryDiagramValue F c ⟶ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryDiagramValue F d
        from F.val.map f) := by
  apply (SSet.unitHomEquiv _).injective
  apply Subtype.ext
  rfl

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
