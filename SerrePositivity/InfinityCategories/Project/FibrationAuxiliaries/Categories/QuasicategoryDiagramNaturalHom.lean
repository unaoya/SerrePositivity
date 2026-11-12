module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryDiagramCategory
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.StrictDiagramMappingVertices

/-!
概要：元の strict な自然変換を、quasicategory 値図式の圏の通常の射にする。
方針：元の変換の頂点をテンソル単位からの射へ移す。
規約：core による移送が保持する元の通常の射を使う。
使われ方：底全体の結合比較を同じ coherent な辺へ実現する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories

/-- 元の自然変換を、全 strict 変換の core で豊穣化した図式の圏の通常の射にする。 -/
def quasicategoryDiagramHom {C : Type u} [Category.{u} C]
    {F G : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryDiagramCategory C}
    (η : F.val ⋙ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryObjectForget ⟶ G.val ⋙ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryObjectForget) : F ⟶ G :=
  (SSet.unitHomEquiv _).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMappingVertex η)

/-- 元の恒等自然変換は、同じ通常の圏の恒等射になる。 -/
lemma quasicategoryDiagramHom_id {C : Type u} [Category.{u} C]
    (F : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryDiagramCategory C) :
    quasicategoryDiagramHom (𝟙 (F.val ⋙ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryObjectForget)) = 𝟙 F := by
  apply (SSet.unitHomEquiv _).injective
  rfl

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
