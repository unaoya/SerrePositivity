module

public import SerrePositivity.InfinityCategories.F1.QuasicategoryDiagramNaturalHom
public import SerrePositivity.InfinityCategories.F1.QuasicategoryDiagramMixedHom

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
namespace SerrePositivity.InfinityCategories

/-- 元の自然変換の豊穣表示を混合評価すると、同じ成分と底の射の合成になる。 -/
lemma quasicategoryDiagramHom_mixed {C : Type u} [Category.{u} C]
    {F G : QuasicategoryDiagramCategory C}
    (η : F.val ⋙ quasicategoryObjectForget ⟶ G.val ⋙ quasicategoryObjectForget)
    {c d : C} (f : c ⟶ d) :
    eHomEquiv SSet.{u} (quasicategoryDiagramHom η) ≫
      quasicategoryDiagramMixedHom f F G =
    eHomEquiv SSet.{u} (show quasicategoryDiagramValue F c ⟶ quasicategoryDiagramValue G d
      from η.app c ≫ G.val.map f) := by
  apply (SSet.unitHomEquiv _).injective
  apply Subtype.ext
  change ((ihom ((F.val ⋙ quasicategoryObjectForget).obj c)).map
    ((G.val ⋙ quasicategoryObjectForget).map f)).app _
      (functorVertex (η.app c)) = functorVertex (η.app c ≫ G.val.map f)
  rfl

/-- 恒等変換と底の任意の射の混合評価は、その同じ元の図式の射。 -/
lemma quasicategoryDiagramMixedHom_ordinary_id {C : Type u} [Category.{u} C]
    (F : QuasicategoryDiagramCategory C) {c d : C} (f : c ⟶ d) :
    eHomEquiv SSet.{u} (𝟙 F) ≫ quasicategoryDiagramMixedHom f F F =
      eHomEquiv SSet.{u} (show quasicategoryDiagramValue F c ⟶ quasicategoryDiagramValue F d
        from F.val.map f) := by
  apply (SSet.unitHomEquiv _).injective
  apply Subtype.ext
  rfl

end SerrePositivity.InfinityCategories
