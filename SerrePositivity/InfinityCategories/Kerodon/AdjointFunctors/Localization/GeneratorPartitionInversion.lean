module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.GeneratorPartition

/-!
# 元の自由圏の指定矢の反転と生成部分への制限

概要：W.paths の反転は指定生成矢の反転、または指定生成部分の全射の反転と同値。
方針：全射列の帰納と指定生成部分の包含の像の特徴付けを使う。
規約：元の関手の同じ射像について IsIso を結論とする。
使われ方：自由積分解による通常の局所化への帰着。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v u' v'
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {D : Type u'} [Category.{v'} D] (L : Paths C ⥤ D)

lemma inverts_iff_generators : W.paths.IsInvertedBy L ↔
    ∀ {X Y : C} (f : X ⟶ Y), W f → IsIso (L.map f.toPath) := by
  constructor
  · intro h X Y f hf
    exact h f.toPath (MorphismProperty.toPath_mem_paths hf)
  · intro h
    change ∀ {X Y : C} (p : Quiver.Path X Y), W.paths p → IsIso (L.map p)
    intro X Y p hp
    induction p with
    | nil => change IsIso (L.map (𝟙 _)); rw [L.map_id]; infer_instance
    | cons p f ih =>
      have := ih hp.1
      have := h f hp.2
      have he : L.map (Quiver.Path.cons (V := C) p f) =
          L.map p ≫ L.map (Quiver.Hom.toPath (V := C) f) :=
        L.map_comp p (Quiver.Hom.toPath (V := C) f)
      rw [he]
      infer_instance

lemma inverts_iff_markedRestriction : W.paths.IsInvertedBy L ↔
    (⊤ : MorphismProperty (Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.quiver W))).IsInvertedBy
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.inclusion W ⋙ L) := by
  constructor
  · intro h X Y p _
    exact h ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.inclusion W).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.inclusion_mem W p)
  · intro h
    apply (inverts_iff_generators W L).2
    intro X Y f hf
    exact h (Quiver.Hom.toPath
      (show @Quiver.Hom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.quiver W) _ X Y from ⟨f, hf⟩)) trivial

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
