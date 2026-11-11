module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitComposition

/-!
# 三つの元の hammock 余極限の積の一意性

概要：三つの元の余極限の積からの射は、全固定語の標準射の積で決まる。
方針：元の外部積余錐と第三の余錐に IsColimit.tensor₂ を反復する。
規約：添字圏の filtered 性や同じ添字での積保存は使わない。
使われ方：元の余極限上の合成の結合則の降下。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory CategoryTheory.Limits MonoidalCategory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  (X Y Z V : C)

lemma tensorTriple_hom_ext {K : SSet.{max u v}}
    (f g : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W X Y ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W Y Z) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W Z V ⟶ K)
    (h : ∀ a b c : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word,
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X Y a ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W Y Z b) ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W Z V c) ≫ f =
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X Y a ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W Y Z b) ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W Z V c) ≫ g) :
    f = g := by
  apply (IsColimit.tensor₂ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.tensorPairCocone_isColimit W X Y Z)
    (colimit.isColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W Z V))).hom_ext
  rintro ⟨⟨a, b⟩, c⟩
  simpa only [Cocone.tensor₂, Functor.mapCocone₂, Functor.const_obj_obj,
    curriedTensor_map_app, curriedTensor_obj_map, curriedTensor_obj_obj,
    colimit.cocone_x, colimit.cocone_ι,
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.tensorPairCocone_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.tensorPairCocone, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram_obj,
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion, tensorHom_def, Category.assoc] using h a b c

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
