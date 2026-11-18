module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordEmbeddingObjects
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.NerveEmbedding
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram

/-!
# 単射な語の遷移による元の graph の単射性

概要：単射な語の射は、全次数の元の graph の単射を与える。
方針：元の zigzag の対象単射性・忠実性を nerve へ移す。
規約：proper 性のうち単射性を証明し、像の交わりの条件は後続。
使われ方：Dwyer–Kan §4.4・5.4 の全語の graph 図式の proper 性。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock
open _root_.CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b) (hf : Function.Injective f.orderHom) (X Y : C)
include hf

/-- 元の図式の包含遷移は、単体集合として単射。 -/
lemma graphDiagram_map_mono : Mono ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y).map f) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram_map]
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor_faithful (W := W) (X := X) (Y := Y) f hf
  exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.nerveMap_mono_of_faithful _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj_injective f hf)

/-- 元の全単体の射列を保つ、各次数の包含遷移の単射性。 -/
lemma graphDiagram_map_app_injective (n : SimplexCategoryᵒᵖ) :
    Function.Injective (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y).map f).app n) := by
  have := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.graphDiagram_map_mono W f hf X Y
  exact CategoryTheory.injective_of_mono _

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock
