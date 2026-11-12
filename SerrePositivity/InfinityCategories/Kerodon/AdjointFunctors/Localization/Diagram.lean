module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordComposition
public import Mathlib.CategoryTheory.Category.Cat

/-!
# 全語の固定端点 zigzag と hammock graph の図式

概要：全ての有限の向き付き語と単調写像を添字とする実際の図式を構成する。
方針：元の遷移関手の厳密な単位・合成則から圏値図式を作り、nerve を取る。
規約：添字圏を filtered と仮定せず、空語を含む全ての語を使う。
使われ方：hammock の余極限表示。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative] (X Y : C)

/-- 全語の元の zigzag 圏と元の遷移関手による厳密な圏値図式。 -/
def categoryDiagram : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word ⥤ Cat.{v, max u v} where
  obj w := Cat.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y)
  map f := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor (W := W) (X := X) (Y := Y) f).toCatHom
  map_id _ := by
    apply Cat.Hom.ext
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.functor_id
  map_comp f g := by
    apply Cat.Hom.ext
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordComposition.functor_comp f g

/-- 全語の固定型の hammock graph と同じ元の遷移射の図式。 -/
def graphDiagram : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word ⥤ SSet.{max u v} := categoryDiagram W X Y ⋙ nerveFunctor

@[simp] lemma graphDiagram_obj (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    (graphDiagram W X Y).obj w = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W w X Y := rfl

lemma graphDiagram_map {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b) :
    (graphDiagram W X Y).map f = nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor (W := W) (X := X) (Y := Y) f) :=
  rfl

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram
