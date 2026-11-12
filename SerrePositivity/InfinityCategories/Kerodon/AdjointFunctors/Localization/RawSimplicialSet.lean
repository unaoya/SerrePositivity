module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock

/-!
# 元の未縮約 hammock の単体集合と余極限への元の射

概要：元の全語を保持する未縮約 hammock の全作用素を単体集合へ束ねる。
方針：各語の graph の元の全作用素と、同じ標準射を使う。
規約：縮約の選択や代表の一意性は仮定しない。
使われ方：縮約写像の全作用素での整合と余極限の比較。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawSimplicialSet
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  (X Y : C)

/-- 元の全語の全単体を保持する未縮約 hammock の単体集合。 -/
def simplicialSet : SSet.{max u v} where
  obj n := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock W X Y n
  map α := ↾fun r => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock.map W X Y α r
  map_id n := by
    apply ConcreteCategory.hom_ext
    intro r
    change (⟨r.1, (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W r.1 X Y).map (𝟙 n) r.2⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock W X Y n) = r
    rw [CategoryTheory.Functor.map_id]
    rfl
  map_comp α β := by
    apply ConcreteCategory.hom_ext
    intro r
    change (⟨r.1, (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W r.1 X Y).map (α ≫ β) r.2⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock W X Y _) =
      ⟨r.1, (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W r.1 X Y).map β ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W r.1 X Y).map α r.2)⟩
    rw [CategoryTheory.Functor.map_comp]
    rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawSimplicialSet (simplicialSet)


/-- 元の語の同じ標準射からなる、元の余極限への単体的射。 -/
def augmentation : simplicialSet W X Y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W X Y where
  app _ := ↾fun r => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock.value W X Y r
  naturality _ _ α := by
    apply ConcreteCategory.hom_ext
    intro r
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock.value_map W X Y α r

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawSimplicialSet (augmentation)


lemma augmentation_app (n : SimplexCategoryᵒᵖ) (r : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock W X Y n) :
    (augmentation W X Y).app n r = (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X Y r.1).app n r.2 := rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawSimplicialSet (augmentation_app)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawSimplicialSet
