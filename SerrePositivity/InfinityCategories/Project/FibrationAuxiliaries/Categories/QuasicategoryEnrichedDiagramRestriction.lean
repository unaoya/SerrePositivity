module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagram

/-!
概要：quasicategory 値豊穣図式の底の制限と、全対象の豊穣な前合成。
方針：元の各比較とその全高次の自然性へ同じ関手を作用させる。
規約：比較成分を選び直さない。
使われ方：元の分類図式を制限した側と、底変換した側の図式の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories

/-- 元の全高次に自然な比較を、同じ豊穣関手で前合成する。 -/
def QuasicategoryEnrichedComparison.precompose
    {C : Type v} {L : Type w} [Category.{u} C] [SimplicialCategory C]
    [Category.{u} L] [SimplicialCategory L]
    {F G : EnrichedFunctor SSet.{u} C _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QuasicategoryObject.{u}}
    (η : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedComparison F G) (R : EnrichedFunctor SSet.{u} L C) :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedComparison (R.comp SSet F) (R.comp SSet G) := by
  refine ⟨fun X ↦ η.val (R.obj X), ?_⟩
  intro X Y
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨x, h⟩
  exact congrArg (fun f ↦ f.app n (x, (R.map X Y).app n h)) (η.property (R.obj X) (R.obj Y))

/-- 元の比較の図式を、底の関手で全対象・全射について制限する。 -/
def QuasicategoryEnrichedDiagram.reindex
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {J L : Type u} [Category.{u} J] [Category.{u} L]
    (D : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagram C J) (k : L ⥤ J) :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagram C L where
  obj i := D.obj (k.obj i)
  map f := D.map (k.map f)
  map_id i X := by rw [k.map_id]; exact D.map_id _ _
  map_comp f g X := by rw [k.map_comp]; exact D.map_comp _ _ _

/-- 元の比較の図式を、全 fibration の同じ豊穣な底変換で前合成する。 -/
def QuasicategoryEnrichedDiagram.precompose
    {C : Type v} {L : Type w} [Category.{u} C] [SimplicialCategory C]
    [Category.{u} L] [SimplicialCategory L]
    {J : Type u} [Category.{u} J] (D : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagram C J)
    (R : EnrichedFunctor SSet.{u} L C) : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagram L J where
  obj j := R.comp SSet (D.obj j)
  map f := (D.map f).precompose R
  map_id i X := D.map_id i (R.obj X)
  map_comp f g X := D.map_comp f g (R.obj X)

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
