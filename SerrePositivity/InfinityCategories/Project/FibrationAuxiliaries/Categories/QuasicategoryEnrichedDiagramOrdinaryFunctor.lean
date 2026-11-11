module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedFunctorCategory
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagramComparison

/-!
概要：元の豊穣図式と比較を、同じ全高次比較を射とする通常の関手と自然変換にする。
方針：恒等・合成・自然性を各成分で検査し、同じ作用を往復する。
規約：射の比較を選び直さない。
使われ方：元の豊穣比較の合成三角形を通常の三点図式で構成する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories

variable {C : Type v} [Category.{u} C] [SimplicialCategory C]
  {J : Type u} [Category.{u} J]

/-- 元の豊穣図式を、元の比較の圏への通常の関手にする。 -/
def QuasicategoryEnrichedDiagram.toFunctor (D : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagram C J) :
    J ⥤ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedFunctorCategory C where
  obj := D.obj
  map f := D.map f
  map_id j := Subtype.ext (funext (D.map_id j))
  map_comp f g := Subtype.ext (funext (D.map_comp f g))

/-- 元の豊穣比較の圏への関手を、同じ豊穣図式として回収する。 -/
def QuasicategoryEnrichedDiagram.ofFunctor (F : J ⥤ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedFunctorCategory C) :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagram C J where
  obj := F.obj
  map f := F.map f
  map_id j X := congrArg (fun η ↦ η.val X) (F.map_id j)
  map_comp f g X := congrArg (fun η ↦ η.val X) (F.map_comp f g)

/-- 元の図式比較は、同じ全高次比較を成分とする通常の自然変換。 -/
def QuasicategoryEnrichedDiagramComparison.toNatTrans
    {D E : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagram C J} (η : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagramComparison D E) :
    D.toFunctor ⟶ E.toFunctor where
  app := η.app
  naturality i j f := Subtype.ext (funext (η.naturality f))

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
