module

public import SerrePositivity.InfinityCategories.F1.QuasicategoryEnrichedFunctorCategory
public import SerrePositivity.InfinityCategories.F1.QuasicategoryEnrichedDiagramComparison

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
namespace SerrePositivity.InfinityCategories

variable {C : Type v} [Category.{u} C] [SimplicialCategory C]
  {J : Type u} [Category.{u} J]

/-- 元の豊穣図式を、元の比較の圏への通常の関手にする。 -/
def QuasicategoryEnrichedDiagram.toFunctor (D : QuasicategoryEnrichedDiagram C J) :
    J ⥤ QuasicategoryEnrichedFunctorCategory C where
  obj := D.obj
  map f := D.map f
  map_id j := Subtype.ext (funext (D.map_id j))
  map_comp f g := Subtype.ext (funext (D.map_comp f g))

/-- 元の豊穣比較の圏への関手を、同じ豊穣図式として回収する。 -/
def QuasicategoryEnrichedDiagram.ofFunctor (F : J ⥤ QuasicategoryEnrichedFunctorCategory C) :
    QuasicategoryEnrichedDiagram C J where
  obj := F.obj
  map f := F.map f
  map_id j X := congrArg (fun η ↦ η.val X) (F.map_id j)
  map_comp f g X := congrArg (fun η ↦ η.val X) (F.map_comp f g)

/-- 元の図式比較は、同じ全高次比較を成分とする通常の自然変換。 -/
def QuasicategoryEnrichedDiagramComparison.toNatTrans
    {D E : QuasicategoryEnrichedDiagram C J} (η : QuasicategoryEnrichedDiagramComparison D E) :
    D.toFunctor ⟶ E.toFunctor where
  app := η.app
  naturality i j f := Subtype.ext (funext (η.naturality f))

end SerrePositivity.InfinityCategories
