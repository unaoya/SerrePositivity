module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagramArrow

/-!
概要：二点と底の積上の同じ豊穣比較の図式の両端は、元の二つの全図式。
方針：端点の包含で制限し、元の全比較成分を厳密に回収する。
規約：底全体・全対象・全高次の図式の等式。
使われ方：比較の実現の両端を元の分類主写像へ正規化する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories

/-- 元の対象と全比較の作用が一致する豊穣図式は等しい。 -/
lemma QuasicategoryEnrichedDiagram.ext
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J] {D E : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagram C J}
    (ho : D.obj = E.obj) (hm : HEq (@D.map) (@E.map)) : D = E := by
  cases D
  cases E
  cases ho
  cases hm
  rfl

/-- 二点と底の積への同じ端点の包含関手。 -/
def quasicategoryDiagramEndpointIndex (i : Fin 2) (J : Type u) [Category.{u} J] :
    J ⥤ Fin 2 × J where
  obj j := (i, j)
  map f := (𝟙 i, f)

/-- 比較の積上の図式を零側へ制限すると、元の始域図式そのもの。 -/
lemma QuasicategoryEnrichedDiagramComparison.arrowDiagram_zero
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J] {D E : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagram C J}
    (η : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagramComparison D E) :
    η.arrowDiagram.reindex (quasicategoryDiagramEndpointIndex 0 J) = D := by
  apply QuasicategoryEnrichedDiagram.ext rfl
  apply heq_of_eq
  funext i j f
  apply Subtype.ext
  funext X
  change 𝟙 _ ≫ (D.map f).val X = (D.map f).val X
  exact Category.id_comp _

/-- 比較の積上の図式を一側へ制限すると、元の標的図式そのもの。 -/
lemma QuasicategoryEnrichedDiagramComparison.arrowDiagram_one
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J] {D E : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagram C J}
    (η : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagramComparison D E) :
    η.arrowDiagram.reindex (quasicategoryDiagramEndpointIndex 1 J) = E := by
  apply QuasicategoryEnrichedDiagram.ext rfl
  apply heq_of_eq
  funext i j f
  apply Subtype.ext
  funext X
  change 𝟙 _ ≫ (E.map f).val X = (E.map f).val X
  exact Category.id_comp _

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
