module

public import SerrePositivity.InfinityCategories.F1.Categories.QuasicategoryDiagramConstantParameter
public import SerrePositivity.InfinityCategories.F1.Categories.QuasicategoryEnrichedDiagramRealization

/-!
概要：quasicategory 値図式の共同実現の頂点は、元の図式全体の coherent 表示。
方針：定値パラメーターの対角評価を全次数で使う。
規約：変換空間や始域の局所 Kan 性を仮定しない。
使われ方：元の全 Hom の区間作用の両端を同じ図式に正規化する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

local instance quasicategoryRealizationVertices_sourceCore_simplicialCategory
    {C : Type v} [Category.{u} C] [SimplicialCategory C] :
    SimplicialCategory (TransportEnrichment quasicategoryCoreFunctor.{u} C) :=
  TransportEnrichment.enrichedOrdinaryCategory C quasicategoryCoreFunctor.{u}
    quasicategoryCoreUnitHomEquiv quasicategoryCoreUnitHomEquiv_eq

/-- 元の図式を頂点に固定した共同実現は、その同じ図式の coherent 表示。 -/
lemma quasicategoryDiagramRealization_vertex {J : Type u} [Category.{u} J]
    (F : QuasicategoryDiagramCategory J) :
    (quasicategoryDiagramRealization J).app (Opposite.op ⦋0⦌) (coherentNerveVertex F) =
      functorVertex (qCatDiagramCoherentNerve (quasicategoryDiagramValueFunctor F)) := by
  apply CategoryTheory.Functor.functorHom_ext
  intro n α
  have hα : α = (SimplexCategory.const n.unop ⦋0⦌ 0).op := Subsingleton.elim _ _
  subst α
  apply ConcreteCategory.hom_ext
  rintro ⟨σ⟩
  exact quasicategoryDiagramDiagonalSimplex_constant F σ

/-- 豊穣図式の実現も、同じ全対象で元の評価図式そのものを表す。 -/
lemma QuasicategoryEnrichedDiagram.realization_vertex
    {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J] (D : QuasicategoryEnrichedDiagram C J)
    (X : TransportEnrichment quasicategoryCoreFunctor.{u} C) :
    D.realization.app (Opposite.op ⦋0⦌) (coherentNerveVertex X) =
      functorVertex (qCatDiagramCoherentNerve
        (quasicategoryDiagramValueFunctor (D.toCoreEnrichedFunctor.obj X))) := by
  change (quasicategoryDiagramRealization J).app _
    ((coherentNerveMap D.toCoreEnrichedFunctor).app _ (coherentNerveVertex X)) = _
  rw [coherentNerveMap_vertex, quasicategoryDiagramRealization_vertex]

end SerrePositivity.InfinityCategories
