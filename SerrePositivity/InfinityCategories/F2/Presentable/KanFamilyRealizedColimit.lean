module

public import SerrePositivity.InfinityCategories.F2.Presentable.KanFamilyColimit
public import SerrePositivity.InfinityCategories.F2.Presentable.KanDiagramRealizedCocone

/-!
概要：元の filtered Kan 図式族の strict 余極限を、全図式の点ごとの native 余極限として実現する。
方針：元の余錐を KanDiagramObject に束縛し、全余錐の評価を同じ通常の評価へ厳密に戻す。
規約：指定頂点は同じ関手圏の strict 余極限図式。点ごとに模型を選び直さない。
使われ方：coherent な錐族の交換で、strict 模型の全余極限を元の指定余錐へ移送する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits
variable {I J : Type u} [SmallCategory I] [SmallCategory J] [IsFiltered J]
  (F : J ⥤ I ⥤ KanObject.{u})

/-- 同じ通常の strict 余極限余錐を、元の全図式の関手空間へ実現した一つの余錐。 -/
def kanFamilyRealizedColimitCocone :
    JoinCocone (strictCoherentDiagram (F ⋙ kanDiagramBundle) ≫ kanDiagramRealization I) :=
  kanDiagramRealizedCocone (kanDiagramBundle.mapCocone (kanFamilyColimitCocone F))

/-- 全余錐を実現しても、頂点は同じ元の strict 余極限図式の全実現そのもの。 -/
lemma kanFamilyRealizedColimitCocone_vertex :
    (kanFamilyRealizedColimitCocone F).vertex =
      functorVertex (kanDiagramCoherentNerve (cardinalFilteredKanDiagram F)) :=
  kanDiagramRealizedCocone_vertex _

/-- 元の全図式の strict な filtered 余極限余錐の実現は、点ごとの native 余極限。 -/
lemma kanFamilyRealizedColimitCocone_pointwise :
    IsPointwiseColimitCone (kanFamilyRealizedColimitCocone F) := by
  apply kanDiagramRealizedCocone_pointwise
  intro i
  change IsColimit
    (((kanDiagramBundle ⋙ coherentEnrichedUnderlyingFunctor (kanDiagramEvaluationEnriched i)) ⋙
      kanObjectForget).mapCocone (kanFamilyColimitCocone F))
  rw [kanDiagramBundle_evaluation]
  exact kanFamilyColimitCocone_evaluation_isColimit F i

end SerrePositivity.InfinityCategories.F2.Presentable
