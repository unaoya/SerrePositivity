module

public import SerrePositivity.InfinityCategories.F2.Presentable.KanDiagramBundle
public import SerrePositivity.InfinityCategories.F2.Ind.StrictCoconePostcomposition
public import SerrePositivity.InfinityCategories.F2.Ind.CoconeTransformationPointPost
public import SerrePositivity.InfinityCategories.F2.Ind.FilteredKanCocone
public import SerrePositivity.InfinityCategories.F2.FunctorCoconeEvaluation
public import SerrePositivity.InfinityCategories.F2.CoconeValEquality

/-!
概要：元の strict な Kan 図式値余錐を、関手空間の点ごとの native な余極限余錐へ実現する。
方針：全余錐の後合成の厳密な式で豊穣評価に戻し、filtered な Kan 余錐の判定を使う。
規約：元の全余錐を保持し、KanDiagramObject の全 Hom の Kan 性を要求しない。
使われ方：共同 strict 模型の余極限と、元の指定された点ごとの余極限との同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits
variable {I J : Type u} [SmallCategory I] [SmallCategory J]
  {F : J ⥤ KanDiagramObject I} (c : Cocone F)

/-- 元の図式値の全余錐を、同じ関手空間へ実現する。 -/
def kanDiagramRealizedCocone :
    JoinCocone (strictCoherentDiagram F ≫ kanDiagramRealization I) :=
  mapJoinCocone (kanDiagramRealization I) (strictNativeCocone c)

/-- 実現した余錐の頂点は、元の指定された図式の全 coherent 実現。 -/
lemma kanDiagramRealizedCocone_vertex :
    (kanDiagramRealizedCocone c).vertex = functorVertex (kanDiagramCoherentNerve c.pt.val) := by
  rw [kanDiagramRealizedCocone, Ind.mapJoinCocone_vertex, strictNativeCocone_vertex,
    kanDiagramRealization_vertex]

/-- 元の全余錐の評価は、同じ豊穣評価関手で写した strict 余錐の全単体と一致する。 -/
lemma kanDiagramRealizedCocone_evaluation_val (i : I) :
    (evaluateFunctorCocone (kanDiagramRealizedCocone c) (ULift.up (nerveVertex i))).val =
      (strictNativeCocone ((coherentEnrichedUnderlyingFunctor
        (kanDiagramEvaluationEnriched i)).mapCocone c)).val := by
  change ((strictNativeCocone c).val ≫ kanDiagramRealization I) ≫
    evaluateFunctorAt (ULift.up (nerveVertex i)) = _
  rw [Category.assoc, kanDiagramRealization_evaluate]
  exact Ind.strictNativeCocone_postcomp_val c (kanDiagramEvaluationEnriched i)

/-- 各 strict 評価の台が filtered 余極限なら、同じ実現した全余錐は点ごとの native 余極限。 -/
lemma kanDiagramRealizedCocone_pointwise [IsFiltered J]
    (hc : ∀ i : I, IsColimit (kanObjectForget.mapCocone
      ((coherentEnrichedUnderlyingFunctor (kanDiagramEvaluationEnriched i)).mapCocone c))) :
    IsPointwiseColimitCone (kanDiagramRealizedCocone c) := by
  intro k
  let i : I := k.down.obj 0
  have hk : k = ULift.up (nerveVertex i) := ULift.ext (ComposableArrows.ext₀ rfl)
  rw [hk]
  apply (isColimitCone_iff_of_cocone_val_eq _ _
    (kanDiagramRealizedCocone_evaluation_val c i)).mpr
  exact Ind.strictNativeCocone_isColimit_of_filtered_forget _ (hc i)

end SerrePositivity.InfinityCategories.F2.Presentable
