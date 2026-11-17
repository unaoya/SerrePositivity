module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanDiagramNaturalTransformationComposition
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagramOrdinaryAction
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.KanDiagramUniversalEnriched
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.NormalizedHomNaturality

/-!
概要：元のKan値自然変換の実現を、指定した通常の添字関手で制限する。
方針：普遍豊穣図式を同じ添字関手で制限し、元の実現のHom作用を計算する。
規約：HTT §1.1.5・Kerodon §2.4.3の構成の法則の特殊化。
  全図式の射の類の等式を示し、点ごとの像の一致だけを仮定しない。
使われ方：P3-C1PNの元のstrict変換と指定νの添字制限の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
open SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

private lemma universal_realization (J : Type u) [SmallCategory J] :
    (kanDiagramUniversalEnriched J).realization = kanDiagramRealization J := by
  rw [KanEnrichedDiagram.realization, kanDiagramUniversalEnriched_toEnrichedFunctor,
    coherentNerveMap_id, Category.id_comp]

private lemma normalized_map_congr {X Y : SSet.{u}} {f g : X ⟶ Y}
    (h : f = g) {x y : X _⦋0⦌} {x' y' : Y _⦋0⦌}
    (hf : x' = f.app _ x) (hf' : y' = f.app _ y)
    (hg : x' = g.app _ x) (hg' : y' = g.app _ y)
    (a : (HomotopyCategory.mk x : hoFunctor.obj X) ⟶ HomotopyCategory.mk y) :
    normalizedVertexHomMap f hf hf' a = normalizedVertexHomMap g hg hg' a := by
  cases h
  rfl

/-- 指定添字関手で制限した同じ自然変換の実現は、元の実現の指定前合成。 -/
@[cite HTT "1.1.5" (partial := special) "通常の小さい添字圏間の関手によるKan値自然変換の実現の制限則。"]
lemma kanDiagramNaturalTransformationHom_precomp
    {I J : Type u} [SmallCategory I] [SmallCategory J] (H : I ⥤ J)
    {F G : KanDiagramObject J} (η : F.val ⋙ kanObjectForget ⟶ G.val ⋙ kanObjectForget) :
    kanFunctorHomCongr (kanDiagramCoherentNerve_precomp H F.val)
      (kanDiagramCoherentNerve_precomp H G.val)
      (precomposeFunctorHom ((SSet.uliftFunctor.{u+1,u}).map (nerveMap H))
        (Truncated.HomotopyCategory.homMk (kanDiagramNaturalTransformationEdge η).toTruncated)) =
      Truncated.HomotopyCategory.homMk (kanDiagramNaturalTransformationEdge
        (F := ⟨H ⋙ F.val, trivial⟩) (G := ⟨H ⋙ G.val, trivial⟩)
        (Functor.whiskerLeft H η)).toTruncated := by
  let D := (kanDiagramUniversalEnriched J).reindex H
  have hreal : kanDiagramRealization J ≫
      (pre ((SSet.uliftFunctor.{u+1,u}).map (nerveMap H))).app SpaceInfinity.{u} =
      D.realization := by
    simpa only [universal_realization] using
      (kanDiagramUniversalEnriched J).realization_reindex H
  rw [kanFunctorHomCongr_precompose_normalized,
    kanDiagramNaturalTransformationHom_eq_normalized, normalizedVertexHomMap_comp]
  trans normalizedVertexHomMap D.realization (D.realization_vertex F).symm
    (D.realization_vertex G).symm
    (Truncated.HomotopyCategory.homMk (coherentNerveEdge (kanDiagramHom η)).toTruncated)
  · exact normalized_map_congr hreal _ _ _ _ _
  · apply D.realization_homMk_of_homEquiv (kanDiagramHom η) (Functor.whiskerLeft H η)
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro z
    apply Subtype.ext
    funext i
    rfl

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
