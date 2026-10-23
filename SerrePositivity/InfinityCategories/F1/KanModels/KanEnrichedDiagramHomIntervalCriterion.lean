module

public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalMappingPostHomCriterion
public import SerrePositivity.InfinityCategories.F1.KanModels.KanEnrichedHomInterval
public import SerrePositivity.InfinityCategories.F1.Coherent.HomEquivalence
public import SerrePositivity.InfinityCategories.F1.Universe.Kan

/-!
概要：豊穣図式の実際の区間作用の同値性を、同じ共同実現の pinched Hom 作用へ戻す。
方針：元の coherent Hom 比較と、端点を正規化した区間模型の自然性を使う。
規約：独立な写像空間同値だけで充満忠実性を結論しない。
使われ方：strict transport の実際の区間作用から分類写像の充満忠実性へ進む。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories

/-- 実際の区間作用が同値なら、その同じ共同実現の pinched Hom 作用が同値。 -/
lemma KanEnrichedDiagram.pinchedHomMap_isQCatEquivalence_of_homInterval
    {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    [∀ X Y : C, KanComplex (SimplicialCategory.sHom X Y)]
    {I : Type u} [SmallCategory I] (D : KanEnrichedDiagram C I) (X Y : C)
    (h : IsQCatEquivalence (kanEnrichedDiagramHomInterval D X Y rfl rfl)) :
    IsQCatEquivalence (pinchedHomMap D.realization (coherentNerveVertex X)
      (coherentNerveVertex Y)) := by
  have hh : IsQCatEquivalence (coherentHomComparison X Y ≫
      (pinchedHomToIntervalMappingSpace (coherentNerveVertex X) (coherentNerveVertex Y) ≫
        intervalMappingPostOfEq D.realization (coherentNerveVertex X) (coherentNerveVertex Y)
          (D.realization_vertex X) (D.realization_vertex Y))) := by
    exact h
  have hc := (coherentHomComparison_isQCatEquivalence X Y).cancel_left hh
  exact pinchedHomMap_isQCatEquivalence_of_intervalPost D.realization
    (coherentNerveVertex X) (coherentNerveVertex Y)
    (D.realization_vertex X) (D.realization_vertex Y) hc

/-- 全ての実際の区間作用の同値性は、同じ豊穣図式の共同実現の充満忠実性を与える。 -/
lemma KanEnrichedDiagram.isFullyFaithful_of_homInterval
    {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    [∀ X Y : C, KanComplex (SimplicialCategory.sHom X Y)]
    {I : Type u} [SmallCategory I] (D : KanEnrichedDiagram C I)
    (h : ∀ X Y : C, IsQCatEquivalence (kanEnrichedDiagramHomInterval D X Y rfl rfl)) :
    IsFullyFaithful D.realization := by
  intro x y
  obtain ⟨X, rfl⟩ := (coherentNerveVertexEquiv C).surjective x
  obtain ⟨Y, rfl⟩ := (coherentNerveVertexEquiv C).surjective y
  exact (D.pinchedHomMap_isQCatEquivalence_of_homInterval X Y
    (h X Y)).isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories
