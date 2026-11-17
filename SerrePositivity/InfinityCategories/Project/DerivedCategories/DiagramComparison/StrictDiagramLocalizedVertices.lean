module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramRightFrameComparison

/-!
概要：元のstrict図式の局所化の各頂点を、同じ図式圏の対象で表示する。
方針：実hammockとの既存比較の全二胞体と、coherent nerveの頂点の回収を使う。
規約：局所化写像の本質的全射性だけを示す。任意coherent図式の厳密化とは別の主張。
使われ方：HTT 4.2.4.4の写像空間比較で、任意の局所化頂点を解像の入力へ戻す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory _root_.HomotopicalAlgebra SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] (d : StrictDiagramDirection)
local instance isw1StrictDiagramLocalizedVerticesLocal1 : ModelCategory (StrictComplexDiagram A d) := strictDiagramReedyModelCategory A d
local instance isw1StrictDiagramLocalizedVerticesLocal2 : (cofibrations (StrictComplexDiagram A d)).HasFunctorialFactorization
    (trivialFibrations (StrictComplexDiagram A d)) :=
  strictDiagramReedy_cof_hasFunctorialFactorization A d

/-- 同じ実hammock局所化と元の指定局所化を結ぶ、既存の全二胞体つきの比較。 -/
def strictDiagramHammockComparison :
    _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CoherentLocalizationComparison
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap (modelRelativeCategory (StrictComplexDiagram A d)))
      (strictDiagramModelLocalization A d) :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelRightFrameLocalizationComparison (strictDiagramRightFrameFamily A d)
    (strictDiagramModelLocalization A d) (strictDiagramModelLocalization_isLocalization A d)

/-- 元の局所化の任意頂点は、元のstrict図式の像と同型である。 -/
lemma strictDiagramLocalization_isEssentiallySurjective :
    IsEssentiallySurjective (strictDiagramLocalization A d) := by
  intro x
  let c := strictDiagramHammockComparison A d
  obtain ⟨z, ⟨ez⟩⟩ := c.equivalence.isEssentiallySurjective x
  let Z : (modelRelativeCategory (StrictComplexDiagram A d)).category :=
    coherentNerveObject (C := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanHammockCategory
      (modelRelativeCategory (StrictComplexDiagram A d))) z
  have hz : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap
      (modelRelativeCategory (StrictComplexDiagram A d))).app (Opposite.op ⦋0⦌)
        (nerveVertex Z) = z :=
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap_vertex _ Z).trans (coherentNerveVertex_object z)
  have hv : (strictDiagramModelNerveIso A d).inv.app (Opposite.op ⦋0⦌)
      (nerveVertex Z) = ComposableArrows.mk₀ ((strictDiagramModelDown A d).obj Z) :=
    ComposableArrows.ext₀ rfl
  have et := c.triangle.app (nerveVertex Z)
  change VertexIso
    (c.equivalence.hom.app (Opposite.op ⦋0⦌)
      ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap (modelRelativeCategory (StrictComplexDiagram A d))).app
        (Opposite.op ⦋0⦌) (nerveVertex Z)))
    ((strictDiagramLocalization A d).app (Opposite.op ⦋0⦌)
      ((strictDiagramModelNerveIso A d).inv.app (Opposite.op ⦋0⦌) (nerveVertex Z))) at et
  rw [hz, hv] at et
  exact ⟨ComposableArrows.mk₀ ((strictDiagramModelDown A d).obj Z), ⟨et.symm ≪≫ ez⟩⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
