module

public import SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.QuillenCfUnitPrism
public import SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.QuillenCfFullyFaithful
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.IntervalUnitCollageComparison
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.CartesianComparisonComposition
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.HomotopyMappingEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitMappingAdjunction

/-!
概要：元の Quillen cf 輸送の同じ単位を使う、cf nerve 間の ∞ 随伴。
方針：元の辺と正方形を保持して、標準の写像空間比較へ移す。
規約：元の cf 置換との比較は別工程。使われ方：HTT 5.2.4.6 と QuillenCfDerivedLimits。

対応節は Kerodon 6.2（Tag 02EH）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open HomotopicalAlgebra

open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
noncomputable section
variable {C D : Type v} [Category.{u} C] [Category.{u} D]
  [SimplicialCategory C] [SimplicialCategory D] [ModelCategory C] [ModelCategory D]
  (R : EnrichedFunctor SSet.{u} D C)
  {L : C ⥤ D} (adj : L ⊣ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor R)
  [SerrePositivity.Quillen.IsLeftQuillen L]
  (fibD : MorphismProperty.FunctorialFactorizationData
    (trivialCofibrations D) (fibrations D))
  (e : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.EnrichedAdjunctionHomComposition R adj)
  (SC : SerrePositivity.Enriched.TensorCotensor SSet.{u} C)
  (SD : SerrePositivity.Enriched.TensorCotensor SSet.{u} D)
  [_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.FixedSimplicialPushoutProduct SC.tensor] [_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.FixedSimplicialPushoutProduct SD.tensor]
  (cofC : MorphismProperty.FunctorialFactorizationData
    (cofibrations C) (trivialFibrations C))

include fibD e SC SD cofC in
/-- 元の同じ η・左右輸送・比較正方形から、標準単位の写像空間条件を証明する。 -/
lemma quillenCfDerivedUnitMappingSpaceCondition_exists :
    letI := _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.cofibrantFibrantObjects_nerve_quasicategory SC
    letI := _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.cofibrantFibrantObjects_nerve_quasicategory SD
    ∃ H : SSet.Homotopy (𝟙 (SimplicialNerve (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects C)))
      (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfLeftDerived R adj fibD e SC SD ≫ _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfRightDerived R adj SC SD cofC),
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitMappingSpaceCondition
        (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)) := by
  have := _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.cofibrantFibrantObjects_nerve_quasicategory SC
  have := _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.cofibrantFibrantObjects_nerve_quasicategory SD
  have := _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageInfinity_quasicategory R adj SC SD
  let F := _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfLeftDerived R adj fibD e SC SD
  let G := _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfRightDerived R adj SC SD cofC
  let i := _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageBottomNerve R
  let j := _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageTopNerve R
  let p := _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageProjection R
  obtain ⟨η, HL, HR, J, hη0, hη1, hηi, hL0, hL1, hLp, hLc,
    hR0, hR1, hRp, hRc, hJb, hJ1, hJp, hJc⟩ :=
    _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfDerivedUnitPrism_exists R adj fibD e SC SD cofC
  let Hu := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyOfPrism η hη0 hη1
  let Hl := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyOfPrism HL hL0 hL1
  let Hr := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyOfPrism HR hR0 hR1
  refine ⟨Hu, (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitMappingSpaceCondition_iff_interval _).mpr ?_⟩
  intro x y
  let lx := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (SSet.Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy Hl)) x
  have hc := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.cartesianComparison_component_comp F G i j η hη0 hη1 HL hL0 hL1
    HR hR0 hR1 J hηi hJb hJ1 x
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitIntervalMap_isSimplicialHomotopyEquivalence_of_collage
    (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy Hu))
    i j Hr x y lx hc
  · have hmap := _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.intervalFunctorMap_isSimplicialHomotopyEquivalence_of_fullyFaithful j
      (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageTopNerve_isFullyFaithful R adj SC SD)
      (F.app (Opposite.op ⦋0⦌) x) y
    have hcL : ∀ z, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge Hl z).edge := by
      intro z
      rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyOfPrism_vertexEdge]
      exact hLc z
    have hy : p.app (Opposite.op ⦋0⦌) (j.app (Opposite.op ⦋0⦌) y) =
        stdSimplex.obj₀Equiv.symm (1 : Fin 2) := by
      exact congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) y) (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageTop_projection R)
    have hpre := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPrecompose_equivalence_of_cocartesianHomotopy Hl p
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyOfPrism_projection HL hL0 hL1 p hLp) hcL x (j.app (Opposite.op ⦋0⦌) y) hy
    exact (hmap.isQCatEquivalence.comp hpre.isQCatEquivalence).isSimplicialHomotopyEquivalence
  · have hmap := _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.intervalFunctorMap_isSimplicialHomotopyEquivalence_of_fullyFaithful i
      (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageBottomNerve_isFullyFaithful R adj SC SD)
      x (G.app (Opposite.op ⦋0⦌) y)
    have hcR : ∀ z, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge p (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge Hr z).edge := by
      intro z
      rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyOfPrism_vertexEdge]
      exact hRc z
    have hx : p.app (Opposite.op ⦋0⦌) (i.app (Opposite.op ⦋0⦌) x) =
        stdSimplex.obj₀Equiv.symm (0 : Fin 2) := by
      exact congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) x) (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageBottom_projection R)
    have hpost := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPostcompose_equivalence_of_cartesianHomotopy Hr p
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyOfPrism_projection HR hR0 hR1 p hRp) hcR y (i.app (Opposite.op ⦋0⦌) x) hx
    exact (hmap.isQCatEquivalence.comp hpost.isQCatEquivalence).isSimplicialHomotopyEquivalence

include fibD e SC SD cofC in
/-- 同じ標準単位を持つ cf nerve 間の導来 ∞ 随伴。余単位・両三角恒等式を含む。 -/
lemma quillenCfDerivedAdjunction_exists :
    letI := _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.cofibrantFibrantObjects_nerve_quasicategory SC
    letI := _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.cofibrantFibrantObjects_nerve_quasicategory SD
    ∃ H : SSet.Homotopy (𝟙 (SimplicialNerve (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects C)))
      (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfLeftDerived R adj fibD e SC SD ≫ _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfRightDerived R adj SC SD cofC),
      ∃ a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfLeftDerived R adj fibD e SC SD)
        (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfRightDerived R adj SC SD cofC),
        a.unitHom = SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H) := by
  have := _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.cofibrantFibrantObjects_nerve_quasicategory SC
  have := _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.cofibrantFibrantObjects_nerve_quasicategory SD
  obtain ⟨H, hH⟩ := quillenCfDerivedUnitMappingSpaceCondition_exists R adj fibD e SC SD cofC
  exact ⟨H, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatAdjunctionOfUnitMappingSpaceCondition _ hH,
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatAdjunctionOfUnitMappingSpaceCondition_unitHom _ hH⟩

end
end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
