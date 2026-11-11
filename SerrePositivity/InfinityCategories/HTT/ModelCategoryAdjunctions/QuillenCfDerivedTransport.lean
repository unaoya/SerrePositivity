module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianEdgeTransport
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QuillenCfBifibration
public import SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.QuillenCfEndpointEquivalence

/-!
概要：元の cf nerve 間の左右の導来関手と、元の対応圏内の輸送 prism を構成する。
方針：区間の輸送を両端 fiber の同型で挟み、全空間への元の包含との一致を使う。
規約：単位・余単位と随伴性は別途証明する。使われ方：HTT 5.2.4.6 の導来 ∞ 随伴。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory HomotopicalAlgebra MonoidalCategory CartesianMonoidalCategory SSet

open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions
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

/-- 元の cf 圏の coherent nerve 間の左導来関手。 -/
def quillenCfLeftDerived : SimplicialNerve (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects C) ⟶
    SimplicialNerve (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects D) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.quillenCfCollageProjection_cocartesianFibration R adj fibD e SC SD
  exact (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfBottomFiberIso R).hom ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageProjection R) _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge ≫
      (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfTopFiberIso R).inv

include fibD e SC SD in
/-- 左導来関手は、元の両包含を両端とする coCartesian な輸送 prism を持つ。 -/
lemma quillenCfLeftDerived_transport :
    ∃ H : (Δ[1] : SSet.{max u v}) ⊗ SimplicialNerve (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects C) ⟶
        _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.QuillenCfCollageInfinity R,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ H = _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageBottomNerve R ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ H =
        quillenCfLeftDerived R adj fibD e SC SD ≫ _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageTopNerve R ∧
      H ≫ _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageProjection R = fst (Δ[1] : SSet.{max u v}) _ ∧
      ∀ v : (SimplicialNerve (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects C)) _⦋0⦌,
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageProjection R)
          (H.app (Opposite.op ⦋1⦌)
            (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{max u v})), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant v 1)) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.quillenCfCollageProjection_cocartesianFibration R adj fibD e SC SD
  obtain ⟨H, h0, h1, hb, hc⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport_isTransport
    (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageProjection R) _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge
  refine ⟨((Δ[1] : SSet.{max u v}) ◁ (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfBottomFiberIso R).hom) ≫ H,
    ?_, ?_, ?_, ?_⟩
  · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc, h0,
      _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfBottomFiberIso_hom_ι]
  · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc, h1]
    change (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfBottomFiberIso R).hom ≫ _ =
      ((_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfBottomFiberIso R).hom ≫ _ ≫ (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfTopFiberIso R).inv) ≫ _
    rw [← _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfTopFiberIso_hom_ι]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  · rw [Category.assoc, hb]
    have he : SSet.yonedaEquiv.symm _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge =
        (𝟙 (Δ[1] : SSet.{max u v})) := by
      apply SSet.yonedaEquiv.injective
      rw [Equiv.apply_symm_apply]
      apply SSet.stdSimplex.ext
      intro i
      fin_cases i <;> rfl
    rw [he, Category.comp_id]
    rfl
  · intro v
    change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageProjection R)
      (H.app (Opposite.op ⦋1⦌) (_, (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfBottomFiberIso R).hom.app _
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant v 1)))
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map]
    exact hc ((_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfBottomFiberIso R).hom.app _ v)

variable (cofC : MorphismProperty.FunctorialFactorizationData
  (cofibrations C) (trivialFibrations C))

/-- 元の cf 圏の coherent nerve 間の右導来関手。 -/
def quillenCfRightDerived : SimplicialNerve (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects D) ⟶
    SimplicialNerve (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects C) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.quillenCfCollageProjection_cartesianFibration R adj SC SD cofC
  exact (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfTopFiberIso R).hom ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgeTransport (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageProjection R) _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge ≫
      (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfBottomFiberIso R).inv

include adj SC SD cofC in
/-- 右導来関手は、元の両包含を両端とする Cartesian な輸送 prism を持つ。 -/
lemma quillenCfRightDerived_transport :
    ∃ H : (Δ[1] : SSet.{max u v}) ⊗ SimplicialNerve (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects D) ⟶
        _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.QuillenCfCollageInfinity R,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ H =
        quillenCfRightDerived R adj SC SD cofC ≫ _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageBottomNerve R ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ H = _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageTopNerve R ∧
      H ≫ _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageProjection R = fst (Δ[1] : SSet.{max u v}) _ ∧
      ∀ v : (SimplicialNerve (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects D)) _⦋0⦌,
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageProjection R)
          (H.app (Opposite.op ⦋1⦌)
            (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{max u v})), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant v 1)) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.quillenCfCollageProjection_cartesianFibration R adj SC SD cofC
  obtain ⟨H, h0, h1, hb, hc⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgeTransport_witness
    (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageProjection R) _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge
  refine ⟨((Δ[1] : SSet.{max u v}) ◁ (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfTopFiberIso R).hom) ≫ H,
    ?_, ?_, ?_, ?_⟩
  · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc, h0]
    change (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfTopFiberIso R).hom ≫ _ =
      ((_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfTopFiberIso R).hom ≫ _ ≫ (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfBottomFiberIso R).inv) ≫ _
    rw [← _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfBottomFiberIso_hom_ι]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc, h1,
      _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfTopFiberIso_hom_ι]
  · rw [Category.assoc, hb]
    have he : SSet.yonedaEquiv.symm _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge =
        (𝟙 (Δ[1] : SSet.{max u v})) := by
      apply SSet.yonedaEquiv.injective
      rw [Equiv.apply_symm_apply]
      apply SSet.stdSimplex.ext
      intro i
      fin_cases i <;> rfl
    rw [he, Category.comp_id]
    rfl
  · intro v
    change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageProjection R)
      (H.app (Opposite.op ⦋1⦌) (_, (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfTopFiberIso R).hom.app _
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant v 1)))
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map]
    exact hc ((_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfTopFiberIso R).hom.app _ v)

end
end SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions
