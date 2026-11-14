module

public import SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.QuillenCfDerivedTransport
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.CartesianPrismComparison

/-!
概要：元の左右導来関手の輸送を比較し、下段 cf nerve 上の自然な単位候補を構成する。
方針：右の輸送を左導来関手で引き戻して比較正方形へ代入し、零 fiber の同型で戻す。
規約：元の輸送と正方形の証人を保持し、随伴性や三角恒等式は追加の証明を要する。
使われ方：HTT 5.2.4.6、F1b の指定単位による随伴判定への入力。
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


variable (cofC : MorphismProperty.FunctorialFactorizationData
  (cofibrations C) (trivialFibrations C))
include fibD e SC SD cofC in
/-- 元の両輸送と比較正方形を保持した、下段 cf nerve 上の自然な単位 prism の存在。 -/
lemma quillenCfDerivedUnitPrism_exists :
    ∃ (η : (Δ[1] : SSet.{max u v}) ⊗ SimplicialNerve (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects C) ⟶
        SimplicialNerve (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects C))
      (HL : (Δ[1] : SSet.{max u v}) ⊗ SimplicialNerve (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects C) ⟶
        _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.QuillenCfCollageInfinity R)
      (HR : (Δ[1] : SSet.{max u v}) ⊗ SimplicialNerve (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects D) ⟶
        _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.QuillenCfCollageInfinity R)
      (J : (Δ[1] : SSet.{max u v}) ⊗
        ((Δ[1] : SSet.{max u v}) ⊗ SimplicialNerve (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects C)) ⟶
          _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.QuillenCfCollageInfinity R),
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ η = 𝟙 _ ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ η =
        _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfLeftDerived R adj fibD e SC SD ≫ _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfRightDerived R adj SC SD cofC ∧
      η ≫ _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageBottomNerve R = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ J ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ HL = _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageBottomNerve R ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ HL =
        _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfLeftDerived R adj fibD e SC SD ≫ _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageTopNerve R ∧
      HL ≫ _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageProjection R = fst (Δ[1] : SSet.{max u v}) _ ∧
      (∀ x, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageProjection R)
        (HL.app (Opposite.op ⦋1⦌)
          (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{max u v})), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1))) ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ HR =
        _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfRightDerived R adj SC SD cofC ≫ _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageBottomNerve R ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ HR = _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageTopNerve R ∧
      HR ≫ _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageProjection R = fst (Δ[1] : SSet.{max u v}) _ ∧
      (∀ x, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageProjection R)
        (HR.app (Opposite.op ⦋1⦌)
          (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{max u v})), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1))) ∧
      ((Δ[1] : SSet.{max u v}) ◁ ((boundary 1).ι ▷
        SimplicialNerve (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects C))) ≫ J = _root_.SerrePositivity.InfinityCategories.HTT.Section2_4_1.cartesianComparisonBoundary HL
          (((Δ[1] : SSet.{max u v}) ◁ _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfLeftDerived R adj fibD e SC SD) ≫ HR) ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ J = HL ∧
      J ≫ _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageProjection R = ((Δ[1] : SSet.{max u v}) ◁
        fst (Δ[1] : SSet.{max u v}) _) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismFirstContraction 1 ∧
      ∀ x, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageProjection R)
        (J.app (Opposite.op ⦋1⦌)
          (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{max u v})), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1)) := by
  let F := _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfLeftDerived R adj fibD e SC SD
  let G := _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfRightDerived R adj SC SD cofC
  obtain ⟨HL, hL0, hL1, hLp, hLc⟩ := _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfLeftDerived_transport R adj fibD e SC SD
  obtain ⟨HR, hR0, hR1, hRp, hRc⟩ := _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfRightDerived_transport R adj SC SD cofC
  let K := ((Δ[1] : SSet.{max u v}) ◁ F) ≫ HR
  have hKp : K ≫ _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageProjection R = fst (Δ[1] : SSet.{max u v}) _ := by
    dsimp only [K]
    rw [Category.assoc, hRp]
    rfl
  have hK1 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ K = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ HL := by
    dsimp only [K]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc, hR1, hL1]
  have hKc : ∀ x, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageProjection R)
      (K.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{max u v})), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1)) := by
    intro x
    change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageProjection R)
      (HR.app (Opposite.op ⦋1⦌) (_, F.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1)))
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map]
    exact hRc (F.app _ x)
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.quillenCfCollageProjection_cartesianFibration R adj SC SD cofC
  obtain ⟨J, hJb, hJ1, hJp, hJc⟩ :=
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.exists_cartesianPrismComparison (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageProjection R) HL K hLp hKp hK1 hKc
  let α := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ J
  have hαp : α ≫ _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageProjection R =
      SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) :=
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.cartesianPrismComparison_unit_base _ J hJp
  have hαb := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.cartesianPrismComparison_unit_boundary HL K J hJb
  have hα0 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ α = _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageBottomNerve R := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint_ι 0, Category.assoc, hαb,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_zero, hL0]
  have hα1 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ α = (F ≫ G) ≫ _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageBottomNerve R := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint_ι 1, Category.assoc, hαb,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_one]
    dsimp only [K]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc, hR0]
    rfl
  let ηf := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageProjection R)
    (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) α hαp
  let η := ηf ≫ (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfBottomFiberIso R).inv
  have hηi : η ≫ _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageBottomNerve R = α := by
    dsimp only [η]
    rw [← _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfBottomFiberIso_hom_ι]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι _ _ _ _
  have hη0 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ η = 𝟙 _ := by
    apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfBottomFiberIso R).hom).mp
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageProjection R)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2))
    simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfBottomFiberIso_hom_ι, Category.id_comp]
    rw [hηi, hα0]
  have hη1 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ η = F ≫ G := by
    apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfBottomFiberIso R).hom).mp
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageProjection R)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2))
    simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfBottomFiberIso_hom_ι]
    rw [hηi, hα1]
    exact Category.assoc _ _ _
  exact ⟨η, HL, HR, J, hη0, hη1, hηi, hL0, hL1, hLp, hLc,
    hR0, hR1, hRp, hRc, hJb, hJ1, hJp, hJc⟩

include fibD e SC SD cofC in
/-- 元の左右導来関手に対する、恒等関手から右左合成への自然なホモトピー候補。 -/
lemma quillenCfDerivedUnitHomotopy_nonempty :
    Nonempty (SSet.Homotopy (𝟙 (SimplicialNerve (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects C)))
      (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfLeftDerived R adj fibD e SC SD ≫ _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfRightDerived R adj SC SD cofC)) := by
  obtain ⟨η, HL, HR, J, h0, h1, _⟩ :=
    quillenCfDerivedUnitPrism_exists R adj fibD e SC SD cofC
  refine ⟨{ h := (β_ _ (Δ[1] : SSet.{max u v})).hom ≫ η, h₀ := ?_, h₁ := ?_, rel := ?_ }⟩
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ η = _
    exact h0
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ η = _
    exact h1
  · apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro z
    exact False.elim z.1.property

end
end SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions
