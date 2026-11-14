module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGYonedaVerdierCone
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.HornFillers.DGFourLastHornYonedaResidual
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGVerdierTriangleLastDenominator
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGFiniteCellSimultaneousPrimitives

/-! # 実四次最後外ホーンの cone 残差の追加実閉分母後の原始元

概要：最後辺が実 Verdier 分母なら、元の実 cone 残差に追加閉分母後の原始元を供給する。
方針：同じ残差の Yoneda 像を有限 cell 加群標的に入れ、導来零化から原始元を戻す。
規約：細分された実ホーンとの照合は別工程。使われ方：実図式辺の整合性の存在証明。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]

/-- 元の指定残差に、追加実閉分母後の具体的な加群 Hom 原始元を持たせた細分データ。 -/
structure DGFourLastHornResidualRefinement (P : Set D)
    (σ : (Λ[4, 4] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) where
  q : D
  s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶
    ForgetEnrichment.of (Complex A) ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)
  denominator : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P
  primitive : _root_.SerrePositivity.DifferentialGraded.GradedHom A (_root_.SerrePositivity.DifferentialGraded.representable A q)
    (ForgetEnrichment.to (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornYonedaCone σ)) (-3)
  differential_primitive :
    (_root_.SerrePositivity.DifferentialGraded.moduleHom A D (_root_.SerrePositivity.DifferentialGraded.representable A q)
      (ForgetEnrichment.to (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornYonedaCone σ))).d (-3) (-2) primitive =
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableModulePrecompose A D (-2) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornYonedaResidual σ) s

variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]

/-- 実最後辺が指定分母なら、元の cone 残差の追加閉分母後の原始元は実際に存在する。 -/
theorem dgFourLastHornResidualRefinement_nonempty (P : Set D)
    (σ : (Λ[4, 4] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (hW : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornFinalClosed σ)).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P) :
    Nonempty (DGFourLastHornResidualRefinement P σ) := by
  have hM := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgYonedaVerdierCone_derivedFiniteCell A D P (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornFinalClosed σ) hW
  have hf : _root_.SerrePositivity.DifferentialGraded.differential A (D := _root_.SerrePositivity.DifferentialGraded.RightModule A D)
      (x := representable A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0))
      (y := ForgetEnrichment.to (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornYonedaCone σ)) (n := -2)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornYonedaResidual σ) = 0 :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornYonedaResidual_closed σ
  obtain ⟨q, s, hs, h, dh⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFiniteCellGraded_exists_closedPrimitive A D P
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornYonedaCone σ) hM (-2) (-3) (by decide)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornYonedaResidual σ) hf
  exact ⟨⟨q, s, hs, h, dh⟩⟩

/-- 任意の実図式二単体と指定三辺錐の残差には、追加実閉分母後の原始元が存在する。 -/
theorem dgVerdierTriangleResidualRefinement_nonempty (P : Set D) (x : D)
    {K : SSet.{max u v}} {f : K ⟶ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet.{max u v})}
    (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierDiagramVertexCone A D P x f) (σ : K _⦋2⦌)
    (H : ∀ i : Fin 3, Truncated.Edge.CompStruct
      (C.leg (K.δ 1 (K.δ i σ)))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (K.δ i σ)).map ((truncation 2).map f))
      (C.leg (K.δ 0 (K.δ i σ)))) :
    Nonempty (DGFourLastHornResidualRefinement P (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramTriangleHorn A D C σ H)) :=
  dgFourLastHornResidualRefinement_nonempty P (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramTriangleHorn A D C σ H)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramTriangleLastClosed_mem A D C σ H)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
