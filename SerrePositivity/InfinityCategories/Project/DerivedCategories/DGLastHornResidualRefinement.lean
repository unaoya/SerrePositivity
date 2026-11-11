module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGYonedaVerdierCone
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFiniteCellSimultaneousPrimitives

/-! # 実最後外ホーンの cone 残差の追加実閉分母後の原始元

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
structure DGLastHornResidualRefinement (P : Set D)
    (σ : (Λ[3, 3] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) where
  q : D
  s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶
    ForgetEnrichment.of (Complex A) ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)
  denominator : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P
  primitive : _root_.SerrePositivity.DifferentialGraded.GradedHom A (_root_.SerrePositivity.DifferentialGraded.representable A q)
    (ForgetEnrichment.to (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornYonedaCone σ)) (-2)
  differential_primitive :
    (_root_.SerrePositivity.DifferentialGraded.moduleHom A D (_root_.SerrePositivity.DifferentialGraded.representable A q)
      (ForgetEnrichment.to (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornYonedaCone σ))).d (-2) (-1) primitive =
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableModulePrecompose A D (-1) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornYonedaResidual σ) s

variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]

/-- 実最後辺が指定分母なら、元の cone 残差の追加閉分母後の原始元は実際に存在する。 -/
theorem dgLastHornResidualRefinement_nonempty (P : Set D)
    (σ : (Λ[3, 3] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (hW : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornFinalClosed σ)).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P) :
    Nonempty (DGLastHornResidualRefinement P σ) := by
  have hM := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgYonedaVerdierCone_derivedFiniteCell A D P (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornFinalClosed σ) hW
  have hf : _root_.SerrePositivity.DifferentialGraded.differential A (D := _root_.SerrePositivity.DifferentialGraded.RightModule A D)
      (x := representable A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0))
      (y := ForgetEnrichment.to (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornYonedaCone σ)) (n := -1)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornYonedaResidual σ) = 0 :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornYonedaResidual_closed σ
  obtain ⟨q, s, hs, h, dh⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFiniteCellGraded_exists_closedPrimitive A D P
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornYonedaCone σ) hM (-1) (-2) (by decide)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornYonedaResidual σ) hf
  exact ⟨⟨q, s, hs, h, dh⟩⟩

/-- 任意の実図式辺と二脚から来る指定残差には、追加実閉分母後の原始元が存在する。 -/
theorem dgVerdierDiagramResidualRefinement_nonempty (P : Set D) (x : D)
    {K : SSet.{max u v}} {f : K ⟶ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet.{max u v})}
    (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierDiagramVertexCone A D P x f) (a : K _⦋1⦌) :
    Nonempty (DGLastHornResidualRefinement P (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramEdgeHorn A D C a)) :=
  dgLastHornResidualRefinement_nonempty P (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramEdgeHorn A D C a)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramLastClosed_mem A D P x C a)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
