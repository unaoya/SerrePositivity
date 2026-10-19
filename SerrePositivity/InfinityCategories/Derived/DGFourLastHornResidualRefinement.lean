module
public import SerrePositivity.InfinityCategories.Derived.DGYonedaVerdierCone
public import SerrePositivity.InfinityCategories.Derived.DGFourLastHornYonedaResidual
public import SerrePositivity.InfinityCategories.Derived.DGVerdierTriangleLastDenominator
public import SerrePositivity.InfinityCategories.Derived.DGFiniteCellSimultaneousPrimitives

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] [Small.{u} D]

/-- 元の指定残差に、追加実閉分母後の具体的な加群 Hom 原始元を持たせた細分データ。 -/
structure DGFourLastHornResidualRefinement (P : Set D)
    (σ : (Λ[4, 4] : SSet.{max u v}) ⟶ dgNerve A D) where
  q : D
  s : ForgetEnrichment.of (Complex A) q ⟶
    ForgetEnrichment.of (Complex A) ((HornData.knownData σ).obj 0)
  denominator : (dgClosedEdge A D s).edge ∈ dgVerdierEdges A D P
  primitive : GradedHom A (representable A q)
    (ForgetEnrichment.to (Complex A) (dgFourLastHornYonedaCone σ)) (-3)
  differential_primitive :
    (moduleHom A D (representable A q)
      (ForgetEnrichment.to (Complex A) (dgFourLastHornYonedaCone σ))).d (-3) (-2) primitive =
        dgRepresentableModulePrecompose A D (-2) (dgFourLastHornYonedaResidual σ) s

variable [IsDGPretriangulated A D]

/-- 実最後辺が指定分母なら、元の cone 残差の追加閉分母後の原始元は実際に存在する。 -/
theorem dgFourLastHornResidualRefinement_nonempty (P : Set D)
    (σ : (Λ[4, 4] : SSet.{max u v}) ⟶ dgNerve A D)
    (hW : (dgClosedEdge A D (dgFourLastHornFinalClosed σ)).edge ∈ dgVerdierEdges A D P) :
    Nonempty (DGFourLastHornResidualRefinement P σ) := by
  have hM := dgYonedaVerdierCone_derivedFiniteCell A D P (dgFourLastHornFinalClosed σ) hW
  have hf : differential A (D := RightModule A D)
      (x := representable A ((HornData.knownData σ).obj 0))
      (y := ForgetEnrichment.to (Complex A) (dgFourLastHornYonedaCone σ)) (n := -2)
      (dgFourLastHornYonedaResidual σ) = 0 :=
    dgFourLastHornYonedaResidual_closed σ
  obtain ⟨q, s, hs, h, dh⟩ := dgFiniteCellGraded_exists_closedPrimitive A D P
    ((HornData.knownData σ).obj 0) (dgFourLastHornYonedaCone σ) hM (-2) (-3) (by decide)
    (dgFourLastHornYonedaResidual σ) hf
  exact ⟨⟨q, s, hs, h, dh⟩⟩

/-- 任意の実図式二単体と指定三辺錐の残差には、追加実閉分母後の原始元が存在する。 -/
theorem dgVerdierTriangleResidualRefinement_nonempty (P : Set D) (x : D)
    {K : SSet.{max u v}} {f : K ⟶ (dgVerdierOver A D P x : SSet.{max u v})}
    (C : DGVerdierDiagramVertexCone A D P x f) (σ : K _⦋2⦌)
    (H : ∀ i : Fin 3, Truncated.Edge.CompStruct
      (C.leg (K.δ 1 (K.δ i σ)))
      ((edgeOfSimplex (K.δ i σ)).map ((truncation 2).map f))
      (C.leg (K.δ 0 (K.δ i σ)))) :
    Nonempty (DGFourLastHornResidualRefinement P (dgVerdierDiagramTriangleHorn A D C σ H)) :=
  dgFourLastHornResidualRefinement_nonempty P (dgVerdierDiagramTriangleHorn A D C σ H)
    (dgVerdierDiagramTriangleLastClosed_mem A D C σ H)

end SerrePositivity.InfinityCategories
