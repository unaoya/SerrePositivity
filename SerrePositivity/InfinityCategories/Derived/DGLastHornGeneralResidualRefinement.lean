module
public import SerrePositivity.InfinityCategories.Derived.DGYonedaVerdierCone
public import SerrePositivity.InfinityCategories.Derived.DGLastHornGeneralYonedaResidual
public import SerrePositivity.InfinityCategories.Derived.DGVerdierTriangleLastDenominator
public import SerrePositivity.InfinityCategories.Derived.DGFiniteCellSimultaneousPrimitives

/-! # 一般最後外ホーンの cone 残差の追加実閉分母後の原始元

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
variable {n : ℕ}
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] [Small.{u} D]

/-- 元の指定残差に、追加実閉分母後の具体的な加群 Hom 原始元を持たせた細分データ。 -/
structure DGGeneralLastHornResidualRefinement (P : Set D)
    (σ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{max u v}) ⟶ dgNerve A D) where
  q : D
  s : ForgetEnrichment.of (Complex A) q ⟶
    ForgetEnrichment.of (Complex A) ((HornData.knownData σ).obj 0)
  denominator : (dgClosedEdge A D s).edge ∈ dgVerdierEdges A D P
  primitive : GradedHom A (representable A q)
    (ForgetEnrichment.to (Complex A) (dgGeneralLastHornYonedaCone σ)) (-(n : ℤ) - 1)
  differential_primitive :
    (moduleHom A D (representable A q)
      (ForgetEnrichment.to (Complex A) (dgGeneralLastHornYonedaCone σ))).d (-(n : ℤ) - 1)
        (-(n : ℤ)) primitive =
        dgRepresentableModulePrecompose A D (-(n : ℤ)) (dgGeneralLastHornYonedaResidual σ) s

variable [IsDGPretriangulated A D]

/-- 実最後辺が指定分母なら、元の cone 残差の追加閉分母後の原始元は実際に存在する。 -/
theorem dgGeneralLastHornResidualRefinement_nonempty (P : Set D)
    (σ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{max u v}) ⟶ dgNerve A D)
    (hW : (dgClosedEdge A D (dgGeneralLastHornFinalClosed σ)).edge ∈ dgVerdierEdges A D P) :
    Nonempty (DGGeneralLastHornResidualRefinement P σ) := by
  have hM := dgYonedaVerdierCone_derivedFiniteCell A D P (dgGeneralLastHornFinalClosed σ) hW
  have hf : differential A (D := RightModule A D)
      (x := representable A ((HornData.knownData σ).obj 0))
      (y := ForgetEnrichment.to (Complex A) (dgGeneralLastHornYonedaCone σ)) (n := -(n : ℤ))
      (dgGeneralLastHornYonedaResidual σ) = 0 :=
    dgGeneralLastHornYonedaResidual_closed σ
  obtain ⟨q, s, hs, h, dh⟩ := dgFiniteCellGraded_exists_closedPrimitive A D P
    ((HornData.knownData σ).obj 0) (dgGeneralLastHornYonedaCone σ) hM (-(n : ℤ)) (-(n : ℤ) -
      1) (by omega)
    (dgGeneralLastHornYonedaResidual σ) hf
  exact ⟨⟨q, s, hs, h, dh⟩⟩

end SerrePositivity.InfinityCategories
