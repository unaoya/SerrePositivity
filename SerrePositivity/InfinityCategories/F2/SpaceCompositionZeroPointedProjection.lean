module

public import SerrePositivity.InfinityCategories.F2.SpaceCompositionZeroPointedHomotopy
public import SerrePositivity.InfinityCategories.F2.SpacePrefixConeProjection
public import SerrePositivity.InfinityCategories.F2.FunctorHomotopyTensorProjection
public import SerrePositivity.InfinityCategories.F2.PointedCoherentPrecompositionProjection

/-!
概要：元の零面への全 Hom 係数の実円柱は最大化図式を全時刻で固定する。
方針：実 coslice 円柱の tail の計算を同じ全前合成へ移す。
規約：元の全係数・円柱・射影を保持する。
使われ方：指定比較の元の相対延長空間への入力。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable (s : SpaceInfinity.{u} _⦋2⦌)
local notation "K" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 0))
local notation "A" => spaceSimplexPointedCoefficients s
local notation "M" => coherentSimplexMaximalization s
local notation "H" => spaceCompositionTetrahedronZeroCosliceHomotopy s
local notation "E" => coherentCosliceSourcePrecomposition pointKanObject K ≫
  pointedCoherentCosliceIso.hom
local notation "q" => sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex K))

/-- 元の全 pointed 円柱の射影は時刻に依存せず同じ最大化図式。 -/
lemma spaceCompositionZeroPointedHomotopy_projection :
    (spaceCompositionZeroPointedHomotopy s).h ≫ pointedSpaceProjection =
      fst ((Δ[2] : SSet.{u + 1}) ⊗ A) Δ[1] ≫
        (fst Δ[2] A ≫ SSet.yonedaEquiv.symm M) := by
  have hH : (spaceCompositionTetrahedronZeroCosliceHomotopy s).h ≫ q =
      fst Δ[2] Δ[1] ≫ SSet.yonedaEquiv.symm M :=
    spacePrefixConeCosliceMap_projection (coherentCompositionTetrahedron s) s
      (coherentCompositionTetrahedron_face_zero s)
  have hp := functorHomotopyTensorRight_postcomp_projection H A E pointedSpaceProjection q
    (SSet.yonedaEquiv.symm M) (pointedCoherentSourcePrecomposition_projection K) hH
  have he : (spaceCompositionZeroPointedHomotopy s).h =
      (spaceCompositionZeroPointedRawHomotopy s).h :=
    functorHomotopyOfEndpointEq_h (spaceCompositionZeroPointedRawHomotopy s)
      (spaceCompositionStandardFamily_eq_coslice s).symm
      (spaceCompositionZeroFamily_eq_coslice s).symm
  exact (congrArg (fun h ↦ h ≫ pointedSpaceProjection) he).trans hp

end SerrePositivity.InfinityCategories.F2
