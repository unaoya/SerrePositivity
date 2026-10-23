module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SpaceCompositionZeroPointedHomotopy
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SpaceCompositionZeroCosliceInitial
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorHomotopyTensorInitial
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedCoherentIdentityAction

/-!
概要：零面の全 Hom 係数の実 pointed 円柱は同じ全初点を固定する。
方針：元の coslice 円柱の初点固定と恒等点の全係数作用を合成する。
規約：元の実円柱・標準 fiber 比較・全独立係数を保持する。
使われ方：指定比較と同じ可縮な相対延長空間への入力。
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
local notation "H" => spaceCompositionTetrahedronZeroCosliceHomotopy s
local notation "E" => coherentCosliceSourcePrecomposition pointKanObject K ≫
  pointedCoherentCosliceIso.hom
local notation "i" => scaffoldFirstVertex 2 ▷ A
local notation "v" => snd Δ[0] A ≫ pointedCoherentFiberComparison K ≫
  vertexFiberι pointedSpaceProjection (coherentNerveVertex K)

/-- 元の全係数円柱は同じ全初点族に厳密に固定される。 -/
lemma spaceCompositionZeroPointedHomotopy_initial :
    (i ▷ Δ[1]) ≫ (spaceCompositionZeroPointedHomotopy s).h = fst (Δ[0] ⊗ A) Δ[1] ≫ v := by
  have hp := functorHomotopyTensorRight_postcomp_initial H A E (scaffoldFirstVertex 2)
    (cosliceIdentityPoint (coherentNerveVertex K)) v
    (spaceCompositionZeroCosliceHomotopy_initial s)
    (pointedCoherentSourcePrecomposition_identity_action K)
  exact (congrArg (fun h ↦ (i ▷ Δ[1]) ≫ h)
    (spaceCompositionZeroPointedHomotopy_h s)).trans hp

end SerrePositivity.InfinityCategories.F2
