module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SpaceCompositionZeroEndpointStandard
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SpaceCompositionZeroEndpointAction
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedCoherentHomComposition

/-!
概要：既存の指定比較の実終点円柱は元の反転精密化の全 Hom 合成作用。
方針：同じ実 coslice 辺の標準比較表示を、全 Hom の合成則へ代入する。
規約：元の全係数・終点 fiber・実円柱を保持する。
使われ方：長辺の値式に元の指定精密化の合成作用を入力する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable (s : SpaceInfinity.{u} _⦋2⦌)
local notation "K" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 0))
local notation "L" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 2))
local notation "A" => spaceSimplexPointedCoefficients s
local notation "j" => simplexPrismVertex 2 2 A
local notation "y" => coherentNerveVertex L
local notation "D" => SSet.yonedaEquiv.symm
  (ULift.up (SSet.opObjEquiv.symm (coherentTriangleHomotopy s)))
local notation "B" => coherentCosliceFiberComparison K L ≫ vertexFiberι
  (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex K))) y

/-- 指定比較の実終点円柱は元の指定精密化の反転による全 Hom の合成作用。 -/
lemma spaceCompositionZeroEndpointEdge_hom_action :
    uncurry (SSet.yonedaEquiv.symm
      (spaceCompositionZeroEndpointEdge s j y (spaceCompositionZeroEndpoint_base s)).edge) ≫
        vertexFiberι pointedSpaceProjection y =
      lift (snd A Δ[1] ≫ D) (fst A Δ[1]) ≫
        (uliftTensorIso (SimplicialCategory.sHom K L).op
          (SimplicialCategory.sHom pointKanObject K).op).inv ≫
        (SSet.uliftFunctor.{u + 1, u}).map (oppositeHomPrecomposition pointKanObject K L) ≫
          pointedCoherentFiberComparison L ≫ vertexFiberι pointedSpaceProjection y := by
  let P : A ⊗ Δ[1] ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K L).op ⊗ A :=
    lift (snd A Δ[1] ≫ D) (fst A Δ[1])
  have hl : P ≫ (B ▷ A) =
      lift (snd A Δ[1] ≫ spaceCompositionZeroCosliceEndpoint s) (fst A Δ[1]) := by
    dsimp only [P]
    rw [lift_whiskerRight, spaceCompositionZeroCosliceEndpoint_eq_standard]
    rfl
  have h := congrArg (fun f ↦ P ≫ f) (pointedCoherentSourcePrecomposition_hom K L)
  rw [← Category.assoc, ← Category.assoc, hl] at h
  exact (spaceCompositionZeroEndpointEdge_action s).trans h

end SerrePositivity.InfinityCategories.F2
