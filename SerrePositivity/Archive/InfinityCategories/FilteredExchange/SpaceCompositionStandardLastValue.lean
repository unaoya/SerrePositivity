module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceCompositionZeroLastActualEndpoint
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceTrianglePointedMaximalLastPrism
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedMorphismFixedDiagonalComparison
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedReverseDiagonalPrismFixed
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.DiagonalPrismBoundaryValue
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedFiberValueToDisplay
/-!
概要：最大化側の実最後辺の指定対角比較の値を、元の固定最後射の同じ係数制限へ戻す。
方針：指定対角比較の係数制限則と、同じ実 prism・両端・値射の等式を合成する。
規約：第一射の元の全係数作用と、指定対角比較を保持する。
使われ方：Ncomp の raw 二辺因子と最後射の値比較の接続。
-/

@[expose] public section
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories

noncomputable section
namespace SerrePositivity.InfinityCategories.F2
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
/-- 概要：係数制限後も同じ底の定値端点を保持する。
方針：prism 端点の自然性を使う。
規約：元の底を保持。使われ方：指定対角比較の制限後の実境界。 -/
private lemma prismEndpoint_precomp_const (i : Fin 2) {A C B : SSet.{u}}
    (r : C ⟶ A) (γ : (Δ[1] : SSet.{u}) ⊗ A ⟶ B) {b : B _⦋0⦌}
    (h : prismEndpoint i A ≫ γ = SSet.const b) :
    prismEndpoint i C ≫ ((Δ[1] ◁ r) ≫ γ) = SSet.const b := by
  rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, h, SSet.comp_const]
variable (s : SpaceInfinity.{u} _⦋2⦌)
local notation "p" => pointedSpaceProjection
local notation "A" => spaceSimplexPointedCoefficients s
local notation "M" => coherentSimplexMaximalization s
local notation "r" => stdSimplex.δ (0 : Fin 3) ▷ A
local notation "β" => fst Δ[2] A ≫ SSet.yonedaEquiv.symm M
local notation "L" => spaceCompositionTetrahedronZeroFamily s
local notation "j" => simplexPrismVertex 2 2 A
local notation "b" => coherentNerveVertex
  (EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 2)))
local notation "g" => spaceCompositionZeroCompositeMap s
local notation "g'" => spaceCompositionZeroTargetMap s
local notation "f" => spaceCompositionZeroMiddleMap s
local notation "h₀" => Eq.trans (Eq.symm (Category.assoc _ _ _))
  (Eq.trans (congrArg (fun t => t ≫ β) (spaceCompositionZeroLast_start s))
    (spaceCompositionZeroMiddle_base s))
local notation "h₁" => Eq.trans (Eq.symm (Category.assoc _ _ _))
  (Eq.trans (congrArg (fun t => t ≫ β) (spaceCompositionZeroLast_end s))
    (spaceCompositionZeroEndpoint_base s))


local notation "K₁" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 1))
local notation "K₂" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 2))
local notation "g₁₂" => coherentEdgeHom (SpaceInfinity.δ 0 s)
local notation "P" => CategoryTheory.Functor.map SSet.uliftFunctor
  (CategoryTheory.Functor.map SSet.opFunctor
    (eHomWhiskerLeft SSet pointKanObject (coherentEdgeHom (SpaceInfinity.δ 2 s))))
local notation "V" => QCatEquivalence.hom
  (pointedSpaceFiberValueEquivalence (spaceInfinityVertex K₂))
local notation "V'" => pointedFiberValueTo (Eq.symm (spaceInfinityVertex_eq_coherent K₂))
/-- 概要：最大化側の最後辺の指定値は、同じ元の固定最後射の値の係数制限。
方針：同じ実 prism の一致を値射まで保持して指定対角比較に反映する。
規約：全係数と指定比較を保持。使われ方：Ncomp の元の二辺評価との照合。 -/
lemma spaceCompositionStandardLastValue_heq_fixed_precomp :
    HEq ((leftFibrationPrism_diagonalTransportIso p f g (r ≫ β) h₀ h₁
      (r ≫ spaceSimplexPointedFamily M)
      (spaceCompositionZeroLast_standard_start s) (spaceCompositionZeroLast_standard_end s)
      (spaceCompositionZeroLast_standard_projection s)).postcomp V')
      (FunctorIso.precomp ((pointedMorphismFixedDiagonalComparison g₁₂).postcomp V) P) := by
  symm
  unfold pointedMorphismFixedDiagonalComparison
  refine (leftFibrationPrism_diagonalTransportIso_precomp_postcomp_heq
    p _ _ _ _ _ _ _ _ _ P ?_ ?_ V).trans ?_
  · refine prismEndpoint_precomp_const _ P _ ?_
    refine prismEndpoint_precomp_const _ _ _ ?_
    exact intervalMappingUncurry_zero _
  · refine prismEndpoint_precomp_const _ P _ ?_
    refine prismEndpoint_precomp_const _ _ _ ?_
    exact intervalMappingUncurry_one _
  · apply diagonalTransportIso_postcomp_heq_of_boundary
    · exact spaceInfinityVertex_eq_coherent K₁
    · exact spaceInfinityVertex_eq_coherent K₂
    · exact (congrArg (fun H => (Δ[1] ◁ P) ≫ H)
        (pointedReverseDiagonalPrism_fixed_eq_coherent g₁₂)).trans
        (spaceTrianglePointedFamily_maximal_last_prism s).symm
    · exact (pointedFiberValueTo_heq_value (Eq.symm (spaceInfinityVertex_eq_coherent K₂))).symm
end SerrePositivity.InfinityCategories.F2
