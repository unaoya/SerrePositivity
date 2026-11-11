module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCompositionEndpointSimplex
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceCompositionZeroCosliceEndpoint
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceCosliceEdgeComponent
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.WeightedConstantSimplex

/-!
概要：元の実 coslice 終点辺は元の指定精密化の反転を標準 Hom 比較へ送った辺。
方針：同じ fiber の全三角形座標で検出し、weighted cone との全 Hom の一致を使う。
規約：元の実円柱と元の終点 fiber を保持する。
使われ方：指定比較の終点像を元の反転 Hom 合成作用へ戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable (s : SpaceInfinity.{u} _⦋2⦌)
local notation "K" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 0))
local notation "L" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 2))

/-- 実終点辺は同じ fiber 内で元の精密化の反転の標準 Hom 比較による像に等しい。 -/
lemma spaceCompositionZeroCosliceEndpointFiber_eq_standard :
    spaceCompositionZeroCosliceEndpointFiber s =
      SSet.yonedaEquiv.symm (ULift.up (SSet.opObjEquiv.symm (coherentTriangleHomotopy s))) ≫
        coherentCosliceFiberComparison K L := by
  let F := (Functor.const (Discrete PUnit.{u + 1})).obj L
  let α := SSet.opObjEquiv.symm (coherentTriangleHomotopy s)
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_symm_comp, Equiv.apply_symm_apply]
  apply Equiv.injective
    (cosliceFiberSimplexEquiv (coherentNerveVertex K) (coherentNerveVertex L) 1)
  apply Subtype.ext
  change coherentCosliceSourceSimplex K
    (SSet.yonedaEquiv (spaceCompositionZeroCosliceEndpoint s)) =
      cosliceFiberSimplex 1
        ((coherentCosliceFiberComparison K L).app (Opposite.op ⦋1⦌) (ULift.up α))
  rw [spaceCompositionZeroCosliceEndpoint_coordinates]
  have h := weightedConstantCosliceFiberMap_simplex F K
    (⟨PUnit.unit⟩ : Discrete PUnit.{u + 1}) α
  rw [weightedConstantCosliceFiberMap_eq] at h
  exact (coherentCompositionEndpoint_simplex_weighted s).trans h.symm

/-- fiber の包含後も元の実終点辺は同じ標準比較の像。 -/
lemma spaceCompositionZeroCosliceEndpoint_eq_standard :
    spaceCompositionZeroCosliceEndpoint s =
      SSet.yonedaEquiv.symm (ULift.up (SSet.opObjEquiv.symm (coherentTriangleHomotopy s))) ≫
        coherentCosliceFiberComparison K L ≫ vertexFiberι
          (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex K)))
            (coherentNerveVertex L) := by
  have h := congrArg (fun f ↦ f ≫ vertexFiberι
      (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex K)))
        (coherentNerveVertex L)) (spaceCompositionZeroCosliceEndpointFiber_eq_standard s)
  rw [spaceCompositionZeroCosliceEndpointFiber_ι] at h
  exact h.trans (Category.assoc _ _ _)

end SerrePositivity.InfinityCategories.F2
