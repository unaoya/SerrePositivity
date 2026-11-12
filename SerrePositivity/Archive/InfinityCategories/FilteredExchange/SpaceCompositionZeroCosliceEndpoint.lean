module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceCompositionTetrahedronZeroCylinder
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpacePrefixConeProjection
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCompositionTetrahedronStrictFace
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCompositionEndpointRefinement
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SimplexPrismFirstVertex

/-!
概要：零面の実 coslice 円柱の終点辺と元の指定精密化の座標を保持する。
方針：同じ全円柱を終頂点で制限し、prefix 単体の実座標を取り出す。
規約：辺を選び直さず、元の終点対象と指定豊穣辺を保持する。
使われ方：既存の指定比較の終点像の全 Hom 作用の照合。
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
local notation "L" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 2))

/-- 同じ元の円柱を終頂点へ制限した実 coslice 辺。 -/
def spaceCompositionZeroCosliceEndpoint : (Δ[1] : SSet.{u + 1}) ⟶
    sliceUnder (SSet.yonedaEquiv.symm (coherentNerveVertex K)) :=
  simplexPrismVertex 2 2 Δ[1] ≫ (spaceCompositionTetrahedronZeroCosliceHomotopy s).h

/-- 終点辺の実 join 座標は同じ元の prefix 三角形。 -/
lemma spaceCompositionZeroCosliceEndpoint_coordinates :
    coherentCosliceSourceSimplex K (SSet.yonedaEquiv (spaceCompositionZeroCosliceEndpoint s)) =
      coherentPrefixConeSimplex (coherentCompositionTetrahedron s)
        (OrderHom.const (Fin 2) (2 : Fin 3)) (OrderHom.id (α := Fin 2)) :=
  spacePrefixConeCosliceSimplex_coordinates (coherentCompositionTetrahedron s)
    (OrderHom.const (Fin 2) (2 : Fin 3)) (OrderHom.id (α := Fin 2))

/-- 終点辺から読む実豊穣一単体は元の指定精密化そのもの。 -/
lemma spaceCompositionZeroCosliceEndpoint_refinement :
    coherentTriangleHomotopy
      (coherentCosliceSourceSimplex K (SSet.yonedaEquiv (spaceCompositionZeroCosliceEndpoint s))) =
        coherentTriangleHomotopy s := by
  have hh : ∀ {a b : SpaceInfinity.{u} _⦋2⦌}, a = b →
      HEq (coherentTriangleHomotopy a) (coherentTriangleHomotopy b) := by
    intro a b h
    cases h
    rfl
  have h : HEq
      (coherentTriangleHomotopy (coherentCosliceSourceSimplex K
        (SSet.yonedaEquiv (spaceCompositionZeroCosliceEndpoint s))))
      (coherentTriangleHomotopy (coherentPrefixConeSimplex (coherentCompositionTetrahedron s)
        (OrderHom.const (Fin 2) (2 : Fin 3)) (OrderHom.id (α := Fin 2)))) :=
    hh (spaceCompositionZeroCosliceEndpoint_coordinates s)
  exact eq_of_heq (h.trans (heq_of_eq (coherentCompositionEndpoint_refinement s)))

/-- 元の実終点辺は同じ終点対象の coslice fiber に全体として入る。 -/
lemma spaceCompositionZeroCosliceEndpoint_projection :
    spaceCompositionZeroCosliceEndpoint s ≫
      sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex K)) =
        SSet.const (coherentNerveVertex L) := by
  have hp : (spaceCompositionTetrahedronZeroCosliceHomotopy s).h ≫
      sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex K)) =
        fst Δ[2] Δ[1] ≫ SSet.yonedaEquiv.symm (coherentSimplexMaximalization s) :=
    spacePrefixConeCosliceMap_projection (coherentCompositionTetrahedron s) s
      (coherentCompositionTetrahedron_face_zero s)
  have hv : (SSet.yonedaEquiv.symm (coherentSimplexMaximalization s)).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (2 : Fin 3)) = coherentNerveVertex L := by
    apply (coherentNerveVertexEquiv KanObject).symm.injective
    rfl
  rw [spaceCompositionZeroCosliceEndpoint, Category.assoc, hp, ← Category.assoc,
    simplexPrismVertex, lift_fst, SSet.const_comp, hv]

/-- 元の実 coslice 終点辺を同じ元の終点 fiber に保持する射。 -/
def spaceCompositionZeroCosliceEndpointFiber : (Δ[1] : SSet.{u + 1}) ⟶
    vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex K)))
      (coherentNerveVertex L) :=
  vertexFiberLift _ _ (spaceCompositionZeroCosliceEndpoint s)
    (spaceCompositionZeroCosliceEndpoint_projection s)

/-- fiber への表示を加えても元の実終点辺は同じ射。 -/
lemma spaceCompositionZeroCosliceEndpointFiber_ι :
    spaceCompositionZeroCosliceEndpointFiber s ≫ vertexFiberι
      (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex K)))
      (coherentNerveVertex L) = spaceCompositionZeroCosliceEndpoint s := rfl

end SerrePositivity.InfinityCategories.F2
