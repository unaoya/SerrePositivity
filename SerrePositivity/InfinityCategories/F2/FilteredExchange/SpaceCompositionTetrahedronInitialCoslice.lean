module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCompositionTetrahedronFirstEdge
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SpaceSimplexSourceConeInitial
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SpaceCosliceEdgeComponent

/-!
概要：合成比較三単体の第二頂点でも元の恒等 coslice 点を回収する。
方針：coslice の座標を実際の最初の辺へ制限し、その恒等辺の式を使う。
規約：元の初点と同じ全反転 Hom 係数を保つ。
使われ方：零面の pointed 族の始点を固定する。
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
local notation "T" => coherentCompositionTetrahedron s
local notation "K" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 0))

/-- 第二頂点における coslice の座標は元の初点の恒等辺。 -/
lemma spaceCompositionTetrahedron_second_coslice_coordinates :
    coherentCosliceSourceSimplex K
      ((sliceUnder (SSet.yonedaEquiv.symm (coherentNerveVertex K))).map
        (SimplexCategory.const ⦋0⦌ ⦋3⦌ 1).op (spaceSimplexSourceCone T)) =
      PinchedHom.constant (coherentNerveVertex K) 1 := by
  let α := SimplexCategory.const ⦋0⦌ ⦋3⦌ 1
  refine (coherentCosliceSourceSimplex_reindex _ α (spaceSimplexSourceCone T)).symm.trans ?_
  change SpaceInfinity.map (SimplexCategory.mkHom (prependOrderHom α.toOrderHom)).op
    (coherentCosliceSourceSimplex _ (spaceSimplexSourceCone T)) = _
  rw [spaceSimplexSourceCone_coordinates, coherentConeTailExtension_eq_sigmaZero]
  change SpaceInfinity.map (SimplexCategory.mkHom (prependOrderHom α.toOrderHom)).op
    (SpaceInfinity.map (SimplexCategory.σ 0).op T) = _
  rw [← CategoryTheory.Functor.map_comp_apply, ← op_comp]
  have h : SimplexCategory.mkHom (prependOrderHom α.toOrderHom) ≫ SimplexCategory.σ 0 =
      SimplexCategory.δ (2 : Fin 3) ≫ SimplexCategory.δ (3 : Fin 4) := by
    ext j
    fin_cases j <;> rfl
  rw [h, op_comp, CategoryTheory.Functor.map_comp_apply]
  exact coherentCompositionTetrahedron_first_edge s

/-- 第二頂点の実 coslice 点は第一頂点の実 coslice 点そのもの。 -/
lemma spaceCompositionTetrahedron_second_coslice_vertex :
    (SSet.yonedaEquiv.symm (spaceSimplexSourceCone T)).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 4)) =
    (SSet.yonedaEquiv.symm (spaceSimplexSourceCone T)).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 4)) := by
  apply spaceCosliceSourceSimplex_injective K 0
  exact (spaceCompositionTetrahedron_second_coslice_coordinates s).trans
    (spaceSimplexSourceCone_initial_coordinates T).symm

end SerrePositivity.InfinityCategories.F2
