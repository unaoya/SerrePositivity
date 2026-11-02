module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceCompositionTetrahedronInitialCoslice
/-!
概要：零面の実初辺を、元の最初の辺の同じ初点 coslice の全座標へ戻す。
方針：元の比較三単体の退化した最後面を、初点を加えた実座標で読む。
規約：元の実辺・全係数を保持。使われ方：零面比較の実中間像の照合。
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
local notation "Z" => sliceUnder (SSet.yonedaEquiv.symm (coherentNerveVertex K))
local notation "α" => SimplexCategory.δ (2 : Fin 3) ≫ SimplexCategory.δ (0 : Fin 4)
/-- 零面の実初辺の全 coslice 座標は、元の最初の辺の初点退化そのもの。 -/
lemma spaceCompositionZeroFirstCoslice_coordinates :
    coherentCosliceSourceSimplex K ((Z).map (Opposite.op α) (spaceSimplexSourceCone T)) =
    coherentConeTailExtension (SpaceInfinity.δ 2 s) := by
  refine (coherentCosliceSourceSimplex_reindex K α (spaceSimplexSourceCone T)).symm.trans ?_
  change SpaceInfinity.map (SimplexCategory.mkHom (prependOrderHom (α).toOrderHom)).op
    (coherentCosliceSourceSimplex K (spaceSimplexSourceCone T)) = _
  have hc : coherentCosliceSourceSimplex K (spaceSimplexSourceCone T) =
      SpaceInfinity.map (SimplexCategory.σ 0).op T :=
    (spaceSimplexSourceCone_coordinates T).trans (coherentConeTailExtension_eq_sigmaZero T)
  refine (congrArg (fun t => SpaceInfinity.map
    (SimplexCategory.mkHom (prependOrderHom (α).toOrderHom)).op t) hc).trans ?_
  rw [← CategoryTheory.Functor.map_comp_apply, ← op_comp]
  have h : SimplexCategory.mkHom (prependOrderHom (α).toOrderHom) ≫ SimplexCategory.σ 0 =
      SimplexCategory.δ (3 : Fin 4) := by
    ext j
    fin_cases j <;> rfl
  rw [h]
  exact (coherentCompositionTetrahedron_face_three s).trans
    (coherentConeTailExtension_eq_sigmaZero (SpaceInfinity.δ 2 s)).symm
/-- 零面の実初辺の coslice 射は、元の最初の辺の同じ標準 source cone。 -/
lemma spaceCompositionZeroFirstCoslice_map :
    (stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (0 : Fin 4)) ≫
      SSet.yonedaEquiv.symm (spaceSimplexSourceCone T) =
        SSet.yonedaEquiv.symm (spaceSimplexSourceCone (SpaceInfinity.δ 2 s)) := by
  have hc : (Z).map (Opposite.op α) (spaceSimplexSourceCone T) =
      spaceSimplexSourceCone (SpaceInfinity.δ 2 s) := by
    apply spaceCosliceSourceSimplex_injective K 1
    exact (spaceCompositionZeroFirstCoslice_coordinates s).trans
      (spaceSimplexSourceCone_coordinates (SpaceInfinity.δ 2 s)).symm
  exact (congrArg (fun r => r ≫ SSet.yonedaEquiv.symm (spaceSimplexSourceCone T))
    (stdSimplex.map_comp (SimplexCategory.δ (2 : Fin 3))
      (SimplexCategory.δ (0 : Fin 4)))).symm.trans
    ((SSet.yonedaEquiv_symm_naturality_left α (spaceSimplexSourceCone T)).trans
      (congrArg SSet.yonedaEquiv.symm hc))

end SerrePositivity.InfinityCategories.F2
