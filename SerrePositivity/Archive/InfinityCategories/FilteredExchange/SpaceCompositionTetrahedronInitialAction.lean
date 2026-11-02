module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceCompositionTetrahedronInitialCoslice
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceSimplexPointedFamilyVertex
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceSimplexPointedFamilyInitial

/-!
概要：比較三単体の第二頂点の全係数作用は元の初点の標準 fiber 比較。
方針：coslice の実頂点の一致を全 Hom の前合成へ代入する。
規約：各点に分解せず同じ全反転 Hom を保持する。
使われ方：零面の全 pointed 族の始点固定条件。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits

/-- 第二頂点でも全係数に対する元の標準比較を厳密に回収する。 -/
lemma spaceCompositionTetrahedron_second_action (s : SpaceInfinity.{u} _⦋2⦌) :
    simplexPrismVertex 3 1 (spaceSimplexPointedCoefficients s) ≫
      spaceSimplexPointedFamily (coherentCompositionTetrahedron s) =
    pointedCoherentFiberComparison (s.obj ⟨ULift.up 0⟩) ≫
      vertexFiberι pointedSpaceProjection (coherentNerveVertex (s.obj ⟨ULift.up 0⟩)) := by
  have h := spaceSimplexPointedFamily_vertex (coherentCompositionTetrahedron s) 1
  rw [spaceCompositionTetrahedron_second_coslice_vertex s] at h
  exact h.trans ((spaceSimplexPointedFamily_vertex
    (coherentCompositionTetrahedron s) 0).symm.trans
      (spaceSimplexPointedFamily_initial (coherentCompositionTetrahedron s)))

end SerrePositivity.InfinityCategories.F2
