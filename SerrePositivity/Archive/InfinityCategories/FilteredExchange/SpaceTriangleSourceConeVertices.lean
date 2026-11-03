module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceTriangleSourceConeCoordinates
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceCosliceEdgeComponent

/-!
概要：元の三角形の初点 coslice の中間・終頂点を、元の Hom 比較の零成分に同定する。
方針：join 座標の単射性と、同じ実辺の厳密な回収を組み合わせる。
規約：元の射と初点を保持。使われ方：全 pointed 族の三頂点の元の作用の計算。
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

/-- 元の初点 coslice の中間頂点は、同じ第一辺の元の Hom 比較の零成分。 -/
lemma spaceTriangleSourceCone_middle_vertex :
    (SSet.yonedaEquiv.symm (spaceSimplexSourceCone s)).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 3)) =
        coherentCosliceEdgeComponent (coherentEdgeHom (SpaceInfinity.δ 2 s)) := by
  apply spaceCosliceSourceSimplex_injective (s.obj ⟨ULift.up 0⟩) 0
  exact (spaceTriangleSourceCone_middle_coordinates s).trans
    (coherentCosliceEdgeComponent_space_coordinates (SpaceInfinity.δ 2 s)).symm

/-- 元の初点 coslice の終頂点は、同じ長辺の元の Hom 比較の零成分。 -/
lemma spaceTriangleSourceCone_target_vertex :
    (SSet.yonedaEquiv.symm (spaceSimplexSourceCone s)).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (2 : Fin 3)) =
        coherentCosliceEdgeComponent (coherentEdgeHom (SpaceInfinity.δ 1 s)) := by
  apply spaceCosliceSourceSimplex_injective (s.obj ⟨ULift.up 0⟩) 0
  exact (spaceTriangleSourceCone_target_coordinates s).trans
    (coherentCosliceEdgeComponent_space_coordinates (SpaceInfinity.δ 1 s)).symm

end SerrePositivity.InfinityCategories.F2
