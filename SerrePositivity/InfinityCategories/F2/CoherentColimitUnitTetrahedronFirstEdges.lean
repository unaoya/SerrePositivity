module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitUnitTetrahedronSides

/-!
概要：中央と最後の単位三単体の第一辺が、元の第一変換そのものであることを回収する。
方針：元の第三面とその第二面を厳密に制限する。
規約：全辺を保持。使われ方：第零面の可変初期値を既存の指定第一辺比較へ接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {l : SSet.Homotopy F G} {r : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle l r d)

/-- 中央の元の三単体の第一辺は、元の指定第一変換そのもの。 -/
lemma coherentColimitUnitTetrahedron_middle_firstEdge :
    (stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4)) ≫
      SSet.yonedaEquiv.symm (coherentColimitUnitTriangleTetrahedron B T 1) = curry l.h := by
  have hs : stdSimplex.δ (3 : Fin 4) ≫
      SSet.yonedaEquiv.symm (coherentColimitUnitTriangleTetrahedron B T 1) =
        (coherentColimitUnitUpperTriangle B l).diagram := by
    apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
    exact coherentColimitUnitTetrahedron_lower_first B T
  rw [Category.assoc, hs, (coherentColimitUnitUpperTriangle B l).face_two]

/-- 最後の元の三単体の第一辺も、元の指定第一変換そのもの。 -/
lemma coherentColimitUnitTetrahedron_last_firstEdge :
    (stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4)) ≫
      SSet.yonedaEquiv.symm (coherentColimitUnitTriangleTetrahedron B T 2) = curry l.h := by
  have hs : stdSimplex.δ (3 : Fin 4) ≫
      SSet.yonedaEquiv.symm (coherentColimitUnitTriangleTetrahedron B T 2) = T.diagram := by
    apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
    exact coherentColimitUnitTriangleTetrahedron_last B T
  rw [Category.assoc, hs, T.face_two]

end SerrePositivity.InfinityCategories.F2
