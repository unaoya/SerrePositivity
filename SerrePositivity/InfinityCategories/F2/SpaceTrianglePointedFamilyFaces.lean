module

public import SerrePositivity.InfinityCategories.F2.SpaceSimplexPointedFamilyRestriction
public import SerrePositivity.InfinityCategories.F2.RelativeVertexIsoOfEq

/-!
概要：同じ全 pointed 三角形比較の三面を、元の三辺を底とする相対同型へ戻す。
方針：三辺の底の厳密な式で相対頂点の表示だけを揃える。
規約：第零面と全係数を含めて、元の全比較の指定値を保持する。
使われ方：三つの辺比較と指定 path の同時照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 三角形の任意の全持ち上げの面は、元の同じ三角形の面を全係数で被覆する。 -/
lemma spaceTrianglePointedFace_projection {A : SSet.{u + 1}}
    (s : SpaceInfinity.{u} _⦋2⦌) (L : (Δ[2] : SSet.{u + 1}) ⊗ A ⟶ PointedSpaceInfinity.{u})
    (hL : L ≫ pointedSpaceProjection = fst Δ[2] A ≫ SSet.yonedaEquiv.symm s) (j : Fin 3) :
    ((stdSimplex.δ j ▷ A) ≫ L) ≫ pointedSpaceProjection =
      fst Δ[1] A ≫ SSet.yonedaEquiv.symm (SpaceInfinity.δ j s) := by
  rw [Category.assoc, hL, ← Category.assoc, whiskerRight_fst,
    Category.assoc, stdSimplex.δ_comp_yonedaEquiv_symm]

/-- 面の底の式は、持ち上げの選択に依存しない元の全図式の厳密な等式。 -/
lemma spaceTrianglePointedFace_base (s : SpaceInfinity.{u} _⦋2⦌)
    (A : SSet.{u + 1}) (j : Fin 3) :
    (stdSimplex.δ j ▷ A) ≫ (fst Δ[2] A ≫ SSet.yonedaEquiv.symm s) =
      fst Δ[1] A ≫ SSet.yonedaEquiv.symm (SpaceInfinity.δ j s) := by
  rw [← Category.assoc, whiskerRight_fst, Category.assoc,
    stdSimplex.δ_comp_yonedaEquiv_symm]

end SerrePositivity.InfinityCategories.F2
