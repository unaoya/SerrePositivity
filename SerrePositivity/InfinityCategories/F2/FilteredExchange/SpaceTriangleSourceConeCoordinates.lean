module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SpaceSimplexSourceCone

/-!
概要：元の三角形の初点 coslice の中間・終点を、同じ元の第一辺・長辺へ戻す。
方針：初点退化と頂点制限を合成する順序写像を、その二つの面写像に同定する。
規約：元の全三角形と二つの実辺を保持。使われ方：全係数の三頂点の値の計算。
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

/-- 初点 coslice の中間頂点の座標は、元の同じ三角形の第一辺。 -/
lemma spaceTriangleSourceCone_middle_coordinates :
    coherentCosliceSourceSimplex (s.obj ⟨ULift.up 0⟩)
      ((sliceUnder (SSet.yonedaEquiv.symm
        (coherentNerveVertex (s.obj ⟨ULift.up 0⟩)))).map
          (SimplexCategory.const ⦋0⦌ ⦋2⦌ 1).op (spaceSimplexSourceCone s)) =
        SpaceInfinity.δ 2 s := by
  let α := SimplexCategory.const ⦋0⦌ ⦋2⦌ 1
  refine (coherentCosliceSourceSimplex_reindex _ α (spaceSimplexSourceCone s)).symm.trans ?_
  change SpaceInfinity.map (SimplexCategory.mkHom
    (prependOrderHom α.toOrderHom)).op
      (coherentCosliceSourceSimplex _ (spaceSimplexSourceCone s)) = _
  rw [spaceSimplexSourceCone_coordinates, coherentConeTailExtension_eq_sigmaZero]
  change SpaceInfinity.map (SimplexCategory.mkHom (prependOrderHom α.toOrderHom)).op
    (SpaceInfinity.map (SimplexCategory.σ 0).op s) = _
  rw [← Functor.map_comp_apply, ← op_comp]
  have h : SimplexCategory.mkHom (prependOrderHom α.toOrderHom) ≫ SimplexCategory.σ 0 =
      SimplexCategory.δ (2 : Fin 3) := by
    ext j
    fin_cases j <;> rfl
  rw [h]
  rfl

/-- 初点 coslice の終頂点の座標は、元の同じ三角形の長辺。 -/
lemma spaceTriangleSourceCone_target_coordinates :
    coherentCosliceSourceSimplex (s.obj ⟨ULift.up 0⟩)
      ((sliceUnder (SSet.yonedaEquiv.symm
        (coherentNerveVertex (s.obj ⟨ULift.up 0⟩)))).map
          (SimplexCategory.const ⦋0⦌ ⦋2⦌ 2).op (spaceSimplexSourceCone s)) =
        SpaceInfinity.δ 1 s := by
  let α := SimplexCategory.const ⦋0⦌ ⦋2⦌ 2
  refine (coherentCosliceSourceSimplex_reindex _ α (spaceSimplexSourceCone s)).symm.trans ?_
  change SpaceInfinity.map (SimplexCategory.mkHom
    (prependOrderHom α.toOrderHom)).op
      (coherentCosliceSourceSimplex _ (spaceSimplexSourceCone s)) = _
  rw [spaceSimplexSourceCone_coordinates, coherentConeTailExtension_eq_sigmaZero]
  change SpaceInfinity.map (SimplexCategory.mkHom (prependOrderHom α.toOrderHom)).op
    (SpaceInfinity.map (SimplexCategory.σ 0).op s) = _
  rw [← Functor.map_comp_apply, ← op_comp]
  have h : SimplexCategory.mkHom (prependOrderHom α.toOrderHom) ≫ SimplexCategory.σ 0 =
      SimplexCategory.δ (1 : Fin 3) := by
    ext j
    fin_cases j <;> rfl
  rw [h]
  rfl

end SerrePositivity.InfinityCategories.F2
