module
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NormalizedIntervalBoundary
public import SerrePositivity.EInfinity.BarrattEccles.Normalized
/-!
概要：指定された線形化Δ[1]の零・一次成分を評価する。
方針：自由生成元で定義して、一次と二次の境界を確認する。
規約：正規化鎖の包含を前合成するA06の構成の分割。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory AlgebraicTopology
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A]
local notation "L" => Functor.obj (SerrePositivity.EInfinity.BarrattEccles.linearization A)
  (SSet.stdSimplex.obj (SimplexCategory.mk 1))
/-- 指定区間の零鎖での評価。 -/
def intervalVertexEvaluation (M : ModuleCat.{u} A) (x y : M) : (L).obj (Opposite.op ⦋0⦌) ⟶ M :=
  ModuleCat.freeDesc (↾fun a => intervalVertexValue x y
    ((SSet.stdSimplex.objEquiv a.down).toOrderHom 0))
/-- 指定区間の一鎖での評価。 -/
def intervalEdgeEvaluation (M : ModuleCat.{u} A) (w : M) : (L).obj (Opposite.op ⦋1⦌) ⟶ M :=
  ModuleCat.freeDesc (↾fun a => intervalEdgeValue w
    ((SSet.stdSimplex.objEquiv a.down).toOrderHom 0)
    ((SSet.stdSimplex.objEquiv a.down).toOrderHom 1))
/-- 一次での鎖写像条件。 -/
theorem interval_evaluation_boundary {M N : ModuleCat.{u} A}
    (d : M ⟶ N) (x y : N) (w : M) (hw : d w = y - x) :
    intervalEdgeEvaluation A M w ≫ d =
      (L).map (SimplexCategory.δ (0 : Fin 2)).op ≫ intervalVertexEvaluation A N x y -
      (L).map (SimplexCategory.δ (1 : Fin 2)).op ≫ intervalVertexEvaluation A N x y := by
  apply ModuleCat.free_hom_ext
  intro a
  simp only [ModuleCat.hom_sub, ModuleCat.hom_add, ModuleCat.hom_zero,
    LinearMap.sub_apply, LinearMap.add_apply, LinearMap.zero_apply, ModuleCat.comp_apply]
  dsimp only [intervalVertexEvaluation, intervalEdgeEvaluation,
    SerrePositivity.EInfinity.BarrattEccles.linearization, Functor.whiskeringRight,
    Functor.comp_map]
  repeat' erw [ModuleCat.free_map_apply]
  repeat' erw [ModuleCat.freeDesc_apply]
  let f := (SSet.stdSimplex.objEquiv a.down).toOrderHom
  change d (intervalEdgeValue w (f 0) (f 1)) =
    intervalVertexValue x y (f 1) - intervalVertexValue x y (f 0)
  exact interval_edge_boundary d.hom.toAddMonoidHom x y w hw (f 0) (f 1)
    (f.monotone (by decide))
/-- 二次境界の像は零。 -/
theorem interval_evaluation_triangle (M : ModuleCat.{u} A) (w : M) :
    (L).map (SimplexCategory.δ (0 : Fin 3)).op ≫ intervalEdgeEvaluation A M w -
      (L).map (SimplexCategory.δ (1 : Fin 3)).op ≫ intervalEdgeEvaluation A M w +
      (L).map (SimplexCategory.δ (2 : Fin 3)).op ≫ intervalEdgeEvaluation A M w = 0 := by
  apply ModuleCat.free_hom_ext
  intro a
  simp only [ModuleCat.hom_sub, ModuleCat.hom_add, ModuleCat.hom_zero,
    LinearMap.sub_apply, LinearMap.add_apply, LinearMap.zero_apply, ModuleCat.comp_apply]
  dsimp only [intervalVertexEvaluation, intervalEdgeEvaluation,
    SerrePositivity.EInfinity.BarrattEccles.linearization, Functor.whiskeringRight,
    Functor.comp_map]
  repeat' erw [ModuleCat.free_map_apply]
  repeat' erw [ModuleCat.freeDesc_apply]
  let f := (SSet.stdSimplex.objEquiv a.down).toOrderHom
  change intervalEdgeValue w (f 1) (f 2) - intervalEdgeValue w (f 0) (f 2) +
    intervalEdgeValue w (f 0) (f 1) = 0
  exact interval_triangle_boundary w f
end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
