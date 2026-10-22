module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ArrowHomTriangleFaces

/-! 指定辺の元の区間図式の両端成分評価を、指定された始点・終点へ正規化する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
variable {X : SSet.{u}} {a b : X _⦋0⦌} (f : X.Edge a b)

lemma dgGluingArrowEdgeEvaluation_zero :
    (evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))).app (Opposite.op ⦋0⦌)
      (functorVertex (SSet.yonedaEquiv.symm f.edge)) = a := by
  rw [evaluateFunctorAt_functorVertex, SSet.yonedaEquiv_symm_app]
  have hv : stdSimplex.objEquiv.{u} (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      SimplexCategory.δ (1 : Fin 2) := by decide
  rw [hv]
  exact f.src_eq

lemma dgGluingArrowEdgeEvaluation_one :
    (evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))).app (Opposite.op ⦋0⦌)
      (functorVertex (SSet.yonedaEquiv.symm f.edge)) = b := by
  rw [evaluateFunctorAt_functorVertex, SSet.yonedaEquiv_symm_app]
  have hv : stdSimplex.objEquiv.{u} (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      SimplexCategory.δ (0 : Fin 2) := by decide
  rw [hv]
  exact f.tgt_eq

end SerrePositivity.InfinityCategories
