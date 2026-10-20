module

public import SerrePositivity.InfinityCategories.F1.PointFunctorEvaluation

/-!
概要：一点評価の逆同型の零単体を元の点の Yoneda 射として計算する。
方針：内部 Hom の各成分で標準零単体の一意性を使う。
規約：Kan 性と quasicategory 性は不要。
使われ方：右 Hom への一点係数と実際の pointed 頂点の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 一点評価の逆の零単体は、同じ点の Yoneda 射を表す関手頂点。 -/
lemma pointFunctorEvaluationIso_inv_vertex (E : SSet.{u}) (z : E _⦋0⦌) :
    (pointFunctorEvaluationIso E).inv.app (Opposite.op ⦋0⦌) z =
      functorVertex (SSet.yonedaEquiv.symm z) := by
  apply (ConcreteCategory.bijective_of_isIso
    ((pointFunctorEvaluationIso E).hom.app (Opposite.op ⦋0⦌))).1
  have h := congrArg (fun f => f.app (Opposite.op ⦋0⦌) z)
    (pointFunctorEvaluationIso E).inv_hom_id
  change (pointFunctorEvaluationIso E).hom.app (Opposite.op ⦋0⦌)
    ((pointFunctorEvaluationIso E).inv.app (Opposite.op ⦋0⦌) z) = z at h
  rw [h]
  change z = (evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0)).app _
    (functorVertex (SSet.yonedaEquiv.symm z))
  rw [evaluateFunctorAt_functorVertex]
  have hp : stdSimplex.obj₀Equiv.symm (0 : Fin 1) =
      SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) := by
    apply stdSimplex.ext
    intro i
    exact @Subsingleton.elim (Fin 1) inferInstance _ _
  rw [hp, SSet.yonedaEquiv_symm_app_id]

end SerrePositivity.InfinityCategories
