module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeJoinFunctorBoundary

/-!
概要：各 fiber で普遍な相対 join 図式は通常の関手の制限に対して相対始点境界を充填する。
方針：境界の最初の頂点を指定された図式と同定し、正次元の境界延長を適用する。
規約：充填は通常の内部 Hom の制限に関するもの。
使われ方：点ごとの Kan 条件から大域的な関手の普遍性へ進む接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：全 fiber で余極限となる図式は、通常の関手の制限の相対始点境界を充填する。
方針：指定始点の等式を関手頂点の全単射で図式の等式へ戻し、境界延長の最初の頂点条件を満たす。
規約：元の p は cocartesian fibration、底と値域は quasicategory。
使われ方：普遍な相対 join 図式から元の図式への制限の大域的な普遍性。 -/
lemma kanRelativeJoinFunctor_initialBoundary_of_colimit_fibers {K C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (p : K ⟶ C) [CocartesianFibration p]
    (H : relativeJoin p (𝟙 C) ⟶ D)
    (hcol : ∀ c : C _⦋0⦌, IsColimitCone (kanRelativeJoinFiberCocone p c H)) :
    InitialBoundaryLifting ((pre (relativeJoinInl p (𝟙 C))).app D) (functorVertex H) := by
  intro n a d hfirst sq
  apply exists_kanRelativeJoin_functor_boundary_extension p n a d sq.w
  have hv := congrArg SSet.yonedaEquiv hfirst
  simp only [boundaryVertex, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] at hv
  have hH : (functorVertexEquiv (relativeJoin p (𝟙 C)) D).symm
      (a.app (Opposite.op ⦋0⦌)
        ⟨stdSimplex.obj₀Equiv.symm (0 : Fin (n + 2)), vertex_mem_boundary n 0⟩) = H := by
    rw [hv]
    exact (functorVertexEquiv _ D).symm_apply_apply H
  intro c
  rw [hH]
  exact hcol c

end SerrePositivity.InfinityCategories.F1B
