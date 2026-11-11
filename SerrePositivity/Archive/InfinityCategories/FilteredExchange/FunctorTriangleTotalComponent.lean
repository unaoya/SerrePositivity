module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorTriangleRelativeComparison
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorTriangleSequentialPostComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.RelativeFunctorPrecomposition

/-!
概要：元の全空間の恒等初期値で、全族の三角形比較の元の値を回収する。
方針：指定成分の前合成表示から恒等前合成を除く。
規約：元の比較を選び直さない。使われ方：全族の二面比較と全空間作用の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 恒等写像での頂点同型の像は、元の同じ指定同型そのもの。 -/
lemma vertexIso_map_identity_heq {X : SSet.{u}} {x y : X _⦋0⦌} (e : VertexIso x y) :
    HEq (VertexIso.map e (𝟙 X)) e := by
  have h : (hoFunctor.map (𝟙 X)).toFunctor = 𝟭 (SSet.HomotopyCategory X) := by
    rw [CategoryTheory.Functor.map_id]
    rfl
  exact mapIso_heq_of_functor_eq h e

/-- 元の全空間と恒等初期値における指定成分は、元の相対三角形比較そのもの。 -/
lemma functorTriangleSequentialPostComparison_total_app_heq
    {B : SSet.{u + 1}} {F G J : B ⟶ SpaceInfinity.{u}}
    {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {c : SSet.Homotopy F J}
    (T : FunctorCompositionTriangle a b c) :
    HEq ((functorTriangleSequentialPostComparison T (leftUnstraighteningProjection F)).app
      (relativeFunctorVertex (leftUnstraighteningProjection F) (leftUnstraighteningProjection F)
        (𝟙 (leftUnstraightening F)) (Category.id_comp _)))
      (functorTriangleRelativeComparison T) := by
  have h := (functorTriangleSequentialPostComparison_app_heq_post T
    (leftUnstraighteningProjection F) _).trans
      (functorTrianglePostComparison_app_heq_pre T (leftUnstraighteningProjection F)
        (𝟙 (leftUnstraightening F)) (Category.id_comp _))
  exact h.trans ((vertexIso_map_heq (functorTriangleRelativeComparison T)
    (relativeFunctorPre_id _ _)).trans
      (vertexIso_map_identity_heq (functorTriangleRelativeComparison T)))

end SerrePositivity.InfinityCategories.F2
