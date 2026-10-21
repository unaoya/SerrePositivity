module

public import SerrePositivity.InfinityCategories.F1.EquivalenceTriangleEvaluation
public import SerrePositivity.InfinityCategories.F1.PreFiberKan

/-!
概要：元の可逆三角形の各面の端点評価は元の頂点評価そのもの。
方針：面の包含の公式と、同じ前合成の頂点評価を使う。
規約：面や頂点の表示を選び直さない。
使われ方：三角形の各面の同値性を同じ評価へ帰着する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 元の同じ三角形の面を端点で評価すると、元の対応する頂点を回収する。 -/
lemma equivalenceTriangleFace_endpoint (Y : SSet.{u}) (i : Fin 3) (j : Fin 2) :
    equivalenceTriangleFace Y i ≫ equivalencePathEndpoint Y j =
      equivalenceTriangleEvaluation Y (i.succAbove j) := by
  change equivalenceTriangleFace Y i ≫ equivalencePathι Y ≫
    evaluateFunctorAt (stdSimplex.obj₀Equiv.symm j) = _
  rw [← Category.assoc, equivalenceTriangleFace_ι, Category.assoc, evaluateFunctorAt_pre]
  unfold equivalenceTriangleEvaluation
  congr 2

end SerrePositivity.InfinityCategories
