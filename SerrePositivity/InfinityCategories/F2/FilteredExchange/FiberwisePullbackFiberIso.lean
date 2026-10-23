module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FiberwisePullbackFiberComparison
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FiberwisePullbackFiberInverse
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FiberwisePullbackFiberExt

/-!
概要：fiber ごとの path 引き戻しの各値は、元の三つの値の path 引き戻しに厳密に同型。
方針：三座標を保つ比較と逆を、両側の三座標の一意性で照合する。
規約：元の全 path と二入力を保持し、充填性は仮定しない。
使われ方：一般 coherent filtered 引き戻し比較の元の値による検出。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：元の path 引き戻しの fiber は元の三値の path 引き戻しそのもの。
方針：元の全 path と二入力を保持する順逆射を三座標で検査する。
規約：同じ元の底の頂点、元の f・g の fiber 射。使われ方：一般 coherent な値の比較。 -/
def fiberwisePullbackFiberIso {E D H B : SSet.{u}}
    (p : H ⟶ B) (f : E ⟶ H) (g : D ⟶ H) (b : B _⦋0⦌) :
    vertexFiber (fiberwiseIntervalPullbackProjection p f g) b ≅
      intervalPullback (vertexFiberMap (f ≫ p) p f rfl b) (vertexFiberMap (g ≫ p) p g rfl b) where
  hom := fiberwisePullbackFiberComparison p f g b
  inv := fiberwisePullbackFiberInverse p f g b
  hom_inv_id := by
    apply fiberwisePullbackFiber_hom_ext p f g b
    · rw [Category.assoc, fiberwisePullbackFiberInverse_path,
        fiberwisePullbackFiberComparison_path, Category.id_comp]
    · rw [Category.assoc, fiberwisePullbackFiberInverse_left,
        fiberwisePullbackFiberComparison_left, Category.id_comp]
    · rw [Category.assoc, fiberwisePullbackFiberInverse_right,
        fiberwisePullbackFiberComparison_right, Category.id_comp]
  inv_hom_id := by
    apply intervalPullback_hom_ext (vertexFiberMap (f ≫ p) p f rfl b)
      (vertexFiberMap (g ≫ p) p g rfl b)
    · rw [Category.assoc, fiberwisePullbackFiberComparison_path,
        fiberwisePullbackFiberInverse_path, Category.id_comp]
    · rw [Category.assoc, fiberwisePullbackFiberComparison_left,
        fiberwisePullbackFiberInverse_left, Category.id_comp]
    · rw [Category.assoc, fiberwisePullbackFiberComparison_right,
        fiberwisePullbackFiberInverse_right, Category.id_comp]

end SerrePositivity.InfinityCategories.F2
