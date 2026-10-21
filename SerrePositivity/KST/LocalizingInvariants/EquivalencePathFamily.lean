module

public import SerrePositivity.KST.LocalizingInvariants.ArrowFamilyHomotopy
public import SerrePositivity.InfinityCategories.Core.EquivalencePathIso

/-!
概要：可逆 path の全族から、その同じ始点・終点の関手同型を得る。
方針：元の uncurry 円柱の各垂直辺が可逆であることを全部分複体の条件から読む。
規約：全族と両端を保持する。使われ方：正方形の境界変形を内部へ延長した後の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable {A X : SSet.{u}} [Quasicategory X] (a : A ⟶ equivalencePath X)

def equivalencePathFamilyIso :
    FunctorIso (a ≫ equivalencePathEndpoint X 0) (a ≫ equivalencePathEndpoint X 1) := by
  let H := uncurry (a ≫ equivalencePathι X)
  have hi (x : A _⦋0⦌) : IsInvertibleEdge (edgeOfSimplex
      (H.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant x 1))) := by
    have hv := fullSubcomplexOnVertices_vertex (a.app (Opposite.op ⦋0⦌) x)
    change IsEquivalencePathVertex ((a ≫ equivalencePathι X).app _ x) at hv
    rw [← curry_uncurry (a ≫ equivalencePathι X)] at hv
    unfold IsEquivalencePathVertex at hv
    rw [intervalFunctorVertexEdge_curry] at hv
    exact hv
  have e := functorIsoOfEquivalenceHomotopy H hi
  have he (i : Fin 2) : prismEndpoint i A ≫ H = a ≫ equivalencePathEndpoint X i := by
    rw [← curry_evaluateFunctorAt_interval, curry_uncurry]
    rfl
  rw [he 0, he 1] at e
  exact e

end SerrePositivity.KST.LocalizingInvariants
