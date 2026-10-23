module

public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorFamilyTranspose
public import SerrePositivity.InfinityCategories.Core.EquivalencePath

/-!
概要：区間族の頂点は、転置族の同じ評価辺によって一意に定まる。
方針：関手頂点・Yoneda の同値と定値パラメーターの自然性を使う。
規約：元の区間族と元の一単体を保持する。
使われ方：全局所比較の path 頂点を既存の結合 path と同定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 区間からの関手の頂点は、表す一単体で一意に定まる。 -/
lemma intervalFunctorVertexEdge_injective (Y : SSet.{u}) :
    Function.Injective (intervalFunctorVertexEdge (Y := Y)) := by
  intro v w h
  exact (functorVertexEquiv Δ[1] Y).symm.injective (SSet.yonedaEquiv.injective h)

/-- 区間族の頂点が表す辺は、同じ転置族の評価辺。 -/
lemma intervalFamily_vertex_edge {U Y : SSet.{u}}
    (F : U ⟶ (ihom (Δ[1] : SSet.{u})).obj Y) (x : U _⦋0⦌) :
    intervalFunctorVertexEdge (F.app (Opposite.op ⦋0⦌) x) =
      (((SSet.Edge.ofTruncated homotopyIntervalEdge).map
        (transposeFunctorFamily F)).map (evaluateFunctorAt x)).edge := by
  rw [transposeFunctorFamily_edgeAt, pinchedConstant_map]
  change intervalFunctorVertexEdge (F.app (Opposite.op ⦋0⦌) x) =
    ((PinchedHom.constant (F.app (Opposite.op ⦋0⦌) x) 1).app (Opposite.op ⦋1⦌)
      (𝟙 (Opposite.op ⦋1⦌))) homotopyIntervalEdge.edge
  have hi : SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) = homotopyIntervalEdge.edge := by
    apply stdSimplex.ext
    intro j
    fin_cases j <;> rfl
  rw [← hi]
  rfl

end SerrePositivity.InfinityCategories
