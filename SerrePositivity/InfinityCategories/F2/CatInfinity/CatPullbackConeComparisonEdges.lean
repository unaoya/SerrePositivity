module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.CatPullbackConeHomotopy
public import SerrePositivity.InfinityCategories.F2.CatInfinity.ConeHomotopyEdges
public import SerrePositivity.InfinityCategories.F2.CatInfinity.HomotopyVerticalRestriction

/-!
概要：Cat_∞ の錐の比較の頂点辺と図式辺の具体的な同定。
方針：相対輸送の二つの制限を各零単体で評価する。
規約：頂点辺は恒等、図式辺は定値 path の切断の指定成分。
使われ方：各脚の自然性の正方形を通常の関手の式に送る。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

variable {A B C : SSet.{u}} [Quasicategory A] [Quasicategory B] [Quasicategory C]

/-- 概要：引き戻し錐の比較の頂点辺は候補対象の恒等辺の一次単体。
方針：頂点側の定値制限と頂点の厳密な一致を使う。
規約：Cat_∞ の元の一単体の等式。
使われ方：二脚の比較の正方形から頂点の自己同値を消す。 -/
lemma catPullbackConeHomotopy_apexEdge (p : A ⟶ C) (q : B ⟶ C) :
    (coneHomotopyApexEdge (catPullbackConeHomotopy p q)).edge =
      (coherentNerveEdge (𝟙 (catPullbackObject p q))).edge := by
  let J := (SSet.uliftFunctor.{u + 1, u}).obj (nerve (AsSmall.{u} WalkingCospan))
  have h := homotopyVertexEdge_constant (catPullbackConeHomotopy p q) (joinInl Δ[0] J)
    (joinInl Δ[0] J ≫ (catPullbackReplacementCone p q).val)
    (catPullbackConeHomotopy_apex p q) (SSet.yonedaEquiv (𝟙 Δ[0]))
  change (coneHomotopyApexEdge (catPullbackConeHomotopy p q)).edge =
    PinchedHom.constant (catPullbackReplacementCone p q).vertex 1 at h
  calc
    _ = PinchedHom.constant (catPullbackReplacementCone p q).vertex 1 := h
    _ = PinchedHom.constant (coherentVertex (catPullbackObject p q)) 1 := by
      rw [catPullbackReplacementCone_vertex]
    _ = _ := by rw [coherentNerveEdge_id, pinchedConstant_one]; rfl
/-- 概要：引き戻し錐の比較の図式辺は切断の指定自然変換の成分。
方針：図式側の制限と coherent 円柱の垂直辺の式を使う。
規約：全ての cospan の添字で同じ等式を返す。
使われ方：二脚の比較の正方形の右辺を実際の関手へ戻す。 -/
lemma catPullbackConeHomotopy_diagramEdge (p : A ⟶ C) (q : B ⟶ C)
    (i : AsSmall.{u} WalkingCospan) :
    (coneHomotopyDiagramEdge (catPullbackConeHomotopy p q)
      (ULift.up (ComposableArrows.mk₀ i))).edge =
        (coherentNerveEdge ((catPullbackReplacementNatTrans p q).app i)).edge := by
  let J := (SSet.uliftFunctor.{u + 1, u}).obj (nerve (AsSmall.{u} WalkingCospan))
  have h := homotopyVertexEdge_prism (catPullbackConeHomotopy p q) (joinInr Δ[0] J)
    (strictCoherentNatTransMap (catPullbackReplacementNatTrans p q))
    (catPullbackConeHomotopy_diagram p q) (ULift.up (ComposableArrows.mk₀ i))
  exact h.trans (strictCoherentNatTransMap_component (catPullbackReplacementNatTrans p q) i)

end SerrePositivity.InfinityCategories.F2
