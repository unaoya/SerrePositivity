module

public import SerrePositivity.InfinityCategories.HomotopyLimits.PrismPointEdges
public import SerrePositivity.InfinityCategories.Core.SliceMap
public import SerrePositivity.InfinityCategories.Core.Cocone
public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialFiberEdgePiZero

/-!
概要：余錐を、その頂点から出る指定辺を保って全 join 図式へ延長する。
方針：余錐圏の射影の標準輸送辺を取り、全辺を uncurry する。
規約：元の余錐と指定辺の両方を全射の等式で保持する。
使われ方：交互列の各辺を、既に選んだ有限の全図式へ組み込む。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits

variable {K X : SSet.{u}} [Quasicategory X] {F : K ⟶ X}
  (c : JoinCocone F) {y : X _⦋0⦌} (e : X.Edge c.vertex y)

/-- 概要：元の余錐と指定した次の辺を含む全 join 図式。
方針：同じ標準輸送 prism の点で得られる余錐圏の辺を展開する。
規約：辺のホモトピー類から別の代表を選び直さない。
使われ方：指定辺を持つ有限図式の延長。 -/
def coconeSpecifiedEdgeExtension : join K (Δ[1] : SSet.{u}) ⟶ X :=
  sliceUnderUncurry (SSet.yonedaEquiv.symm (standardTransportPointEdge
    (sliceUnderProjection F) e (initialFiberVertexAt _ c c.vertex rfl)).edge)

/-- 概要：延長された join 図式は元の固定図式を保つ。
方針：uncurry の固定側の制限を使う。
規約：全射の厳密な等式。
使われ方：同じ余錐圏での構成の確認。 -/
lemma coconeSpecifiedEdgeExtension_inl :
    joinInl K Δ[1] ≫ coconeSpecifiedEdgeExtension c e = F :=
  sliceUnderUncurry_fixed _

/-- 概要：時刻零への制限は元の指定余錐全体。
方針：余錐圏の輸送辺の始点と uncurry の前合成則を使う。
規約：頂点と脚だけの照合で代用しない。
使われ方：可算列の既存の有限段階との厳密な整合。 -/
lemma coconeSpecifiedEdgeExtension_zero :
    joinMap (𝟙 K) (SSet.stdSimplex.δ (1 : Fin 2)) ≫
      coconeSpecifiedEdgeExtension c e = c.val := by
  let k := standardTransportPointEdge (sliceUnderProjection F) e
    (initialFiberVertexAt _ c c.vertex rfl)
  change joinMap (𝟙 K) (SSet.stdSimplex.δ (1 : Fin 2)) ≫
    sliceUnderUncurry (SSet.yonedaEquiv.symm k.edge) = c.val
  rw [← sliceUnderUncurry_precomp, k.δ_one_yonedaEquiv_symm]
  exact sliceUnderUncurry_yoneda 0 c

/-- 概要：延長された join の右辺は元の指定辺そのもの。
方針：標準輸送辺の射影の等式を Yoneda 表示で読む。
規約：辺のホモトピー類ではなく全単体射の等式。
使われ方：交互列の隣接辺の指定を保持する。 -/
lemma coconeSpecifiedEdgeExtension_inr :
    joinInr K Δ[1] ≫ coconeSpecifiedEdgeExtension c e =
      SSet.yonedaEquiv.symm e.edge := by
  have hk := standardTransportPointEdge_projection (sliceUnderProjection F) e
    (initialFiberVertexAt (sliceUnderProjection F) c c.vertex rfl)
  rw [coconeSpecifiedEdgeExtension, sliceUnderUncurry_projection]
  simpa only [SSet.Edge.map_edge, SSet.yonedaEquiv_symm_comp] using
    congrArg (fun s : X _⦋1⦌ ↦ SSet.yonedaEquiv.symm s) hk

end SerrePositivity.InfinityCategories.F2.Presentable
