module

public import SerrePositivity.InfinityCategories.HomotopyLimits.PointHomTransportAction
public import SerrePositivity.InfinityCategories.Core.KanHomotopyEquivalence

/-!
概要：始点 fiber の指定辺に沿う、全 Hom の輸送作用の実際のホモトピー。
方針：全始点の作用を関手空間へ curry し、指定辺の像を同じ円柱へ展開する。
規約：新しい経路やホモトピーの代表は選ばない。元の辺と作用への射影式を保持する。
使われ方：同じ頂点上の左右の輸送余錐間の指定経路に沿う全 Hom の変化。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p] (a b : B _⦋0⦌)
  {v w : (vertexFiber p a) _⦋0⦌} (k : (vertexFiber p a).Edge v w)

/-- 指定された始点の辺を、同じ全 Hom の作用で写した実際の関手辺。 -/
def pointHomTransportEdge : ((ihom (pinchedHomLeft a b)).obj (vertexFiber p b)).Edge
    (functorVertex (pointHomTransportActionAt p a b v))
    (functorVertex (pointHomTransportActionAt p a b w)) where
  edge := (k.map (pointHomTransportMap p a b)).edge
  src_eq := (k.map (pointHomTransportMap p a b)).src_eq.trans (pointHomTransportMap_vertex p a b v)
  tgt_eq := (k.map (pointHomTransportMap p a b)).tgt_eq.trans (pointHomTransportMap_vertex p a b w)

/-- 指定した同じ始点辺を動かす、全 Hom パラメータでの実際のホモトピー。 -/
def pointHomTransportPathHomotopy : SSet.Homotopy
    (pointHomTransportActionAt p a b v) (pointHomTransportActionAt p a b w) :=
  simplicialHomotopyOfFunctorEdge (pointHomTransportEdge p a b k).toTruncated

/-- 円柱の射は、元の始点辺と同じ全 Hom の作用を組み合わせたものそのもの。 -/
lemma pointHomTransportPathHomotopy_projection :
    (pointHomTransportPathHomotopy p a b k).h =
      lift (snd (pinchedHomLeft a b) (Δ[1] : SSet.{u}) ≫ SSet.yonedaEquiv.symm k.edge)
        (fst (pinchedHomLeft a b) (Δ[1] : SSet.{u})) ≫ pointHomTransportAction p a b := by
  change uncurry (SSet.yonedaEquiv.symm
    ((pointHomTransportMap p a b).app (Opposite.op ⦋1⦌) k.edge)) = _
  rw [← SSet.yonedaEquiv_symm_comp, pointHomTransportMap,
    uncurry_natural_left, uncurry_curry]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨s, t⟩
  rfl

end
end SerrePositivity.InfinityCategories.HomotopyLimits
