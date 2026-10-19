module

public import SerrePositivity.InfinityCategories.HomotopyLimits.PrismPointEdges
public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeRestrictionEdges

/-!
概要：指定した元の余錐の左制限へ、標準輸送 prism 自身から比較辺を取り出す。
方針：左制限の厳密な輸送像の式で、同じ標準 prism の点の辺の終点を表示し直す。
規約：裸の辺の存在命題から選ばない。元の prism と底の左脚を同時に保つ。
使われ方：元の native な左三角形に付加比較辺と左輸送辺を持ち上げる。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ SpaceInfinity.{u})
  (c : JoinCocone (f ≫ (i ≫ p))) (hc : IsColimitCone c)
  (dB : JoinCocone (i ≫ p)) (dC : JoinCocone (j ≫ p))
local notation "qB" => sliceUnderProjection (i ≫ p)
local notation "eB" => partialColimitSpanLeftLeg c hc f (i ≫ p) rfl dB
  g (j ≫ p) (coconePushoutBoundary_eq hp p) dC
local notation "vB" => initialFiberVertexAt qB dB (JoinCocone.vertex dB) rfl

/-- 左の標準 prism 自身の辺を、指定した元の余錐の左制限を終点として保持する。 -/
def specifiedCoconeLeftTransportEdge : (sliceUnder (i ≫ p)).Edge dB
    ((partialColimitSpecifiedPathCocone hp p c hc dB dC).restrict i) := by
  let k := standardTransportPointEdge qB eB vB
  exact
    ⟨k.edge, k.src_eq, k.tgt_eq.trans
      ((congrArg Subtype.val (partialColimitSpecifiedFiberVertex_left hp p c hc dB dC)).symm.trans
        (coconeRestrictionFiber_vertex_val i _
          (partialColimitSpecifiedFiberVertex hp p c hc dB dC)))⟩

set_option maxHeartbeats 800000 in
-- 指定余錐の左制限と標準輸送像の大きい頂点表示を一単体の型で照合する。
/-- 終点の表示を変えても、一単体は元の標準輸送の点の辺そのもの。 -/
lemma specifiedCoconeLeftTransportEdge_raw :
    (specifiedCoconeLeftTransportEdge hp p c hc dB dC).edge =
      (standardTransportPointEdge qB eB vB).edge := rfl

/-- この辺の全単体表示は、元の標準輸送 prism の同じ点での評価そのもの。 -/
lemma specifiedCoconeLeftTransportEdge_diagram :
    SSet.yonedaEquiv.symm (specifiedCoconeLeftTransportEdge hp p c hc dB dC).edge =
      prismVertexEvaluation (transportEdgePrism qB eB) vB :=
  (congrArg SSet.yonedaEquiv.symm
    (specifiedCoconeLeftTransportEdge_raw hp p c hc dB dC)).trans
      (standardTransportPointEdge_diagram qB eB vB)

/-- 左の実際の比較辺は、元の span の左脚を一単体のまま厳密に被覆する。 -/
lemma specifiedCoconeLeftTransportEdge_projection :
    (qB).app (Opposite.op ⦋1⦌) (specifiedCoconeLeftTransportEdge hp p c hc dB dC).edge =
      (eB).edge :=
  (congrArg (fun z ↦ (qB).app (Opposite.op ⦋1⦌) z)
    (specifiedCoconeLeftTransportEdge_raw hp p c hc dB dC)).trans
      (standardTransportPointEdge_projection qB eB vB)

end
end SerrePositivity.InfinityCategories.HomotopyLimits
