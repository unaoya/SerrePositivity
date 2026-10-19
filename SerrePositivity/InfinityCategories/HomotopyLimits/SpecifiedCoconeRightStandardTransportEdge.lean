module

public import SerrePositivity.InfinityCategories.HomotopyLimits.PrismPointEdges
public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeRestrictionEdges

/-!
概要：指定右修正三角形の初辺を、標準輸送 prism 自身の辺として保持する。
方針：同じ標準 prism を、元の右余錐の fiber 頂点で評価する。
規約：裸の存在命題から辺を選び直さない。元の prism と底の右脚を同時に保つ。
使われ方：右修正辺と合成する前の標準輸送辺の厳密な照合。
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
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) (p : D ⟶ SpaceInfinity.{u})
  (c : JoinCocone (f ≫ (i ≫ p))) (hc : IsColimitCone c)
  (dB : JoinCocone (i ≫ p)) (dC : JoinCocone (j ≫ p))
local notation "qC" => sliceUnderProjection (j ≫ p)
local notation "eC" => partialColimitSpanRightLeg c hc f (i ≫ p) rfl dB
  g (j ≫ p) (coconePushoutBoundary_eq hp p) dC
local notation "vC" => initialFiberVertexAt qC dC (JoinCocone.vertex dC) rfl

/-- 右修正を加える前の辺は、同じ標準 prism の点の辺そのもの。 -/
def specifiedCoconeRightStandardTransportEdge : (sliceUnder (j ≫ p)).Edge dC
    (transportedCoconeVertex dC eC).val := standardTransportPointEdge qC eC vC

/-- 第一辺の一単体は、標準 prism 自身から取った同じ一単体。 -/
lemma specifiedCoconeRightStandardTransportEdge_raw :
    (specifiedCoconeRightStandardTransportEdge hp p c hc dB dC).edge =
      (standardTransportPointEdge qC eC vC).edge := rfl

/-- 第一辺の全単体表示は、同じ標準 prism を元の fiber 頂点で評価したもの。 -/
lemma specifiedCoconeRightStandardTransportEdge_diagram :
    SSet.yonedaEquiv.symm (specifiedCoconeRightStandardTransportEdge hp p c hc dB dC).edge =
      prismVertexEvaluation (transportEdgePrism qC eC) vC :=
  standardTransportPointEdge_diagram qC eC vC

/-- 標準の右辺は、元の native span の右脚を一単体のまま被覆する。 -/
lemma specifiedCoconeRightStandardTransportEdge_projection :
    (qC).app (Opposite.op ⦋1⦌)
        (specifiedCoconeRightStandardTransportEdge hp p c hc dB dC).edge = (eC).edge :=
  standardTransportPointEdge_projection qC eC vC

end
end SerrePositivity.InfinityCategories.HomotopyLimits
