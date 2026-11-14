module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.CoherentTransportComparisonSpace
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalMappingSpace

/-!
概要：底と始点を固定する同じ輸送 prism の比較辺の類は、選択によらない。
方針：実際の比較辺を可縮な延長空間に置き、同じ終点への Hom の一意性を終点評価へ移す。
規約：任意の fiber 内の辺には主張しない。固定した同じ延長空間の辺だけを比較する。
使われ方：全 Hom の境界から作った比較を、指定済みの合成比較の辺と照合する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
private lemma edgeMap_homMk_eq {X Y : SSet.{u}} (r : X ⟶ Y)
    {x y : X _⦋0⦌} (k l : X.Edge x y)
    (h : SSet.Truncated.HomotopyCategory.homMk k.toTruncated =
      SSet.Truncated.HomotopyCategory.homMk l.toTruncated) :
    SSet.Truncated.HomotopyCategory.homMk (k.map r).toTruncated =
      SSet.Truncated.HomotopyCategory.homMk (l.map r).toTruncated := by
  exact congrArg (fun z : (SSet.HomotopyCategory.mk x : X.HomotopyCategory) ⟶
    SSet.HomotopyCategory.mk y ↦ (SSet.mapHomotopyCategory r).map z) h

variable {E B : SSet.{u}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
  {a c : B _⦋0⦌} (g : B.Edge a c)
  {x y : (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportPrismExtensionSpace p g) _⦋0⦌}
  (k l : (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportPrismExtensionSpace p g).Edge x y)

/-- 同じ底・初期値の延長空間内で、同じ二頂点を結ぶ比較辺の類は一意。 -/
lemma transportPrismExtensionEdge_homMk_eq :
    SSet.Truncated.HomotopyCategory.homMk k.toTruncated =
      SSet.Truncated.HomotopyCategory.homMk l.toTruncated := by
  have hc := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportPrismExtensionSpace_isContractibleKan p g
  let := hc.kanComplex
  exact (hc.isTerminalVertex y).isTerminalHo.hom_ext _ _

/-- 終点での像も、同じ二頂点を結ぶ元の比較辺の選択によらない。 -/
lemma transportPrismExtensionEdge_endpoint_homMk_eq :
    SSet.Truncated.HomotopyCategory.homMk
        ((k.map (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportPrismExtensionEndpoint p g)).toTruncated) =
      SSet.Truncated.HomotopyCategory.homMk
        ((l.map (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportPrismExtensionEndpoint p g)).toTruncated) := by
  exact edgeMap_homMk_eq (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportPrismExtensionEndpoint p g) k l
    (transportPrismExtensionEdge_homMk_eq p g k l)

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
