module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.PartialColimitSpanHomTriangles
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.FiberPointHomPath
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePathVertexEdge

/-!
概要：左右の実際の輸送余錐間の指定経路に沿う、既存の全 Hom 族のホモトピー。
方針：元の経路自身の辺を取り、全始点の作用と両端の元の族の比較を適用する。
規約：元の経路・始点・終点を保持する。点の族には新たな余極限性を仮定しない。
使われ方：共通 path end における左右の Hom 係数の高次照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {A B C : SSet.{u + 1}} {p : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}}
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
  (i : A ⟶ B) (F : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (hi : i ≫ F = p) (dB : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F)
  (j : A ⟶ C) (G : C ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (hj : j ≫ G = p) (dC : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone G)
local notation "z" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitStrictSpanCocone c hc i F hi dB j G hj dC)
local notation "q" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p
local notation "P" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanTransportCoconePath c hc i F hi dB j G hj dC

/-- 左輸送余錐を、同じ native な span 頂点の fiber に置いた元の点。 -/
def partialColimitSpanLeftTransportFiberPoint : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace p z) _⦋0⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialFiberVertexAt q (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanLeftTransportCocone c hc i F hi dB j G hj dC) z
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanLeftTransportCocone_vertex c hc i F hi dB j G hj dC)

/-- 右輸送余錐も、同じ fiber の元の点として保持する。 -/
def partialColimitSpanRightTransportFiberPoint : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace p z) _⦋0⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialFiberVertexAt q (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRightTransportCocone c hc i F hi dB j G hj dC) z
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRightTransportCocone_vertex c hc i F hi dB j G hj dC)

/-- 元の指定経路の零端点の評価は、左の元の fiber 点。 -/
lemma partialColimitSpanTransportCoconePath_source :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace p z) 0).app _ (SSet.yonedaEquiv P) =
      partialColimitSpanLeftTransportFiberPoint c hc i F hi dB j G hj dC := by
  have h := congrArg SSet.yonedaEquiv
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanTransportCoconePath_zero c hc i F hi dB j G hj dC)
  rw [SSet.yonedaEquiv_comp] at h
  exact h.trans (SSet.yonedaEquiv.apply_symm_apply _)

/-- 元の指定経路の一端点の評価は、右の元の fiber 点。 -/
lemma partialColimitSpanTransportCoconePath_target :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace p z) 1).app _ (SSet.yonedaEquiv P) =
      partialColimitSpanRightTransportFiberPoint c hc i F hi dB j G hj dC := by
  have h := congrArg SSet.yonedaEquiv
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanTransportCoconePath_one c hc i F hi dB j G hj dC)
  rw [SSet.yonedaEquiv_comp] at h
  exact h.trans (SSet.yonedaEquiv.apply_symm_apply _)

/-- 両端の表示を揃えた、元の指定経路自身の実際の辺。 -/
def partialColimitSpanTransportCoconeEdge : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace p z).Edge
    (partialColimitSpanLeftTransportFiberPoint c hc i F hi dB j G hj dC)
    (partialColimitSpanRightTransportFiberPoint c hc i F hi dB j G hj dC) :=
  { edge := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathVertexEdge (SSet.yonedaEquiv P)).edge
    src_eq := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathVertexEdge (SSet.yonedaEquiv P)).src_eq.trans
      (partialColimitSpanTransportCoconePath_source c hc i F hi dB j G hj dC)
    tgt_eq := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathVertexEdge (SSet.yonedaEquiv P)).tgt_eq.trans
      (partialColimitSpanTransportCoconePath_target c hc i F hi dB j G hj dC) }

/-- 辺の一単体は元の経路自身の一単体であり、別の経路へ置き換えていない。 -/
lemma partialColimitSpanTransportCoconeEdge_projection :
    (partialColimitSpanTransportCoconeEdge c hc i F hi dB j G hj dC).edge =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge (SSet.yonedaEquiv P).val := rfl

variable (y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌)

/-- 同じ fiber 点による点 Hom の表示は、既存の左輸送余錐の全 Hom の族そのもの。 -/
lemma partialColimitSpanLeftTransportHomFamily_fiberPoint :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fiberPointHomFamily q z y
        (partialColimitSpanLeftTransportFiberPoint c hc i F hi dB j G hj dC) =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanLeftTransportHomFamily c hc i F hi dB j G hj dC y := rfl

/-- 右側も、既存の同じ全 Hom の族そのものを保持する。 -/
lemma partialColimitSpanRightTransportHomFamily_fiberPoint :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fiberPointHomFamily q z y
        (partialColimitSpanRightTransportFiberPoint c hc i F hi dB j G hj dC) =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRightTransportHomFamily c hc i F hi dB j G hj dC y := rfl

/-- 元の指定辺の作用を、既存の左右の族の表示へ厳密に移した同型。 -/
def partialColimitSpanTransportHomPathIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanLeftTransportHomFamily c hc i F hi dB j G hj dC y)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRightTransportHomFamily c hc i F hi dB j G hj dC y) :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorIsoTransport
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fiberPointHomPathIso q z y (partialColimitSpanTransportCoconeEdge c hc i F hi dB j G hj dC))
    (partialColimitSpanLeftTransportHomFamily_fiberPoint c hc i F hi dB j G hj dC y)
    (partialColimitSpanRightTransportHomFamily_fiberPoint c hc i F hi dB j G hj dC y)

/-- 同じ指定経路に沿う、既存の左右の全 Hom の族の実際のホモトピー。 -/
def partialColimitSpanTransportHomPathComparison : SSet.Homotopy
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanLeftTransportHomFamily c hc i F hi dB j G hj dC y)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRightTransportHomFamily c hc i F hi dB j G hj dC y) :=
  (partialColimitSpanTransportHomPathIso c hc i F hi dB j G hj dC y).simplicialHomotopy

/-- 公開した比較円柱の辺の類は、同じ指定辺の作用と元の両端比較の合成を保つ。 -/
lemma partialColimitSpanTransportHomPathComparison_hom :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (partialColimitSpanTransportHomPathComparison c hc i F hi dB j G hj dC y)) =
      (partialColimitSpanTransportHomPathIso c hc i F hi dB j G hj dC y).hom :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorIso_simplicialHomotopy_hom _

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
