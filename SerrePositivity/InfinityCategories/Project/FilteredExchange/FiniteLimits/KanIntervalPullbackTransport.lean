module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Quasicategory
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreLimit
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismContraction
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalMap
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanDiagramCoherentNerve
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Vertices
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpecifiedLimitConeTransport
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.StrictCoherentNatTrans
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.StrictCoherentNatTransComponent
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.IntervalDiagram
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.KanIntervalCospan
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.KanIntervalCospanIso
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.KanConeLimits
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.SpacePullbacks
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictCones
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictNerveMaps
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic

/-!
概要：任意の Kan cospan の path 引き戻し模型に、追跡可能な極限錐の輸送を与える。
方針：終点が fibration の置換 cospan の既存の極限錐を指定円柱に沿って戻す。
規約：頂点・全錐のホモトピー・境界の円柱を保持する。
使われ方：元の cospan 上の実際の homotopy pullback 錐。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

variable {X Y Z : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}}

/-- 概要：任意の二射の区間の path 引き戻しを Kan 対象として束ねる。
方針：置換 cospan の標準引き戻し対象を使う。
規約：台は実際の二段の path 引き戻し。使われ方：元の cospan の極限頂点。 -/
def intervalPullbackKanObject (f : X ⟶ Y) (g : Z ⟶ Y) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.kanPullbackCone (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementKanEndpoint f) g).pt

/-- 概要：束ねた対象の台は構成済みの区間の引き戻し模型。
方針：標準引き戻し錐の頂点の定義を使う。
規約：対象の厳密な等式。使われ方：filtered 比較の始域・終域の照合。 -/
lemma intervalPullbackKanObject_obj (f : X ⟶ Y) (g : Z ⟶ Y) :
    (intervalPullbackKanObject f g).obj =
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullback (show X.obj ⟶ Y.obj from f) (show Z.obj ⟶ Y.obj from g) := rfl

/-- 概要：置換した cospan の既存の native な極限錐を strict 図式上に戻す。
方針：図式の表示の等式だけを cast する。
規約：錐の join からの射と頂点は同じ。使われ方：指定円柱による輸送の始域。 -/
def intervalPullbackReplacementCone (f : X ⟶ Y) (g : Z ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.kanPullbackDiagram (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementKanEndpoint f) g)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spacePullbackCone (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementKanEndpoint f) g).cast
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram_eq_kanDiagram _).symm

/-- 概要：置換した cospan の錐は実際の極限錐。
方針：N の一脚 fibration の定理を図式の等式で戻す。
規約：元の f は任意。使われ方：元の cospan への普遍性の輸送。 -/
lemma intervalPullbackReplacementCone_isLimit (f : X ⟶ Y) (g : Z ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (intervalPullbackReplacementCone f g) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spacePullbackCone_isLimitCone (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementKanEndpoint f) g).cast _

/-- 概要：置換の極限錐は実際の path 引き戻し対象を頂点に持つ。
方針：cast と strict な錐の頂点の式を使う。
規約：coherentNerveVertex の表示。使われ方：輸送後の頂点の同定。 -/
lemma intervalPullbackReplacementCone_vertex (f : X ⟶ Y) (g : Z ⟶ Y) :
    (intervalPullbackReplacementCone f g).vertex =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (intervalPullbackKanObject f g) := by
  rw [intervalPullbackReplacementCone, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone.vertex_cast, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spacePullbackCone,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone.vertex_cast, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone_vertex]
  rfl

/-- 概要：元の cospan への錐の輸送を全ホモトピー・境界の証拠とともに構成する。
方針：指定された定値切断の coherent 円柱の全垂直辺の可逆性を使う。
規約：置換前の図式と頂点を固定する。使われ方：実際の引き戻し錐の公開。 -/
def intervalPullbackStrictConeTransport (f : X ⟶ Y) (g : Z ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpecifiedLimitConeTransport (p := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.kanPullbackDiagram f g))
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.strictCoherentNatTransMap (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalCospanSection f g))
      (intervalPullbackReplacementCone f g) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.specifiedLimitConeTransport _ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.strictCoherentNatTransMap_zero _) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.strictCoherentNatTransMap_one _)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.strictCoherentNatTransMap_vertical_isInvertible _
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalCospanSection_component_isInvertible f g)) _
    (intervalPullbackReplacementCone_isLimit f g)

end SerrePositivity.InfinityCategories.Project.FilteredExchange
