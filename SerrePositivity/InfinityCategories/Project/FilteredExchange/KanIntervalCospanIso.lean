module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Quasicategory
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Edges
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanInvertible
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Vertices
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakWhitehead
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.StrictCoherentNatTransComponent
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.IntervalReplacementSection
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanIntervalCospan
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.SpacePullbacks
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictNerveMaps

/-!
概要：元と path 置換後の Kan cospan の coherent な図式は同型。
方針：比較の全成分の弱同値性を Whitehead 判定と coherent 円柱へ渡す。
規約：成分ごとに逆を選んだ自然変換は仮定しない。
使われ方：元の cospan の極限錐を path 模型と同じ頂点で構成する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

variable {X Y Z : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}}

/-- 概要：cospan の定値 path の比較は全ての成分で弱ホモトピー同値。
方針：第一入力では切断の弱同値性、他では恒等射の弱同値性を使う。
規約：元の f と g は任意。使われ方：図式全体の同型の構成。 -/
lemma intervalCospanSection_isWeakHomotopyEquivalence (f : X ⟶ Y) (g : Z ⟶ Y)
    (i : AsSmall.{u} WalkingCospan) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence ((_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalCospanSection f g).app i) := by
  rcases i with ⟨_ | ⟨_ | _⟩⟩
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (𝟙 Y.obj)
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_id Y.obj).isWeakHomotopyEquivalence
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementSection (show X.obj ⟶ Y.obj from f))
    exact _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementSection_isWeakHomotopyEquivalence f
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (𝟙 Z.obj)
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_id Z.obj).isWeakHomotopyEquivalence

/-- 概要：cospan の比較の各成分の coherent な辺は可逆。
方針：Kan 複体の弱同値性を Whitehead 判定で移す。
規約：指定された成分の辺。使われ方：指定 prism の垂直辺の判定。 -/
lemma intervalCospanSection_component_isInvertible (f : X ⟶ Y) (g : Z ⟶ Y)
    (i : AsSmall.{u} WalkingCospan) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge ((_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalCospanSection f g).app i)) := by
  have h := intervalCospanSection_isWeakHomotopyEquivalence f g i
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentKanEdge_isInvertible_of_isQCatEquivalence
    (f := (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalCospanSection f g).app i) h.isSimplicialHomotopyEquivalence.isQCatEquivalence

/-- 概要：任意の Kan cospan と path 置換後の cospan の coherent 表示は関手同型。
方針：全成分が可逆な通常の自然変換の標準 coherent 円柱を使う。
規約：指定された図式そのものの同型。使われ方：極限の普遍性の輸送。 -/
def kanIntervalCospanDiagramIso (f : X ⟶ Y) (g : Z ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.kanPullbackDiagram f g))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.kanPullbackDiagram (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementKanEndpoint f) g)) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.strictCoherentNatTransIso (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalCospanSection f g)
  exact intervalCospanSection_component_isInvertible f g

end SerrePositivity.InfinityCategories.Project.FilteredExchange
