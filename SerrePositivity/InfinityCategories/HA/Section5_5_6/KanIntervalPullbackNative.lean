module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreLimit
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalMap
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanDiagramCoherentNerve
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaces
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Vertices
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpecifiedLimitConeTransport
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.StrictCoherentNatTrans
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.KanIntervalCospan
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.KanIntervalPullbackTransport
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.KanConeLimits
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.SpacePullbacks
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictNerveMaps

/-!
概要：任意の Kan cospan の区間による path 引き戻しを、元の図式の native な極限錐にする。
方針：指定円柱で輸送した錐を標準の Kan 図式上に表示する。
規約：元の二射に fibration 性は要求しない。
使われ方：𝒮 の引き戻しと filtered 余極限の比較から fibration 仮定を外す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open _root_.CategoryTheory _root_.SSet
namespace SerrePositivity.InfinityCategories.HA.Section5_5_6

variable {X Y Z : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}}

/-- 概要：元の任意の cospan 上の区間による path 引き戻し錐。
方針：定値切断の指定円柱で戻した錐の表示を正規化する。
規約：輸送の全錐のホモトピーは intervalPullbackStrictConeTransport が保持する。 -/
def intervalPullbackCone (f : X ⟶ Y) (g : Z ⟶ Y) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.kanPullbackDiagram f g)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackStrictConeTransport f g).cone.cast (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram_eq_kanDiagram _)

/-- 概要：区間の引き戻し錐は元の任意の cospan の実際の ∞ 極限。
方針：指定円柱に沿う極限錐の輸送の普遍性を使う。
規約：両射の fibration 性は不要。使われ方：一般の二射の引き戻し模型。 -/
lemma intervalPullbackCone_isLimit (f : X ⟶ Y) (g : Z ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.HA.Section5_5_6.intervalPullbackCone f g) :=
  (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackStrictConeTransport f g).isLimit.cast _

/-- 概要：元の cospan の極限頂点は実際の二段の path 引き戻し。
方針：輸送の頂点の等式を置換後の元の頂点の式に合成する。
規約：台の模型との厳密な同定は intervalPullbackKanObject_obj。使われ方：filtered 比較。 -/
lemma intervalPullbackCone_vertex (f : X ⟶ Y) (g : Z ⟶ Y) :
    (_root_.SerrePositivity.InfinityCategories.HA.Section5_5_6.intervalPullbackCone f g).vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceInfinityVertex (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackKanObject f g) := by
  rw [_root_.SerrePositivity.InfinityCategories.HA.Section5_5_6.intervalPullbackCone, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone.vertex_cast,
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackStrictConeTransport f g).vertex_eq, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackReplacementCone_vertex]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityVertex_eq_coherent _).symm

end SerrePositivity.InfinityCategories.HA.Section5_5_6

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "5.5.6.17" (partial := stronger-hyp) "仮定：X=S の場合で添字 B は filtered、coherent な cospan の三つの族を B 上の left fibration で指定（Lean が強い：sifted より強い filtered 性とこの unstraightening 模型）。結論：fiberwise な path pullback の全空間の Kan 模型から、三全空間の Kan 模型の path pullback への標準比較が単体的ホモトピー同値となり、path pullback の錐は元の空間の ∞ 極限となる（filtered な空間値の場合の pullback と余極限の交換に一致する部分）。一般 sifted 添字と任意 ∞ トポスは含まれない。"] _root_.SerrePositivity.InfinityCategories.HA.Section5_5_6.intervalPullbackCone_isLimit
