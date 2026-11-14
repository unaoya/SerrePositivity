module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Cocone
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.HomotopyCoconeRealization
public import SerrePositivity.InfinityCategories.HTT.Section3_3_4.CoherentTotalObject
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoconeComparison.CoherentTotalUnitRepresentation

/-!
概要：小さい全空間の Kan 模型を頂点とする一般 coherent 図式の native な余錐。
方針：実際の単位を表す変換を、図式と頂点を固定する join 余錐として実現する。
規約：余錐の存在と頂点の同定を証明する。余極限性は別途必要。
使われ方：一般 coherent filtered 図式の余極限模型の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open _root_.CategoryTheory _root_.SSet
namespace SerrePositivity.InfinityCategories.HTT.Section3_3_4
variable {B : SSet.{u}}

/-- 概要：全空間の単位を表す変換の、全比較データ付き native な余錐の実現。
方針：指定変換を両端固定の fat join 比較で移す。
規約：単位の比較は coherentTotalUnitRepresentation が保持。使われ方：普遍性の追跡。 -/
def coherentTotalCoconeRealization
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.HomotopyCoconeRealization (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTotalUnitHomotopy F) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.homotopyCoconeRealization (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTotalUnitHomotopy F)

/-- 概要：元の一般 coherent 図式上の、全空間 Kan 模型を頂点とする native な余錐。
方針：全比較データ付きの実現から余錐を取る。
規約：図式 F は厳密に同じ。使われ方：一般 filtered 余極限の候補。 -/
def coherentDiagramTotalCocone
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F :=
  (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentTotalCoconeRealization F).cocone

/-- 概要：構成した native な余錐の頂点は元の小さい全空間の Kan 模型。
方針：指定ホモトピーの実現の頂点の式を使う。
規約：頂点は厳密に一致する。使われ方：既存の有限射・境界の検出との接続。 -/
lemma coherentDiagramTotalCocone_vertex
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :
    (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalCocone F).vertex = _root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex F :=
  (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentTotalCoconeRealization F).vertex_eq

end SerrePositivity.InfinityCategories.HTT.Section3_3_4

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "3.3.4.6" (partial := special) "仮定：任意の小さい K と p:K→SpaceInfinity に対し分類束を smallLeftUnstraightening p、余極限を coherentDiagramTotalCocone p の頂点に固定（Lean が強い特殊形）。結論：元の全空間からこの余極限への標準単位が弱ホモトピー同値（一致）。任意に指定された分類束・余極限への比較はこの型には含まない。"] _root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalCocone_vertex
