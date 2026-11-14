module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.SectionsUnitRepresentation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.HomotopyConeRealization
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：一般 coherent 空間値図式上に、小さい全切断を頂点とする native な全錐を構成する。
方針：全切断の恒等射を表す変換を両端固定で join の錐へ実現する。
規約：元の図式・頂点・指定変換との比較を保持する。極限性は別工程。
使われ方：F1-4 の小さい極限の具体的な候補錐。

対応節は Kerodon 7.4（Tag 02SX）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
variable {B : SSet.{u}}
  (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})

/-- 元の全切断の恒等射を表す変換を、全比較データ付きの錐へ実現する。 -/
def coherentSectionsConeRealization :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.HomotopyConeRealization (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentSectionsIdentityHomotopy F) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.homotopyConeRealization (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentSectionsIdentityHomotopy F)

/-- 元の小さい全切断を頂点とする、同じ一般 coherent 図式上の native な全錐。 -/
@[kerodon 02VD]
def coherentDiagramSectionsCone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone F := (coherentSectionsConeRealization F).cone

/-- 同じ元の全錐の頂点は、元の宇宙の小さい全切断対象そのもの。 -/
lemma coherentDiagramSectionsCone_vertex :
    (coherentDiagramSectionsCone F).vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentSpaceSectionsVertex F :=
  (coherentSectionsConeRealization F).vertex_eq

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "3.3.3.4" (partial := special) "仮定：任意の小さい K と p:K→SpaceInfinity に対し分類束 X を標準の smallLeftUnstraightening p に固定（Lean が強い特殊形）。結論：全切断の Kan 複体そのものを頂点とする錐が極限であり、原典のこの標準分類束の場合の式と一致。任意の分類束への全切断の輸送比較はこの型には含まない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentDiagramSectionsCone_vertex
