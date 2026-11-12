module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreLimit
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.SimplicialHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.HomotopyEdgeNaturality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.NativeConeLeg

/-!
概要：錐全体の比較ホモトピーの頂点・図式の辺と各脚の自然性。
方針：join の二因子で制限し、標準の脚に自然性を適用する。
規約：標的の quasicategory 性は不要。
使われ方：Cat_∞ の引き戻し錐の二脚の読み戻し。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-- 概要：錐全体の比較ホモトピーを頂点での辺にする。
方針：join の左因子の零単体でホモトピーを評価する。
規約：元と比較先の錐の頂点を両端に明示する。
使われ方：二脚の比較で頂点の恒等性を計算する。 -/
def coneHomotopyApexEdge {K X : SSet.{u}} {p q : K ⟶ X}
    {c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p} {d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone q} (G : SSet.Homotopy c.val d.val) :
    SSet.Truncated.Edge (X := (truncation 2).obj X) c.vertex d.vertex where
  edge := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge G
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[0] K).app (Opposite.op ⦋0⦌) (SSet.yonedaEquiv (𝟙 Δ[0])))).edge
  src_eq := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge G _).src_eq
  tgt_eq := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge G _).tgt_eq
/-- 概要：錐全体の比較ホモトピーを図式の指定頂点での辺にする。
方針：join の右包含で評価し、錐の固定条件で両端を合わせる。
規約：元と比較先の図式の指定値を両端にする。
使われ方：切断の自然変換の指定成分との比較。 -/
def coneHomotopyDiagramEdge {K X : SSet.{u}} {p q : K ⟶ X}
    {c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p} {d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone q} (G : SSet.Homotopy c.val d.val) (k : K _⦋0⦌) :
    SSet.Truncated.Edge (X := (truncation 2).obj X)
      (p.app (Opposite.op ⦋0⦌) k) (q.app (Opposite.op ⦋0⦌) k) where
  edge := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge G ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] K).app (Opposite.op ⦋0⦌) k)).edge
  src_eq := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge G _).src_eq.trans
    (ConcreteCategory.congr_hom (NatTrans.congr_app c.property (Opposite.op ⦋0⦌)) k)
  tgt_eq := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge G _).tgt_eq.trans
    (ConcreteCategory.congr_hom (NatTrans.congr_app d.property (Opposite.op ⦋0⦌)) k)
/-- 概要：錐の各脚と頂点・図式の比較辺はホモトピー圏で可換。
方針：join 内の標準の脚にホモトピーの自然性を適用する。
規約：各脚の端点を元の図式の値として厳密に扱う。
使われ方：Cat_∞ の錐の二射影を実際の関手として同定する。 -/
lemma coneHomotopy_leg_naturality {K X : SSet.{u}} {p q : K ⟶ X}
    {c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p} {d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone q} (G : SSet.Homotopy c.val d.val) (k : K _⦋0⦌) :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg c k) ≫
        SSet.Truncated.HomotopyCategory.homMk (coneHomotopyDiagramEdge G k) =
      SSet.Truncated.HomotopyCategory.homMk (coneHomotopyApexEdge G) ≫
        SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg d k) := by
  rcases c with ⟨c, hc⟩
  rcases d with ⟨d, hd⟩
  subst p
  subst q
  exact _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.homotopy_edge_naturality G (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneDomainLeg k)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
