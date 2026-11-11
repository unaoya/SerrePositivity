module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.NativeConeComparisonTriangles
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorHomotopy

/-!
概要：元の同じ slice 内の錐の同型を、元の同型の射を表す可逆辺で表示する。
方針：ホモトピー圏への全射から一つの代表を取り、同じ代表を全頂点・脚に使う。
規約：元の同型の順方向の射を保持する。
使われ方：P_Σ 評価錐と元の有限積錐の比較を、全脚の実際の合成三角形へ写す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
variable {K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X} {c d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p}
  (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) c d)

/-- 元の slice 内の同じ錐同型の順方向の射を表す、一つの固定した比較辺。 -/
def nativeConeIsoRepresentative :
    SSet.Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p)) c d :=
  Classical.choose (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) c d e.hom)

/-- 選んだ同じ比較辺の類は、元の slice 内の同型の順方向の射そのもの。 -/
lemma nativeConeIsoRepresentative_homMk :
    SSet.Truncated.HomotopyCategory.homMk (nativeConeIsoRepresentative e) = e.hom :=
  Classical.choose_spec (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) c d e.hom)

/-- 選んだ同じ比較辺は、元の同型を表すので可逆。 -/
lemma nativeConeIsoRepresentative_isInvertible :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) (nativeConeIsoRepresentative e) := by
  change IsIso (SSet.Truncated.HomotopyCategory.homMk (nativeConeIsoRepresentative e))
  rw [nativeConeIsoRepresentative_homMk]
  infer_instance

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
