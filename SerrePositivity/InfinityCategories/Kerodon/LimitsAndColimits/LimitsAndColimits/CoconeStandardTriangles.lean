module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeStandardUnitSquare
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.IntervalVertexHomotopy

/-!
概要：標準余錐の単位正方形を、元の合成三角形の長辺の区間同型へ移す。
方針：同じ共役された頂点射の代表を一つ取り、両三角形の類の等式を使う。
規約：入力された合成三角形と両長辺の全一単体を保持する。
使われ方：元の全変換三角形と全余錐作用の比較。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SSet.Truncated.HomotopyCategory
variable {K X : SSet.{u}} [Quasicategory X] {p r : K ⟶ X}
  {q q' : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p} {d d' : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone r}
  (i : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p) q q') (j : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder r) d d')
  (e : SSet.Truncated.Edge
    (X := (truncation 2).obj ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[0] : SSet.{u}))).obj X))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex q.val) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex d.val))

/-- 同じ標準頂点間の共役された射を表す、一つの元の辺。 -/
def coconeStandardApexEdge :
    SSet.Truncated.Edge (X := (truncation 2).obj ((ihom K).obj X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const q'.vertex)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const d'.vertex)) :=
  Classical.choose (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeStandardApexHom i j e))

/-- 同じ選択済み頂点辺の類は、元の両端比較で共役した同じ射。 -/
lemma coconeStandardApexEdge_homMk :
    homMk (coconeStandardApexEdge i j e) = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeStandardApexHom i j e :=
  Classical.choose_spec (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeStandardApexHom i j e))

/-- 同じ標準単位の正方形の両合成を表す元の三角形の長辺は、区間内で同型。 -/
def coconeStandardUnitCompositeIso
    (l m : SSet.Edge (X := (ihom K).obj X) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const d'.vertex)))
    (L : SSet.Truncated.Edge.CompStruct (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeWholeEdgeBottom q d e).toTruncated
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeTransformationVertex d')).toTruncated l.toTruncated)
    (M : SSet.Truncated.Edge.CompStruct
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeTransformationVertex q')).toTruncated
      (coconeStandardApexEdge i j e) m.toTruncated) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge l) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge m) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.intervalVertexIsoOfHomMkEq
  calc
    homMk l.toTruncated = _ := (homMk_comp_homMk L).symm
    _ = _ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeStandardUnit_square i j e
    _ = homMk m.toTruncated := by
      rw [← coconeStandardApexEdge_homMk i j e]
      exact homMk_comp_homMk M

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
