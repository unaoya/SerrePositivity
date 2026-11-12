module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeApexConstantHom
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.NativeCoconeTopIso

/-!
概要：同じ coslice 比較の頂点同型と関手圏内の頂点同型を定値 Hom 像で照合する。
方針：同じ元の代表を右頂点へ射影し、全余錐の頂点評価の式を使う。
規約：頂点同型の順方向・逆方向とも元の比較と代表を保持する。
使われ方：実際の頂点脚の Space 内の共役を関手圏の共役へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
open SSet.Truncated.HomotopyCategory
variable {K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X} {q d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p}
  (i : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p) q d)

/-- 同じ元の coslice 比較を、元の余錐頂点間の同型として保持する。 -/
def nativeCoconeApexIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := X) q.vertex d.vertex :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map i (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p)

/-- 同じ頂点同型の順方向は、同じ coslice 代表の全余錐の右頂点評価の類。 -/
lemma nativeCoconeApexIso_homMk :
    (nativeCoconeApexIso i).hom = homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeWholeEdgeApex q d
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeCoconeFunctorEdge (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeCoconeIsoRepresentative i)).toTruncated).toTruncated := by
  change (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p)).toFunctor.map i.hom = _
  rw [← _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeCoconeIsoRepresentative_homMk i]
  change homMk ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeCoconeIsoRepresentative i).map
    ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p))) = _
  congr 1
  apply SSet.Truncated.Edge.ext
  exact (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeCoconeFunctorEdge_apex (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeCoconeIsoRepresentative i)).symm

/-- 元の頂点同型の順方向の定値像は、同じ元の関手圏内の頂点同型の順方向。 -/
lemma nativeCoconeApexIso_constant_hom :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap K (nativeCoconeApexIso i).hom = (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeCoconeIsoTopIso i).hom := by
  rw [nativeCoconeApexIso_homMk, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeWholeEdgeApex_constant_hom, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeCoconeIsoTopIso_hom]

/-- 元の頂点同型の逆方向の定値像も、同じ元の関手圏内の頂点同型の逆方向。 -/
lemma nativeCoconeApexIso_constant_inv :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap K (nativeCoconeApexIso i).inv = (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeCoconeIsoTopIso i).inv := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeCoconeIsoTopIso i).hom).1
  rw [← nativeCoconeApexIso_constant_hom, ← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap_comp,
    Iso.inv_hom_id, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap_id,
    nativeCoconeApexIso_constant_hom, Iso.inv_hom_id]

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
