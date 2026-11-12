module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IntervalBoundary
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.VertexFiberMap
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwiseIntervalProjection
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwiseIntervalPullback
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwisePullbackFiberIso
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwisePullbackPathPrism
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwisePullbackValue
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.IntervalBoundaryExt
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.IntervalBoundaryPostcomposition
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.IntervalDiagram
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativePathBoundary
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativePathInputTransportData
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativePathTransportTarget

/-!
概要：輸送先の全相対境界図式を、元の同じ頂点の標的値へ厳密に制限する。
方針：部分 path と二端点で底が定値であることを照合し、元の fiber に持ち上げる。
規約：元の輸送先の境界図式を変更しない。
使われ方：標的有限模型の相対 fiber 輸送の指定境界。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange
variable {K M E D H B : SSet.{u}} {p : H ⟶ B} {f : E ⟶ H} {g : D ⟶ H}
  {A : K.Subcomplex} {u : K ⟶ E} {v : K ⟶ D}
  {a : (A : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullback p f g}
  {m : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryShape A ⟶ M} {q : M ⟶ H}
  (d : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativePathInputTransportData p f g A u v a m q)

/-- 概要：輸送先の全相対境界の底は元の共通頂点に定値。
方針：部分 path と区間境界の二端点で照合する。
規約：全境界の厳密な式。使われ方：元の標的 fiber への境界の制限。 -/
lemma relativePathTransportTarget_projection :
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathTransportTarget d ≫ p = SSet.const d.vertex := by
  have hπ : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackValueToTotal p f g d.vertex ≫
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackProjection p f g = SSet.const d.vertex := by
    change ((_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackFiberIso p f g d.vertex).inv ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackProjection p f g) d.vertex) ≫ _ = _
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const]
  have hl : ((d.leftValue ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (f ≫ p) d.vertex) ≫ f) ≫ p =
      SSet.const d.vertex := by
    rw [Category.assoc, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const]
  have hr : ((d.rightValue ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (g ≫ p) d.vertex) ≫ g) ≫ p =
      SSet.const d.vertex := by
    rw [Category.assoc, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const]
  apply (Subcomplex.unionProd.isPushout (boundary 1) A).hom_ext
  · change _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundarySide A ≫ (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathTransportTarget d ≫ p) =
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundarySide A ≫ SSet.const d.vertex
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathTransportTarget_side, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackPathPrism_projection,
      Category.assoc, hπ, SSet.comp_const, SSet.comp_const, SSet.comp_const]
  · change _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryEnds A ≫ (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathTransportTarget d ≫ p) =
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryEnds A ≫ SSet.const d.vertex
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathTransportTarget_ends, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalBoundaryDiagram_postcomp,
      hl, hr, SSet.comp_const]
    apply _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalBoundary_hom_ext
    · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_zero, SSet.comp_const]
    · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_one, SSet.comp_const]

/-- 概要：輸送先の相対境界を元の標的値に制限する射。
方針：厳密な定値の底射で fiber に入れる。
規約：元の境界図式を保持。使われ方：有限模型の終点 fiber の指定境界。 -/
def relativePathTransportTargetFiber : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryShape A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p d.vertex :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift p d.vertex (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathTransportTarget d)
    (relativePathTransportTarget_projection d)

/-- 概要：元の標的値から含めると輸送先の全境界図式に厳密に戻る。
方針：fiber の持ち上げの式。規約：全相対境界。使われ方：相対輸送の終点照合。 -/
lemma relativePathTransportTargetFiber_ι :
    relativePathTransportTargetFiber d ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p d.vertex = _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathTransportTarget d :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι _ _ _ _

end SerrePositivity.InfinityCategories.Project.FilteredExchange
