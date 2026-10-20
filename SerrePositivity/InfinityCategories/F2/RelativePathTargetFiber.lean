module

public import SerrePositivity.InfinityCategories.F2.RelativePathTransportTarget
public import SerrePositivity.InfinityCategories.F2.IntervalBoundaryExt

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
namespace SerrePositivity.InfinityCategories.F2
variable {K M E D H B : SSet.{u}} {p : H ⟶ B} {f : E ⟶ H} {g : D ⟶ H}
  {A : K.Subcomplex} {u : K ⟶ E} {v : K ⟶ D}
  {a : (A : SSet.{u}) ⟶ fiberwiseIntervalPullback p f g}
  {m : relativePathBoundaryShape A ⟶ M} {q : M ⟶ H}
  (d : RelativePathInputTransportData p f g A u v a m q)

/-- 概要：輸送先の全相対境界の底は元の共通頂点に定値。
方針：部分 path と区間境界の二端点で照合する。
規約：全境界の厳密な式。使われ方：元の標的 fiber への境界の制限。 -/
lemma relativePathTransportTarget_projection :
    relativePathTransportTarget d ≫ p = SSet.const d.vertex := by
  have hπ : fiberwisePullbackValueToTotal p f g d.vertex ≫
      fiberwiseIntervalPullbackProjection p f g = SSet.const d.vertex := by
    change ((fiberwisePullbackFiberIso p f g d.vertex).inv ≫
      vertexFiberι (fiberwiseIntervalPullbackProjection p f g) d.vertex) ≫ _ = _
    rw [Category.assoc, vertexFiberι_comp, SSet.comp_const]
  have hl : ((d.leftValue ≫ vertexFiberι (f ≫ p) d.vertex) ≫ f) ≫ p =
      SSet.const d.vertex := by
    rw [Category.assoc, Category.assoc, vertexFiberι_comp, SSet.comp_const]
  have hr : ((d.rightValue ≫ vertexFiberι (g ≫ p) d.vertex) ≫ g) ≫ p =
      SSet.const d.vertex := by
    rw [Category.assoc, Category.assoc, vertexFiberι_comp, SSet.comp_const]
  apply (Subcomplex.unionProd.isPushout (boundary 1) A).hom_ext
  · change relativePathBoundarySide A ≫ (relativePathTransportTarget d ≫ p) =
      relativePathBoundarySide A ≫ SSet.const d.vertex
    rw [← Category.assoc, relativePathTransportTarget_side, fiberwisePullbackPathPrism_projection,
      Category.assoc, hπ, SSet.comp_const, SSet.comp_const, SSet.comp_const]
  · change relativePathBoundaryEnds A ≫ (relativePathTransportTarget d ≫ p) =
      relativePathBoundaryEnds A ≫ SSet.const d.vertex
    rw [← Category.assoc, relativePathTransportTarget_ends, intervalBoundaryDiagram_postcomp,
      hl, hr, SSet.comp_const]
    apply intervalBoundary_hom_ext
    · rw [intervalBoundaryDiagram_zero, SSet.comp_const]
    · rw [intervalBoundaryDiagram_one, SSet.comp_const]

/-- 概要：輸送先の相対境界を元の標的値に制限する射。
方針：厳密な定値の底射で fiber に入れる。
規約：元の境界図式を保持。使われ方：有限模型の終点 fiber の指定境界。 -/
def relativePathTransportTargetFiber : relativePathBoundaryShape A ⟶ vertexFiber p d.vertex :=
  vertexFiberLift p d.vertex (relativePathTransportTarget d)
    (relativePathTransportTarget_projection d)

/-- 概要：元の標的値から含めると輸送先の全境界図式に厳密に戻る。
方針：fiber の持ち上げの式。規約：全相対境界。使われ方：相対輸送の終点照合。 -/
lemma relativePathTransportTargetFiber_ι :
    relativePathTransportTargetFiber d ≫ vertexFiberι p d.vertex = relativePathTransportTarget d :=
  vertexFiberLift_ι _ _ _ _

end SerrePositivity.InfinityCategories.F2
