module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativePathTargetFiber

/-!
概要：輸送先の相対境界の元の標的値内の三座標を厳密に照合する。
方針：元の fiber の単射な包含後で、境界の二端点と全 path の式を使う。
規約：元の境界の値と二入力の値を変更しない。
使われ方：輸送した有限模型の指定境界を元の値で読む。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {K M E D H B : SSet.{u}} {p : H ⟶ B} {f : E ⟶ H} {g : D ⟶ H}
  {A : K.Subcomplex} {u : K ⟶ E} {v : K ⟶ D}
  {a : (A : SSet.{u}) ⟶ fiberwiseIntervalPullback p f g}
  {m : relativePathBoundaryShape A ⟶ M} {q : M ⟶ H}
  (d : RelativePathInputTransportData p f g A u v a m q)

/-- 概要：輸送先の相対境界の始点は元の第一値の像。
方針：標的 fiber の包含後に区間境界の始点を評価する。
規約：元の fiber 射。使われ方：有限模型の始点の厳密な照合。 -/
lemma relativePathTransportTargetFiber_zero :
    relativePathBoundaryEndpoint A 0 ≫ relativePathTransportTargetFiber d =
      d.leftValue ≫ vertexFiberMap (f ≫ p) p f rfl d.vertex := by
  apply vertexFiber_hom_ext p d.vertex
  rw [Category.assoc, relativePathTransportTargetFiber_ι, relativePathBoundaryEndpoint,
    Category.assoc, relativePathTransportTarget_ends, intervalBoundaryDiagram_zero]
  simp only [Category.assoc, vertexFiberMap_ι]

/-- 概要：輸送先の相対境界の終点は元の第二値の像。
方針：標的 fiber の包含後に区間境界の終点を評価する。
規約：元の fiber 射。使われ方：有限模型の終点の厳密な照合。 -/
lemma relativePathTransportTargetFiber_one :
    relativePathBoundaryEndpoint A 1 ≫ relativePathTransportTargetFiber d =
      d.rightValue ≫ vertexFiberMap (g ≫ p) p g rfl d.vertex := by
  apply vertexFiber_hom_ext p d.vertex
  rw [Category.assoc, relativePathTransportTargetFiber_ι, relativePathBoundaryEndpoint,
    Category.assoc, relativePathTransportTarget_ends, intervalBoundaryDiagram_one]
  simp only [Category.assoc, vertexFiberMap_ι]

/-- 概要：輸送先の相対境界の全部分 path は、元の境界値の元の全 path そのもの。
方針：単射な包含後に元の値の全 path の比較式を uncurry する。
規約：高次単体も保持。使われ方：元の値での指定境界の厳密な反映。 -/
lemma relativePathTransportTargetFiber_side :
    relativePathBoundarySide A ≫ relativePathTransportTargetFiber d =
      uncurry (d.boundaryValue ≫ intervalPullbackPath
        (vertexFiberMap (f ≫ p) p f rfl d.vertex)
        (vertexFiberMap (g ≫ p) p g rfl d.vertex)) := by
  apply vertexFiber_hom_ext p d.vertex
  rw [Category.assoc, relativePathTransportTargetFiber_ι, relativePathTransportTarget_side]
  have h := congrArg (fun r ↦ uncurry (d.boundaryValue ≫ r))
    (fiberwisePullbackValueToTotal_path p f g d.vertex)
  rw [← Category.assoc d.boundaryValue _
    ((ihom (Δ[1] : SSet.{u})).map (vertexFiberι p d.vertex)), uncurry_natural_right] at h
  simpa only [fiberwisePullbackPathPrism, Category.assoc] using h

end SerrePositivity.InfinityCategories.F2
