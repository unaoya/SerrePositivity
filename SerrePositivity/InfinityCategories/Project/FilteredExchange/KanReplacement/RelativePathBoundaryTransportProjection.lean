module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IntervalBoundary
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PushoutHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.VertexFiberMap
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.FiberwiseIntervalProjection
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwiseIntervalPullback
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwisePullbackPathPrism
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwisePullbackPathPrismHomotopy
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwisePullbackValue
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.IntervalDiagram
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.RelativePathBoundary
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.RelativePathBoundaryCylinderCompatibility
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.RelativePathBoundaryTransportHomotopy
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.RelativePathInputTransportData
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.RelativePathTransportTarget

/-!
概要：貼り合わせた全相対境界円柱の両側の制限と、元の模型の底円柱との一致。
方針：押し出しホモトピーの制限式と、元の二つの底射の式を使う。
規約：全円柱を厳密に保持する。
使われ方：標的有限模型の相対 fiber 輸送の底条件。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange
variable {K M E D H B : SSet.{u}} {p : H ⟶ B} {f : E ⟶ H} {g : D ⟶ H}
  {A : K.Subcomplex} {u : K ⟶ E} {v : K ⟶ D}
  {a : (A : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullback p f g}
  {m : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryShape A ⟶ M} {q : M ⟶ H}
  (d : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativePathInputTransportData p f g A u v a m q)
  (hk : (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundarySide A ≫ m) ≫ q = _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackPathPrism p f g a)
  (he : (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryEnds A ≫ m) ≫ q = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram (u ≫ f) (v ≫ g))

/-- 概要：貼り合わせの部分 path 円柱は元の境界引き戻し射の全 path 正方形。
方針：押し出しホモトピーの第一脚。規約：全正方形。使われ方：指定境界の厳密な保持。 -/
lemma relativePathBoundaryTransportHomotopy_side :
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundarySide A ▷ (Δ[1] : SSet.{u})) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryTransportHomotopy d hk he).h =
        (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackPathPrismHomotopy p f g d.boundaryHomotopy).h :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pushoutHomotopy_inl (Subcomplex.unionProd.isPushout (boundary 1) A)
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundarySideHomotopy d hk) (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryEndsHomotopy d he)
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryCylinder_compatible d)

/-- 概要：貼り合わせの両端円柱は元の二入力の全境界円柱。
方針：押し出しホモトピーの第二脚。規約：全時間。使われ方：二入力の厳密な保持。 -/
lemma relativePathBoundaryTransportHomotopy_ends :
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryEnds A ▷ (Δ[1] : SSet.{u})) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryTransportHomotopy d hk he).h = (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathEndsHomotopy d).h :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pushoutHomotopy_inr (Subcomplex.unionProd.isPushout (boundary 1) A)
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundarySideHomotopy d hk) (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryEndsHomotopy d he)
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryCylinder_compatible d)

/-- 概要：全相対境界の輸送円柱の底は、元の有限模型の指定底円柱に厳密に一致。
方針：時間との直積後の押し出しの両脚で底射の式を使う。
規約：全時刻。使われ方：模型本体の境界固定 fiber 輸送。 -/
lemma relativePathBoundaryTransportHomotopy_projection :
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryTransportHomotopy d hk he).h ≫ p =
      (m ▷ (Δ[1] : SSet.{u})) ≫ d.modelBase.h := by
  apply ((Subcomplex.unionProd.isPushout (boundary 1) A).map
    (tensorRight (Δ[1] : SSet.{u}))).hom_ext
  · change (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundarySide A ▷ (Δ[1] : SSet.{u})) ≫
      ((_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryTransportHomotopy d hk he).h ≫ p) =
        (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundarySide A ▷ (Δ[1] : SSet.{u})) ≫
          ((m ▷ (Δ[1] : SSet.{u})) ≫ d.modelBase.h)
    rw [← Category.assoc, relativePathBoundaryTransportHomotopy_side,
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackPathPrismHomotopy_projection, ← comp_whiskerRight_assoc]
    exact d.path_projection.symm
  · change (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryEnds A ▷ (Δ[1] : SSet.{u})) ≫
      ((_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryTransportHomotopy d hk he).h ≫ p) =
        (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryEnds A ▷ (Δ[1] : SSet.{u})) ≫
          ((m ▷ (Δ[1] : SSet.{u})) ≫ d.modelBase.h)
    rw [← Category.assoc, relativePathBoundaryTransportHomotopy_ends,
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathEndsHomotopy_projection, ← comp_whiskerRight_assoc]

end SerrePositivity.InfinityCategories.Project.FilteredExchange
