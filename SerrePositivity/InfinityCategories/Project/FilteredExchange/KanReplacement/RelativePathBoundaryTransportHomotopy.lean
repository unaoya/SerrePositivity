module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IntervalBoundary
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PushoutHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.VertexFiberMap
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwiseIntervalPullback
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwisePullbackPathPrism
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwisePullbackPathPrismHomotopy
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwisePullbackValue
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.IntervalDiagram
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.RelativePathBoundary
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.RelativePathBoundaryCylinderCompatibility
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.RelativePathInputTransportData
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.RelativePathTransportTarget

/-!
概要：元の境界 path 正方形と二入力の全円柱を、全相対境界のホモトピーへ貼る。
方針：共通部分での厳密な一致を使い、元の積の和の押し出し上で貼り合わせる。
規約：全円柱を選び直さず、両側の制限を保持する。
使われ方：標的有限模型の全相対境界を保つ相対輸送。
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

/-- 概要：元の境界 path の正方形を模型の境界表示の端点へ合わせる。
方針：端点の等式だけを照合し、元の全正方形を保持する。
規約：h を変更しない。使われ方：押し出しの部分 path 側の指定円柱。 -/
def relativePathBoundarySideHomotopy
    (hk : (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundarySide A ≫ m) ≫ q = _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackPathPrism p f g a) :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundarySide A ≫ (m ≫ q))
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundarySide A ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathTransportTarget d) where
  h := (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackPathPrismHomotopy p f g d.boundaryHomotopy).h
  h₀ := by
    change SSet.ι₀ ≫ (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackPathPrismHomotopy p f g d.boundaryHomotopy).h =
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundarySide A ≫ (m ≫ q)
    rw [SSet.Homotopy.h₀, ← Category.assoc, hk]
  h₁ := by
    change SSet.ι₁ ≫ (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackPathPrismHomotopy p f g d.boundaryHomotopy).h =
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundarySide A ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathTransportTarget d
    rw [SSet.Homotopy.h₁, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathTransportTarget_side]
  rel := (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackPathPrismHomotopy p f g d.boundaryHomotopy).rel

/-- 概要：二入力の全境界円柱を模型の両端表示へ合わせる。
方針：元の二つの全円柱を保ち、両端の等式を照合する。
規約：h を変更しない。使われ方：押し出しの二端点側の指定円柱。 -/
def relativePathBoundaryEndsHomotopy
    (he : (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryEnds A ≫ m) ≫ q = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram (u ≫ f) (v ≫ g)) :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryEnds A ≫ (m ≫ q))
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryEnds A ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathTransportTarget d) where
  h := (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathEndsHomotopy d).h
  h₀ := by
    change SSet.ι₀ ≫ (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathEndsHomotopy d).h = _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryEnds A ≫ (m ≫ q)
    rw [SSet.Homotopy.h₀, ← Category.assoc, he]
  h₁ := by
    change SSet.ι₁ ≫ (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathEndsHomotopy d).h =
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryEnds A ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathTransportTarget d
    rw [SSet.Homotopy.h₁, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathTransportTarget_ends]
  rel := (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathEndsHomotopy d).rel

/-- 概要：元の部分 path と二入力の全輸送を全相対境界上へ貼り合わせる。
方針：厳密に一致する共通部分で押し出しホモトピーを使う。
規約：両側の全円柱を保持。使われ方：模型本体の相対持ち上げの指定境界。 -/
def relativePathBoundaryTransportHomotopy
    (hk : (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundarySide A ≫ m) ≫ q = _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackPathPrism p f g a)
    (he : (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryEnds A ≫ m) ≫ q = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram (u ≫ f) (v ≫ g)) :
    SSet.Homotopy (m ≫ q) (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathTransportTarget d) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pushoutHomotopy (Subcomplex.unionProd.isPushout (boundary 1) A)
    (relativePathBoundarySideHomotopy d hk) (relativePathBoundaryEndsHomotopy d he)
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryCylinder_compatible d)

end SerrePositivity.InfinityCategories.Project.FilteredExchange
