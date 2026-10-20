module

public import SerrePositivity.InfinityCategories.F2.RelativePathTransportTarget
public import SerrePositivity.InfinityCategories.F2.RelativePathBoundaryCylinderCompatibility
public import SerrePositivity.InfinityCategories.Core.PushoutHomotopy

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
namespace SerrePositivity.InfinityCategories.F2
variable {K M E D H B : SSet.{u}} {p : H ⟶ B} {f : E ⟶ H} {g : D ⟶ H}
  {A : K.Subcomplex} {u : K ⟶ E} {v : K ⟶ D}
  {a : (A : SSet.{u}) ⟶ fiberwiseIntervalPullback p f g}
  {m : relativePathBoundaryShape A ⟶ M} {q : M ⟶ H}
  (d : RelativePathInputTransportData p f g A u v a m q)

/-- 概要：元の境界 path の正方形を模型の境界表示の端点へ合わせる。
方針：端点の等式だけを照合し、元の全正方形を保持する。
規約：h を変更しない。使われ方：押し出しの部分 path 側の指定円柱。 -/
def relativePathBoundarySideHomotopy
    (hk : (relativePathBoundarySide A ≫ m) ≫ q = fiberwisePullbackPathPrism p f g a) :
    SSet.Homotopy (relativePathBoundarySide A ≫ (m ≫ q))
      (relativePathBoundarySide A ≫ relativePathTransportTarget d) where
  h := (fiberwisePullbackPathPrismHomotopy p f g d.boundaryHomotopy).h
  h₀ := by
    change SSet.ι₀ ≫ (fiberwisePullbackPathPrismHomotopy p f g d.boundaryHomotopy).h =
      relativePathBoundarySide A ≫ (m ≫ q)
    rw [SSet.Homotopy.h₀, ← Category.assoc, hk]
  h₁ := by
    change SSet.ι₁ ≫ (fiberwisePullbackPathPrismHomotopy p f g d.boundaryHomotopy).h =
      relativePathBoundarySide A ≫ relativePathTransportTarget d
    rw [SSet.Homotopy.h₁, relativePathTransportTarget_side]
  rel := (fiberwisePullbackPathPrismHomotopy p f g d.boundaryHomotopy).rel

/-- 概要：二入力の全境界円柱を模型の両端表示へ合わせる。
方針：元の二つの全円柱を保ち、両端の等式を照合する。
規約：h を変更しない。使われ方：押し出しの二端点側の指定円柱。 -/
def relativePathBoundaryEndsHomotopy
    (he : (relativePathBoundaryEnds A ≫ m) ≫ q = intervalBoundaryDiagram (u ≫ f) (v ≫ g)) :
    SSet.Homotopy (relativePathBoundaryEnds A ≫ (m ≫ q))
      (relativePathBoundaryEnds A ≫ relativePathTransportTarget d) where
  h := (relativePathEndsHomotopy d).h
  h₀ := by
    change SSet.ι₀ ≫ (relativePathEndsHomotopy d).h = relativePathBoundaryEnds A ≫ (m ≫ q)
    rw [SSet.Homotopy.h₀, ← Category.assoc, he]
  h₁ := by
    change SSet.ι₁ ≫ (relativePathEndsHomotopy d).h =
      relativePathBoundaryEnds A ≫ relativePathTransportTarget d
    rw [SSet.Homotopy.h₁, relativePathTransportTarget_ends]
  rel := (relativePathEndsHomotopy d).rel

/-- 概要：元の部分 path と二入力の全輸送を全相対境界上へ貼り合わせる。
方針：厳密に一致する共通部分で押し出しホモトピーを使う。
規約：両側の全円柱を保持。使われ方：模型本体の相対持ち上げの指定境界。 -/
def relativePathBoundaryTransportHomotopy
    (hk : (relativePathBoundarySide A ≫ m) ≫ q = fiberwisePullbackPathPrism p f g a)
    (he : (relativePathBoundaryEnds A ≫ m) ≫ q = intervalBoundaryDiagram (u ≫ f) (v ≫ g)) :
    SSet.Homotopy (m ≫ q) (relativePathTransportTarget d) :=
  pushoutHomotopy (Subcomplex.unionProd.isPushout (boundary 1) A)
    (relativePathBoundarySideHomotopy d hk) (relativePathBoundaryEndsHomotopy d he)
    (relativePathBoundaryCylinder_compatible d)

end SerrePositivity.InfinityCategories.F2
