module

public import SerrePositivity.InfinityCategories.F2.RelativePathInputTransportData
public import SerrePositivity.InfinityCategories.F2.FiberwisePullbackPathPrismHomotopy
public import SerrePositivity.InfinityCategories.F2.IntervalBoundaryHomotopy
public import SerrePositivity.InfinityCategories.F1B.HomotopyWhiskering

/-!
概要：元の境界 path の全輸送と二入力の全円柱は、相対境界の共通部分で一致する。
方針：区間境界上の全円柱の二端点を照合する。
規約：元の全円柱を保持し、底射の像も全時刻で一致させる。
使われ方：全相対境界円柱の貼り合わせと標的模型への相対持ち上げ。
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

/-- 概要：二入力の指定円柱を区間境界上に記録する。
方針：元の f・g で写した円柱を境界上で組にする。
規約：全時刻。使われ方：相対境界の両端の全円柱。 -/
def relativePathEndsHomotopy := intervalBoundaryHomotopy
  (functorHomotopyPostcomp d.leftHomotopy f) (functorHomotopyPostcomp d.rightHomotopy g)

/-- 概要：元の境界 path の正方形と二入力の境界円柱は共通部分で厳密に一致。
方針：両端で元の入力の部分円柱の式を使う。
規約：全円柱。使われ方：押し出し上のホモトピーの貼り合わせ。 -/
lemma relativePathBoundaryCylinder_compatible :
    (((boundary 1).ι ▷ (A : SSet.{u})) ▷ (Δ[1] : SSet.{u})) ≫
      (fiberwisePullbackPathPrismHomotopy p f g d.boundaryHomotopy).h =
    (((boundary 1 : SSet.{u}) ◁ A.ι) ▷ (Δ[1] : SSet.{u})) ≫
      (relativePathEndsHomotopy d).h := by
  apply intervalBoundaryCylinder_hom_ext
  · change (prismEndpoint 0 (A : SSet.{u}) ▷ (Δ[1] : SSet.{u})) ≫
      (fiberwisePullbackPathPrismHomotopy p f g d.boundaryHomotopy).h =
        (A.ι ▷ (Δ[1] : SSet.{u})) ≫ (intervalBoundaryEndpoint 0 K ▷ (Δ[1] : SSet.{u})) ≫
          (intervalBoundaryHomotopy (functorHomotopyPostcomp d.leftHomotopy f)
            (functorHomotopyPostcomp d.rightHomotopy g)).h
    rw [fiberwisePullbackPathPrismHomotopy_zero, intervalBoundaryHomotopy_zero]
    change d.boundaryHomotopy.h ≫ fiberwiseIntervalPullbackLeft p f g ≫ f =
      (A.ι ▷ (Δ[1] : SSet.{u})) ≫ (d.leftHomotopy.h ≫ f)
    exact congrArg (fun r ↦ r ≫ f) d.left_restrict.symm
  · change (prismEndpoint 1 (A : SSet.{u}) ▷ (Δ[1] : SSet.{u})) ≫
      (fiberwisePullbackPathPrismHomotopy p f g d.boundaryHomotopy).h =
        (A.ι ▷ (Δ[1] : SSet.{u})) ≫ (intervalBoundaryEndpoint 1 K ▷ (Δ[1] : SSet.{u})) ≫
          (intervalBoundaryHomotopy (functorHomotopyPostcomp d.leftHomotopy f)
            (functorHomotopyPostcomp d.rightHomotopy g)).h
    rw [fiberwisePullbackPathPrismHomotopy_one, intervalBoundaryHomotopy_one]
    change d.boundaryHomotopy.h ≫ fiberwiseIntervalPullbackRight p f g ≫ g =
      (A.ι ▷ (Δ[1] : SSet.{u})) ≫ (d.rightHomotopy.h ≫ g)
    exact congrArg (fun r ↦ r ≫ g) d.right_restrict.symm

/-- 概要：二入力の全境界円柱の底は元の模型の底円柱に一致。
方針：区間境界の二端点で指定底射の式を使う。
規約：全時刻。使われ方：全相対境界の底条件。 -/
lemma relativePathEndsHomotopy_projection :
    (relativePathEndsHomotopy d).h ≫ p =
      ((relativePathBoundaryEnds A ≫ m) ▷ (Δ[1] : SSet.{u})) ≫ d.modelBase.h := by
  apply intervalBoundaryCylinder_hom_ext
  · change ((intervalBoundaryEndpoint 0 K ▷ (Δ[1] : SSet.{u})) ≫
      (intervalBoundaryHomotopy (functorHomotopyPostcomp d.leftHomotopy f)
        (functorHomotopyPostcomp d.rightHomotopy g)).h) ≫ p =
        ((relativePathBoundaryEndpoint A 0 ≫ m) ▷ (Δ[1] : SSet.{u})) ≫ d.modelBase.h
    rw [intervalBoundaryHomotopy_zero]
    exact d.left_projection
  · change ((intervalBoundaryEndpoint 1 K ▷ (Δ[1] : SSet.{u})) ≫
      (intervalBoundaryHomotopy (functorHomotopyPostcomp d.leftHomotopy f)
        (functorHomotopyPostcomp d.rightHomotopy g)).h) ≫ p =
        ((relativePathBoundaryEndpoint A 1 ≫ m) ▷ (Δ[1] : SSet.{u})) ≫ d.modelBase.h
    rw [intervalBoundaryHomotopy_one]
    exact d.right_projection

end SerrePositivity.InfinityCategories.F2
