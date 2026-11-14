module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IntervalBoundary
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismContraction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.VertexFiberMap
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwiseIntervalPullback
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwiseIntervalPullbackMaps
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwisePullbackPathPrism
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwisePullbackPathPrismHomotopy
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwisePullbackValue
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.IntervalBoundaryExt
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.IntervalBoundaryHomotopy
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.IntervalDiagram
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.RelativePathBoundary
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.RelativePathInputTransportData

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
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange
variable {K M E D H B : SSet.{u}} {p : H ⟶ B} {f : E ⟶ H} {g : D ⟶ H}
  {A : K.Subcomplex} {u : K ⟶ E} {v : K ⟶ D}
  {a : (A : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullback p f g}
  {m : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryShape A ⟶ M} {q : M ⟶ H}
  (d : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativePathInputTransportData p f g A u v a m q)

/-- 概要：二入力の指定円柱を区間境界上に記録する。
方針：元の f・g で写した円柱を境界上で組にする。
規約：全時刻。使われ方：相対境界の両端の全円柱。 -/
def relativePathEndsHomotopy := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalBoundaryHomotopy
  (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp d.leftHomotopy f) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp d.rightHomotopy g)

/-- 概要：元の境界 path の正方形と二入力の境界円柱は共通部分で厳密に一致。
方針：両端で元の入力の部分円柱の式を使う。
規約：全円柱。使われ方：押し出し上のホモトピーの貼り合わせ。 -/
lemma relativePathBoundaryCylinder_compatible :
    (((boundary 1).ι ▷ (A : SSet.{u})) ▷ (Δ[1] : SSet.{u})) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackPathPrismHomotopy p f g d.boundaryHomotopy).h =
    (((boundary 1 : SSet.{u}) ◁ A.ι) ▷ (Δ[1] : SSet.{u})) ≫
      (relativePathEndsHomotopy d).h := by
  apply _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalBoundaryCylinder_hom_ext
  · change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (A : SSet.{u}) ▷ (Δ[1] : SSet.{u})) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackPathPrismHomotopy p f g d.boundaryHomotopy).h =
        (A.ι ▷ (Δ[1] : SSet.{u})) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint 0 K ▷ (Δ[1] : SSet.{u})) ≫
          (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalBoundaryHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp d.leftHomotopy f)
            (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp d.rightHomotopy g)).h
    rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackPathPrismHomotopy_zero, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalBoundaryHomotopy_zero]
    change d.boundaryHomotopy.h ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackLeft p f g ≫ f =
      (A.ι ▷ (Δ[1] : SSet.{u})) ≫ (d.leftHomotopy.h ≫ f)
    exact congrArg (fun r ↦ r ≫ f) d.left_restrict.symm
  · change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (A : SSet.{u}) ▷ (Δ[1] : SSet.{u})) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackPathPrismHomotopy p f g d.boundaryHomotopy).h =
        (A.ι ▷ (Δ[1] : SSet.{u})) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint 1 K ▷ (Δ[1] : SSet.{u})) ≫
          (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalBoundaryHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp d.leftHomotopy f)
            (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp d.rightHomotopy g)).h
    rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackPathPrismHomotopy_one, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalBoundaryHomotopy_one]
    change d.boundaryHomotopy.h ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackRight p f g ≫ g =
      (A.ι ▷ (Δ[1] : SSet.{u})) ≫ (d.rightHomotopy.h ≫ g)
    exact congrArg (fun r ↦ r ≫ g) d.right_restrict.symm

/-- 概要：二入力の全境界円柱の底は元の模型の底円柱に一致。
方針：区間境界の二端点で指定底射の式を使う。
規約：全時刻。使われ方：全相対境界の底条件。 -/
lemma relativePathEndsHomotopy_projection :
    (relativePathEndsHomotopy d).h ≫ p =
      ((_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryEnds A ≫ m) ▷ (Δ[1] : SSet.{u})) ≫ d.modelBase.h := by
  apply _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalBoundaryCylinder_hom_ext
  · change ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint 0 K ▷ (Δ[1] : SSet.{u})) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalBoundaryHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp d.leftHomotopy f)
        (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp d.rightHomotopy g)).h) ≫ p =
        ((_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryEndpoint A 0 ≫ m) ▷ (Δ[1] : SSet.{u})) ≫ d.modelBase.h
    rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalBoundaryHomotopy_zero]
    exact d.left_projection
  · change ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint 1 K ▷ (Δ[1] : SSet.{u})) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalBoundaryHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp d.leftHomotopy f)
        (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp d.rightHomotopy g)).h) ≫ p =
        ((_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryEndpoint A 1 ≫ m) ▷ (Δ[1] : SSet.{u})) ≫ d.modelBase.h
    rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalBoundaryHomotopy_one]
    exact d.right_projection

end SerrePositivity.InfinityCategories.Project.FilteredExchange
