module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.PointSlicePostcomp
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.RightFibrationFiberCriterion
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftUnstraighteningFiberIso

/-!
概要：元の指定頂点の slice から、像の頂点の slice を元の始域へ引き戻した圏への比較。
方針：正規化した全後合成と、元の始点射影を引き戻しに束ねる。
規約：元の関手に inner fibration 性を要求しない。
使われ方：充満忠実な関手の局所 Kan 恒等頂点の終対象性。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {C D : SSet.{u}} (f : C ⟶ D) (y : C _⦋0⦌)

/-- 像の指定頂点の slice を、元の始域に沿って引き戻した圏。 -/
abbrev pointSlicePullback : SSet.{u} :=
  pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm (f.app (Opposite.op ⦋0⦌) y))) f

/-- 同じ引き戻しから元の始域への射影。 -/
def pointSlicePullbackProjection : pointSlicePullback f y ⟶ C := pullback.snd _ _

instance pointSlicePullbackProjection_rightFibration [Quasicategory D] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration (pointSlicePullbackProjection f y) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightFibrations.pullback_snd _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration.mem (p :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm (f.app (Opposite.op ⦋0⦌) y))))⟩

instance pointSlicePullback_quasicategory [Quasicategory C] [Quasicategory D] :
    Quasicategory (pointSlicePullback f y) :=
  quasicategory_of_innerFibration (pointSlicePullbackProjection f y)

/-- 元の指定頂点の slice から、同じ始点の引き戻しへの比較。 -/
def pointSliceComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm y) ⟶ pointSlicePullback f y :=
  pullback.lift (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.pointSlicePostcomp f y) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm y))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.pointSlicePostcomp_projection f y)

/-- 同じ比較は元の始点射影を厳密に保つ。 -/
lemma pointSliceComparison_projection :
    pointSliceComparison f y ≫ pointSlicePullbackProjection f y =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm y) := pullback.lift_snd _ _ _

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
