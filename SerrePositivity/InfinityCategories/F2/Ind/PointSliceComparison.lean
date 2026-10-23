module

public import SerrePositivity.InfinityCategories.F2.Ind.PointSlicePostcomp
public import SerrePositivity.InfinityCategories.F2.Ind.RightFibrationFiberCriterion
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningFiberIso

/-!
概要：元の指定頂点の slice から、像の頂点の slice を元の始域へ引き戻した圏への比較。
方針：正規化した全後合成と、元の始点射影を引き戻しに束ねる。
規約：元の関手に inner fibration 性を要求しない。
使われ方：充満忠実な関手の局所 Kan 恒等頂点の終対象性。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C D : SSet.{u}} (f : C ⟶ D) (y : C _⦋0⦌)

/-- 像の指定頂点の slice を、元の始域に沿って引き戻した圏。 -/
abbrev pointSlicePullback : SSet.{u} :=
  pullback (sliceOverProjection (SSet.yonedaEquiv.symm (f.app (Opposite.op ⦋0⦌) y))) f

/-- 同じ引き戻しから元の始域への射影。 -/
def pointSlicePullbackProjection : pointSlicePullback f y ⟶ C := pullback.snd _ _

instance pointSlicePullbackProjection_rightFibration [Quasicategory D] :
    RightFibration (pointSlicePullbackProjection f y) :=
  ⟨rightFibrations.pullback_snd _ _ (RightFibration.mem (p :=
    sliceOverProjection (SSet.yonedaEquiv.symm (f.app (Opposite.op ⦋0⦌) y))))⟩

instance pointSlicePullback_quasicategory [Quasicategory C] [Quasicategory D] :
    Quasicategory (pointSlicePullback f y) :=
  quasicategory_of_innerFibration (pointSlicePullbackProjection f y)

/-- 元の指定頂点の slice から、同じ始点の引き戻しへの比較。 -/
def pointSliceComparison : sliceOver (SSet.yonedaEquiv.symm y) ⟶ pointSlicePullback f y :=
  pullback.lift (pointSlicePostcomp f y) (sliceOverProjection (SSet.yonedaEquiv.symm y))
    (pointSlicePostcomp_projection f y)

/-- 同じ比較は元の始点射影を厳密に保つ。 -/
lemma pointSliceComparison_projection :
    pointSliceComparison f y ≫ pointSlicePullbackProjection f y =
      sliceOverProjection (SSet.yonedaEquiv.symm y) := pullback.lift_snd _ _ _

end SerrePositivity.InfinityCategories.F2.Ind
