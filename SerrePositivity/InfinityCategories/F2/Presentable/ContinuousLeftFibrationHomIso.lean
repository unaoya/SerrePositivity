module

public import SerrePositivity.InfinityCategories.F2.Presentable.ContinuousLeftFibrationAnodyne
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorPrecompositionComparison
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationCoherentEvaluation

/-!
概要：連続 left fibration 置換は、元の底上の相対 Hom の全 coherent な関手を保つ。
方針：元の単位の左アノダイン性を F1 の全豊穣比較へ渡し、底上の可換条件を読み戻す。
規約：比較は全対象・全射・全高次単体を含む関手同型であり、対象ごとの同値に留めない。
使われ方：有限底上模型の置換の compact 性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 具体的な置換の底上の値を、元の宇宙の left fibration として束ねる。 -/
def continuousReplacementLeftFibrationObject {B : SSet.{u}} (X : Over B) :
    LeftFibrationObject B :=
  ⟨(continuousLeftFibrationReplacement B).obj X, inferInstance⟩

/-- 元の単位による相対 Hom の比較は、coherent な全評価関手の同型。 -/
def continuousLeftFibrationHomIso {B : SSet.{u}} (X : Over B) :
    FunctorIso (leftFibrationCoherentEvaluation ((continuousLeftFibrationReplacement B).obj X))
      (leftFibrationCoherentEvaluation X) := by
  let R := (continuousLeftFibrationReplacement B).obj X
  let η : X ⟶ R := (continuousLeftFibrationReplacementUnit B).app X
  have hη : leftAnodyneExtensions η.left :=
    continuousLeftFibrationReplacementUnit_leftAnodyne X
  have hbase : η.left ≫ R.hom = X.hom := η.w
  have h := relativeFunctorPrecompositionComparisonIso R.hom η.left hη
  rw [hbase] at h
  change FunctorIso (leftFibrationCoherentEvaluation (Over.mk R.hom))
    (leftFibrationCoherentEvaluation (Over.mk X.hom)) at h
  have hR : Over.mk R.hom = R := (CostructuredArrow.eq_mk R).symm
  have hX : Over.mk X.hom = X := (CostructuredArrow.eq_mk X).symm
  rw [hR, hX] at h
  exact h

end SerrePositivity.InfinityCategories.F2.Presentable
