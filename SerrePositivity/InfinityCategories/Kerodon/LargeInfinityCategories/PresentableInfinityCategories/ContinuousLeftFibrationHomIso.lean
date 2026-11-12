module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ContinuousLeftFibrationAnodyne
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.RelativeFunctorPrecompositionComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationCoherentEvaluation

/-!
概要：連続 left fibration 置換は、元の底上の相対 Hom の全 coherent な関手を保つ。
方針：元の単位の左アノダイン性を F1 の全豊穣比較へ渡し、底上の可換条件を読み戻す。
規約：比較は全対象・全射・全高次単体を含む関手同型であり、対象ごとの同値に留めない。
使われ方：有限底上模型の置換の compact 性。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 具体的な置換の底上の値を、元の宇宙の left fibration として束ねる。 -/
def continuousReplacementLeftFibrationObject {B : SSet.{u}} (X : Over B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B :=
  ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.continuousLeftFibrationReplacement B).obj X, inferInstance⟩

/-- 元の単位による相対 Hom の比較は、coherent な全評価関手の同型。 -/
def continuousLeftFibrationHomIso {B : SSet.{u}} (X : Over B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationCoherentEvaluation ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.continuousLeftFibrationReplacement B).obj X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationCoherentEvaluation X) := by
  let R := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.continuousLeftFibrationReplacement B).obj X
  let η : X ⟶ R := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.continuousLeftFibrationReplacementUnit B).app X
  have hη : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions η.left :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.continuousLeftFibrationReplacementUnit_leftAnodyne X
  have hbase : η.left ≫ R.hom = X.hom := η.w
  have h := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorPrecompositionComparisonIso R.hom η.left hη
  rw [hbase] at h
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationCoherentEvaluation (Over.mk R.hom))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationCoherentEvaluation (Over.mk X.hom)) at h
  have hR : Over.mk R.hom = R := (CostructuredArrow.eq_mk R).symm
  have hX : Over.mk X.hom = X := (CostructuredArrow.eq_mk X).symm
  rw [hR, hX] at h
  exact h

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
