module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedOriginalHomComparison

/-!
# 元の複体射の全単体表示と同じ Hom 比較の整合

概要：元の複体射を二つの augmentation で表した全単体は、同じ共通 Hom で一致する。
方針：始域置換に対する標準 augmentation の自然性と実共通 frame の全三角形を合成。
規約：元の射・同じ置換比較・全次数を保つ。
使われ方：元の単位射の正規化 frame による表示の回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.HomotopicalAlgebra
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.Reedy
open _root_.SerrePositivity.HomotopyFunctionComplex
variable (A : Type u) [CommRing A]

lemma normalizedOriginalHomComparison_augmentation (X Y : Complex A) (f : X ⟶ Y)
    (n : SimplexCategory) :
    letI := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
    let q := cosimplicialResolutionFamily (_root_.SerrePositivity.ComplexLimits.mappingCofibrantFactorization A)
    ((((_root_.SerrePositivity.ComplexLimits.normalizedOriginalHomComparison A).app (Opposite.op X)).app Y).app (Opposite.op n))
      ((q.augmentation.app X).app n ≫ f) =
    ((((_root_.SerrePositivity.ComplexLimits.normalizedProbeHomFromTensor A).app (Opposite.op X)).app Y).app (Opposite.op n))
      ((((_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorAugmentation A).app X).app n) ≫
        _root_.SerrePositivity.ComplexLimits.framedLimitProbeComparison A X ≫ f) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  let q := cosimplicialResolutionFamily (_root_.SerrePositivity.ComplexLimits.mappingCofibrantFactorization A)
  let Q := _root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A
  let a := _root_.SerrePositivity.ComplexLimits.normalizedProbeTensorAugmentation A
  let L := FrameOverFunctor.left (_root_.SerrePositivity.ComplexLimits.mappingCofibrantFactorization A) q Q
    (_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorFrame A) a
  let R := FrameOverFunctor.right (_root_.SerrePositivity.ComplexLimits.mappingCofibrantFactorization A) q Q
    (_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorFrame A) a
  have hq := congr_app (q.augmentation.naturality (_root_.SerrePositivity.ComplexLimits.framedLimitProbeComparison A X)) n
  change (q.obj.map (_root_.SerrePositivity.ComplexLimits.framedLimitProbeComparison A X)).app n ≫
      (q.augmentation.app X).app n =
    (q.augmentation.app (Q.obj X)).app n ≫ _root_.SerrePositivity.ComplexLimits.framedLimitProbeComparison A X at hq
  have ho := congr_app (congr_app (FrameOverFunctor.over
    (_root_.SerrePositivity.ComplexLimits.mappingCofibrantFactorization A) q Q (_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorFrame A) a) X) n
  change (L.app X).app n ≫ (q.augmentation.app (Q.obj X)).app n =
    (R.app X).app n ≫ (a.app X).app n at ho
  change (L.app X).app n ≫ ((q.obj.map (_root_.SerrePositivity.ComplexLimits.framedLimitProbeComparison A X)).app n ≫
      ((q.augmentation.app X).app n ≫ f)) =
    (R.app X).app n ≫ ((a.app X).app n ≫ _root_.SerrePositivity.ComplexLimits.framedLimitProbeComparison A X ≫ f)
  calc
    _ = (L.app X).app n ≫ ((q.augmentation.app (Q.obj X)).app n ≫
        _root_.SerrePositivity.ComplexLimits.framedLimitProbeComparison A X ≫ f) := by
      simpa only [Category.assoc] using congrArg (fun k => (L.app X).app n ≫ k ≫ f) hq
    _ = _ := by
      simpa only [Category.assoc] using
        congrArg (fun k => k ≫ _root_.SerrePositivity.ComplexLimits.framedLimitProbeComparison A X ≫ f) ho

end SerrePositivity.ComplexLimits
