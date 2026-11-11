module

public import SerrePositivity.EInfinity.ComplexLimits.NormalizedOriginalHomComparison

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
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.DifferentialGraded SerrePositivity.Reedy
open SerrePositivity.HomotopyFunctionComplex
variable (A : Type u) [CommRing A]

lemma normalizedOriginalHomComparison_augmentation (X Y : Complex A) (f : X ⟶ Y)
    (n : SimplexCategory) :
    letI := projectiveModelCategory A
    let q := cosimplicialResolutionFamily (mappingCofibrantFactorization A)
    ((((normalizedOriginalHomComparison A).app (Opposite.op X)).app Y).app (Opposite.op n))
      ((q.augmentation.app X).app n ≫ f) =
    ((((normalizedProbeHomFromTensor A).app (Opposite.op X)).app Y).app (Opposite.op n))
      ((((normalizedProbeTensorAugmentation A).app X).app n) ≫
        framedLimitProbeComparison A X ≫ f) := by
  let := projectiveModelCategory A
  let q := cosimplicialResolutionFamily (mappingCofibrantFactorization A)
  let Q := framedLimitProbeFunctor A
  let a := normalizedProbeTensorAugmentation A
  let L := FrameOverFunctor.left (mappingCofibrantFactorization A) q Q
    (normalizedProbeTensorFrame A) a
  let R := FrameOverFunctor.right (mappingCofibrantFactorization A) q Q
    (normalizedProbeTensorFrame A) a
  have hq := congr_app (q.augmentation.naturality (framedLimitProbeComparison A X)) n
  change (q.obj.map (framedLimitProbeComparison A X)).app n ≫
      (q.augmentation.app X).app n =
    (q.augmentation.app (Q.obj X)).app n ≫ framedLimitProbeComparison A X at hq
  have ho := congr_app (congr_app (FrameOverFunctor.over
    (mappingCofibrantFactorization A) q Q (normalizedProbeTensorFrame A) a) X) n
  change (L.app X).app n ≫ (q.augmentation.app (Q.obj X)).app n =
    (R.app X).app n ≫ (a.app X).app n at ho
  change (L.app X).app n ≫ ((q.obj.map (framedLimitProbeComparison A X)).app n ≫
      ((q.augmentation.app X).app n ≫ f)) =
    (R.app X).app n ≫ ((a.app X).app n ≫ framedLimitProbeComparison A X ≫ f)
  calc
    _ = (L.app X).app n ≫ ((q.augmentation.app (Q.obj X)).app n ≫
        framedLimitProbeComparison A X ≫ f) := by
      simpa only [Category.assoc] using congrArg (fun k => (L.app X).app n ≫ k ≫ f) hq
    _ = _ := by
      simpa only [Category.assoc] using
        congrArg (fun k => k ≫ framedLimitProbeComparison A X ≫ f) ho

end SerrePositivity.EInfinity.ComplexLimits
