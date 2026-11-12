module

public import SerrePositivity.EInfinity.ComplexLimits.NormalizedProbeHomKan

/-!
# 全複体の指定共通 frame の左右射と augmentation

DAG XIII §2.2 のスペクトル忘却の降下で使う屋根比較への前段。
標準 frame・正規化テンソル frame の同じ共通置換と厳密な三角形を保持する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.Reedy SerrePositivity.DifferentialGraded
open SerrePositivity.HomotopyFunctionComplex SerrePositivity.EInfinity.ComplexLimits
variable (A : Type u) [CommRing A]

def complexNormalizedCommonRight :
    normalizedProbeCommonFrame A ⟶ normalizedProbeTensorFrame A := by
  let := projectiveModelCategory A
  exact FrameOverFunctor.right (mappingCofibrantFactorization A)
    (cosimplicialResolutionFamily (mappingCofibrantFactorization A))
    (framedLimitProbeFunctor A) (normalizedProbeTensorFrame A) (normalizedProbeTensorAugmentation A)

def complexNormalizedCommonAugmentation :
    normalizedProbeCommonFrame A ⟶ framedLimitProbeFunctor A ⋙ Functor.const SimplexCategory :=
  complexNormalizedCommonRight A ≫ normalizedProbeTensorAugmentation A

def complexNormalizedCommonLeft :
    normalizedProbeCommonFrame A ⟶ normalizedProbeStandardFrame A := by
  let := projectiveModelCategory A
  exact FrameOverFunctor.left (mappingCofibrantFactorization A)
    (cosimplicialResolutionFamily (mappingCofibrantFactorization A))
    (framedLimitProbeFunctor A) (normalizedProbeTensorFrame A) (normalizedProbeTensorAugmentation A)

lemma complexNormalizedCommonLeft_over :
    let := projectiveModelCategory A
    complexNormalizedCommonLeft A ≫ Functor.whiskerLeft (framedLimitProbeFunctor A)
      (cosimplicialResolutionFamily (mappingCofibrantFactorization A)).augmentation =
      complexNormalizedCommonAugmentation A := by
  let := projectiveModelCategory A
  exact FrameOverFunctor.over (mappingCofibrantFactorization A)
    (cosimplicialResolutionFamily (mappingCofibrantFactorization A))
    (framedLimitProbeFunctor A) (normalizedProbeTensorFrame A) (normalizedProbeTensorAugmentation A)

lemma complexNormalizedCommonAugmentation_weak (X : Complex A) (n : SimplexCategory) :
    QuasiIso (((complexNormalizedCommonAugmentation A).app X).app n) := by
  let := projectiveModelCategory A
  have hr := FrameOverFunctor.right_weakEquivalence (mappingCofibrantFactorization A)
    (cosimplicialResolutionFamily (mappingCofibrantFactorization A))
    (framedLimitProbeFunctor A) (normalizedProbeTensorFrame A)
    (normalizedProbeTensorAugmentation A) X n
  exact (weakEquivalences (Complex A)).comp_mem _ _ hr
    (normalizedProbeTensorAugmentation_weak A X n)

lemma complexNormalizedCommon_map_weak (X : Complex A)
    {n m : SimplexCategory} (f : n ⟶ m) :
    QuasiIso (((normalizedProbeCommonFrame A).obj X).map f) := by
  let := projectiveModelCategory A
  exact FrameOverFunctor.commonObj_homotopicallyConstant (mappingCofibrantFactorization A)
    (cosimplicialResolutionFamily (mappingCofibrantFactorization A))
    (framedLimitProbeFunctor A) (normalizedProbeTensorFrame A)
    (normalizedProbeTensorAugmentation A) (normalizedProbeTensorAugmentation_weak A) X f

end SerrePositivity.EInfinity.PowerOperation
