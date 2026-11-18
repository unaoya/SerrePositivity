module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedProbeHomKan

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
open SerrePositivity.HomotopyFunctionComplex _root_.SerrePositivity.ComplexLimits
variable (A : Type u) [CommRing A]

def complexNormalizedCommonRight :
    _root_.SerrePositivity.ComplexLimits.normalizedProbeCommonFrame A ⟶ _root_.SerrePositivity.ComplexLimits.normalizedProbeTensorFrame A := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  exact FrameOverFunctor.right (_root_.SerrePositivity.ComplexLimits.mappingCofibrantFactorization A)
    (cosimplicialResolutionFamily (_root_.SerrePositivity.ComplexLimits.mappingCofibrantFactorization A))
    (_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A) (_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorFrame A) (_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorAugmentation A)

def complexNormalizedCommonAugmentation :
    _root_.SerrePositivity.ComplexLimits.normalizedProbeCommonFrame A ⟶ _root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A ⋙ Functor.const SimplexCategory :=
  complexNormalizedCommonRight A ≫ _root_.SerrePositivity.ComplexLimits.normalizedProbeTensorAugmentation A

def complexNormalizedCommonLeft :
    _root_.SerrePositivity.ComplexLimits.normalizedProbeCommonFrame A ⟶ _root_.SerrePositivity.ComplexLimits.normalizedProbeStandardFrame A := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  exact FrameOverFunctor.left (_root_.SerrePositivity.ComplexLimits.mappingCofibrantFactorization A)
    (cosimplicialResolutionFamily (_root_.SerrePositivity.ComplexLimits.mappingCofibrantFactorization A))
    (_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A) (_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorFrame A) (_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorAugmentation A)

lemma complexNormalizedCommonLeft_over :
    let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
    complexNormalizedCommonLeft A ≫ Functor.whiskerLeft (_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A)
      (cosimplicialResolutionFamily (_root_.SerrePositivity.ComplexLimits.mappingCofibrantFactorization A)).augmentation =
      complexNormalizedCommonAugmentation A := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  exact FrameOverFunctor.over (_root_.SerrePositivity.ComplexLimits.mappingCofibrantFactorization A)
    (cosimplicialResolutionFamily (_root_.SerrePositivity.ComplexLimits.mappingCofibrantFactorization A))
    (_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A) (_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorFrame A) (_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorAugmentation A)

lemma complexNormalizedCommonAugmentation_weak (X : Complex A) (n : SimplexCategory) :
    QuasiIso (((complexNormalizedCommonAugmentation A).app X).app n) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  have hr := FrameOverFunctor.right_weakEquivalence (_root_.SerrePositivity.ComplexLimits.mappingCofibrantFactorization A)
    (cosimplicialResolutionFamily (_root_.SerrePositivity.ComplexLimits.mappingCofibrantFactorization A))
    (_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A) (_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorFrame A)
    (_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorAugmentation A) X n
  exact (weakEquivalences (Complex A)).comp_mem _ _ hr
    (_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorAugmentation_weak A X n)

lemma complexNormalizedCommon_map_weak (X : Complex A)
    {n m : SimplexCategory} (f : n ⟶ m) :
    QuasiIso (((_root_.SerrePositivity.ComplexLimits.normalizedProbeCommonFrame A).obj X).map f) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  exact FrameOverFunctor.commonObj_homotopicallyConstant (_root_.SerrePositivity.ComplexLimits.mappingCofibrantFactorization A)
    (cosimplicialResolutionFamily (_root_.SerrePositivity.ComplexLimits.mappingCofibrantFactorization A))
    (_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A) (_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorFrame A)
    (_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorAugmentation A) (_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorAugmentation_weak A) X f

end SerrePositivity.EInfinity.PowerOperation
