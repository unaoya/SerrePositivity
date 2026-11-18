module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedProbeTensorFrame
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameOverFunctor

/-!
# 元の標準 probe frame と正規化テンソル frame の共通 Hom

概要：同じ probe 上の二つの全 frame を同じ共通始域へ比較する。
方針：元の augmentation の実 Reedy 共通置換を使う。
規約：始域と標的に自然な実 Hom 射を保つ。
使われ方：標準 source frame Hom と実 Dold–Kan Hom の接続。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.HomotopicalAlgebra
open _root_.SerrePositivity.Reedy
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.HomotopyFunctionComplex
variable (A : Type u) [CommRing A]

def normalizedProbeStandardFrame : Complex A ⥤ (SimplexCategory ⥤ Complex A) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  exact _root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A ⋙
    (cosimplicialResolutionFamily (_root_.SerrePositivity.ComplexLimits.mappingCofibrantFactorization A)).obj

def normalizedProbeStandardHom : (Complex A)ᵒᵖ ⥤ Complex A ⥤ SSet.{u} :=
  (_root_.SerrePositivity.ComplexLimits.normalizedProbeStandardFrame A).op ⋙ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomBifunctor

def normalizedProbeTensorHom : (Complex A)ᵒᵖ ⥤ Complex A ⥤ SSet.{u} :=
  (_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorFrame A).op ⋙ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomBifunctor

def normalizedProbeCommonFrame : Complex A ⥤ (SimplexCategory ⥤ Complex A) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  exact FrameOverFunctor.commonObj (_root_.SerrePositivity.ComplexLimits.mappingCofibrantFactorization A)
    (cosimplicialResolutionFamily (_root_.SerrePositivity.ComplexLimits.mappingCofibrantFactorization A)) (_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A)
    (_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorFrame A) (_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorAugmentation A)

def normalizedProbeHomMiddle : (Complex A)ᵒᵖ ⥤ Complex A ⥤ SSet.{u} :=
  (_root_.SerrePositivity.ComplexLimits.normalizedProbeCommonFrame A).op ⋙ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomBifunctor

def normalizedProbeHomFromStandard : _root_.SerrePositivity.ComplexLimits.normalizedProbeStandardHom A ⟶ _root_.SerrePositivity.ComplexLimits.normalizedProbeHomMiddle A := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  exact FrameOverFunctor.homLeft (_root_.SerrePositivity.ComplexLimits.mappingCofibrantFactorization A)
    (cosimplicialResolutionFamily (_root_.SerrePositivity.ComplexLimits.mappingCofibrantFactorization A)) (_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A)
    (_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorFrame A) (_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorAugmentation A)

def normalizedProbeHomFromTensor : _root_.SerrePositivity.ComplexLimits.normalizedProbeTensorHom A ⟶ _root_.SerrePositivity.ComplexLimits.normalizedProbeHomMiddle A := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  exact FrameOverFunctor.homRight (_root_.SerrePositivity.ComplexLimits.mappingCofibrantFactorization A)
    (cosimplicialResolutionFamily (_root_.SerrePositivity.ComplexLimits.mappingCofibrantFactorization A)) (_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A)
    (_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorFrame A) (_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorAugmentation A)

end SerrePositivity.ComplexLimits
