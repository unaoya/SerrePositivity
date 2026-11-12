module

public import SerrePositivity.EInfinity.ComplexLimits.NormalizedProbeTensorFrame
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
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.Reedy
open SerrePositivity.DifferentialGraded SerrePositivity.HomotopyFunctionComplex
variable (A : Type u) [CommRing A]

def normalizedProbeStandardFrame : Complex A ⥤ (SimplexCategory ⥤ Complex A) := by
  let := projectiveModelCategory A
  exact framedLimitProbeFunctor A ⋙
    (cosimplicialResolutionFamily (mappingCofibrantFactorization A)).obj

def normalizedProbeStandardHom : (Complex A)ᵒᵖ ⥤ Complex A ⥤ SSet.{u} :=
  (normalizedProbeStandardFrame A).op ⋙ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomBifunctor

def normalizedProbeTensorHom : (Complex A)ᵒᵖ ⥤ Complex A ⥤ SSet.{u} :=
  (normalizedProbeTensorFrame A).op ⋙ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomBifunctor

def normalizedProbeCommonFrame : Complex A ⥤ (SimplexCategory ⥤ Complex A) := by
  let := projectiveModelCategory A
  exact FrameOverFunctor.commonObj (mappingCofibrantFactorization A)
    (cosimplicialResolutionFamily (mappingCofibrantFactorization A)) (framedLimitProbeFunctor A)
    (normalizedProbeTensorFrame A) (normalizedProbeTensorAugmentation A)

def normalizedProbeHomMiddle : (Complex A)ᵒᵖ ⥤ Complex A ⥤ SSet.{u} :=
  (normalizedProbeCommonFrame A).op ⋙ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomBifunctor

def normalizedProbeHomFromStandard : normalizedProbeStandardHom A ⟶ normalizedProbeHomMiddle A := by
  let := projectiveModelCategory A
  exact FrameOverFunctor.homLeft (mappingCofibrantFactorization A)
    (cosimplicialResolutionFamily (mappingCofibrantFactorization A)) (framedLimitProbeFunctor A)
    (normalizedProbeTensorFrame A) (normalizedProbeTensorAugmentation A)

def normalizedProbeHomFromTensor : normalizedProbeTensorHom A ⟶ normalizedProbeHomMiddle A := by
  let := projectiveModelCategory A
  exact FrameOverFunctor.homRight (mappingCofibrantFactorization A)
    (cosimplicialResolutionFamily (mappingCofibrantFactorization A)) (framedLimitProbeFunctor A)
    (normalizedProbeTensorFrame A) (normalizedProbeTensorAugmentation A)

end SerrePositivity.EInfinity.ComplexLimits
