module

public import SerrePositivity.EInfinity.BarrattEccles.FreeNormalizedProbeFrameProperties

/-!
# 標準自由 probe Hom と実正規化 Hom の同じ共通フレーム

概要：元の自由 probe の標準 Hom と正規化 frame Hom を同じ実共通 Hom へ送る。
方針：同じ FQX 上の全 augmentation と実随伴 Hom 同型を使う。
規約：標準 sourceFrameHom と元の全自由忘却随伴を保つ。
使われ方：標準単位射と正規化 DK Hom の全比較。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.DifferentialGraded SerrePositivity.Reedy
open SerrePositivity.HomotopyFunctionComplex

variable (A : Type u) [CommRing A]

def freeNormalizedProbeHom : (Complex A)ᵒᵖ ⥤ (operad A).Algebra ⥤ SSet.{u} :=
  (freeNormalizedProbeFrame A).op ⋙ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomBifunctor

def freeNormalizedCommonFrame : Complex A ⥤ (SimplexCategory ⥤ (operad A).Algebra) := by
  let := modelCategory A
  exact FrameOverFunctor.commonObj (mappingCofibrantFactorization A)
    (cosimplicialResolutionFamily (mappingCofibrantFactorization A))
    (freeProbeFunctor A) (freeNormalizedProbeFrame A) (freeNormalizedProbeAugmentation A)

def freeNormalizedHomMiddle : (Complex A)ᵒᵖ ⥤ (operad A).Algebra ⥤ SSet.{u} :=
  (freeNormalizedCommonFrame A).op ⋙ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomBifunctor

def freeNormalizedHomFromStandard :
    (freeProbeFunctor A).op ⋙ sourceFrameHom A ⟶ freeNormalizedHomMiddle A := by
  let := modelCategory A
  exact FrameOverFunctor.homLeft (mappingCofibrantFactorization A)
    (cosimplicialResolutionFamily (mappingCofibrantFactorization A))
    (freeProbeFunctor A) (freeNormalizedProbeFrame A) (freeNormalizedProbeAugmentation A)

def freeNormalizedHomFromTensor : freeNormalizedProbeHom A ⟶ freeNormalizedHomMiddle A := by
  let := modelCategory A
  exact FrameOverFunctor.homRight (mappingCofibrantFactorization A)
    (cosimplicialResolutionFamily (mappingCofibrantFactorization A))
    (freeProbeFunctor A) (freeNormalizedProbeFrame A) (freeNormalizedProbeAugmentation A)

def freeNormalizedProbeHomAdjunctionIso :
    freeNormalizedProbeHom A ≅ _root_.SerrePositivity.ComplexLimits.normalizedProbeTensorHom A ⋙
      (Functor.whiskeringLeft (operad A).Algebra (Complex A) SSet.{u}).obj
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget (operad A)) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.adjunctionFrameHomBifunctorIso (operad A).freeAlgebraAdjunction
    (_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorFrame A) (𝟭 (operad A).Algebra)

end SerrePositivity.EInfinity.BarrattEccles
