module

public import SerrePositivity.EInfinity.PowerOperation.ComplexNormalizedCommonFrame
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameRoofComparisonInvariance

/-!
# 同じ全複体の正規化・共通 frame の hammock 屋根

DAG XIII §2.2 の native な降下への前段。同じ全要素圏・augmentation を保持する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory Opposite _root_.HomotopicalAlgebra
open SerrePositivity.DifferentialGraded SerrePositivity.Reedy
open _root_.SerrePositivity.ComplexLimits
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (colimitGraph)
variable (A : Type u) [CommRing A] (X Y : Complex A)

def complexNormalizedCommonLeftIndex :
    ULiftHom.{u + 1} (((((_root_.SerrePositivity.ComplexLimits.normalizedProbeStandardHom A).obj (op X)).obj Y).Elements)ᵒᵖ) ⥤
      ULiftHom.{u + 1} (((((_root_.SerrePositivity.ComplexLimits.normalizedProbeHomMiddle A).obj (op X)).obj Y).Elements)ᵒᵖ) :=
  _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.frameSpanSourceIndexMap ((_root_.SerrePositivity.ComplexLimits.normalizedProbeCommonFrame A).obj X)
    ((_root_.SerrePositivity.ComplexLimits.normalizedProbeStandardFrame A).obj X) ((complexNormalizedCommonLeft A).app X)

def complexNormalizedCommonRightIndex :
    ULiftHom.{u + 1} (((((_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorHom A).obj (op X)).obj Y).Elements)ᵒᵖ) ⥤
      ULiftHom.{u + 1} (((((_root_.SerrePositivity.ComplexLimits.normalizedProbeHomMiddle A).obj (op X)).obj Y).Elements)ᵒᵖ) :=
  _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.frameSpanSourceIndexMap ((_root_.SerrePositivity.ComplexLimits.normalizedProbeCommonFrame A).obj X)
    ((_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorFrame A).obj X) ((complexNormalizedCommonRight A).app X)

def complexNormalizedCommonRoof :
    nerve (ULiftHom.{u + 1}
      (((((_root_.SerrePositivity.ComplexLimits.normalizedProbeHomMiddle A).obj (op X)).obj Y).Elements)ᵒᵖ)) ⟶
      colimitGraph (HomologicalComplex.quasiIso (ModuleCat A) (ComplexShape.up ℤ))
        ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X) Y := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  exact _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.frameLeftRoofColimitMap (weakEquivalences (Complex A))
    ((_root_.SerrePositivity.ComplexLimits.normalizedProbeCommonFrame A).obj X) ((complexNormalizedCommonAugmentation A).app X)
    (complexNormalizedCommonAugmentation_weak A X)
    (fun f => complexNormalizedCommon_map_weak A X f)

def complexNormalizedTensorRoof :
    nerve (ULiftHom.{u + 1}
      (((((_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorHom A).obj (op X)).obj Y).Elements)ᵒᵖ)) ⟶
      colimitGraph (HomologicalComplex.quasiIso (ModuleCat A) (ComplexShape.up ℤ))
        ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X) Y := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  exact _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.frameLeftRoofColimitMap (weakEquivalences (Complex A))
    ((_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorFrame A).obj X) ((_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorAugmentation A).app X)
    (_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorAugmentation_weak A X)
    (fun f => _root_.SerrePositivity.ComplexLimits.normalizedSimplexTensor_homotopicallyConstant A
      ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X) f)

end SerrePositivity.EInfinity.PowerOperation
