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
open SerrePositivity.EInfinity.ComplexLimits
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (colimitGraph)
variable (A : Type u) [CommRing A] (X Y : Complex A)

def complexNormalizedCommonLeftIndex :
    ULiftHom.{u + 1} (((((normalizedProbeStandardHom A).obj (op X)).obj Y).Elements)ᵒᵖ) ⥤
      ULiftHom.{u + 1} (((((normalizedProbeHomMiddle A).obj (op X)).obj Y).Elements)ᵒᵖ) :=
  _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.frameSpanSourceIndexMap ((normalizedProbeCommonFrame A).obj X)
    ((normalizedProbeStandardFrame A).obj X) ((complexNormalizedCommonLeft A).app X)

def complexNormalizedCommonRightIndex :
    ULiftHom.{u + 1} (((((normalizedProbeTensorHom A).obj (op X)).obj Y).Elements)ᵒᵖ) ⥤
      ULiftHom.{u + 1} (((((normalizedProbeHomMiddle A).obj (op X)).obj Y).Elements)ᵒᵖ) :=
  _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.frameSpanSourceIndexMap ((normalizedProbeCommonFrame A).obj X)
    ((normalizedProbeTensorFrame A).obj X) ((complexNormalizedCommonRight A).app X)

def complexNormalizedCommonRoof :
    nerve (ULiftHom.{u + 1}
      (((((normalizedProbeHomMiddle A).obj (op X)).obj Y).Elements)ᵒᵖ)) ⟶
      colimitGraph (HomologicalComplex.quasiIso (ModuleCat A) (ComplexShape.up ℤ))
        ((framedLimitProbeFunctor A).obj X) Y := by
  let := projectiveModelCategory A
  exact _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.frameLeftRoofColimitMap (weakEquivalences (Complex A))
    ((normalizedProbeCommonFrame A).obj X) ((complexNormalizedCommonAugmentation A).app X)
    (complexNormalizedCommonAugmentation_weak A X)
    (fun f => complexNormalizedCommon_map_weak A X f)

def complexNormalizedTensorRoof :
    nerve (ULiftHom.{u + 1}
      (((((normalizedProbeTensorHom A).obj (op X)).obj Y).Elements)ᵒᵖ)) ⟶
      colimitGraph (HomologicalComplex.quasiIso (ModuleCat A) (ComplexShape.up ℤ))
        ((framedLimitProbeFunctor A).obj X) Y := by
  let := projectiveModelCategory A
  exact _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.frameLeftRoofColimitMap (weakEquivalences (Complex A))
    ((normalizedProbeTensorFrame A).obj X) ((normalizedProbeTensorAugmentation A).app X)
    (normalizedProbeTensorAugmentation_weak A X)
    (fun f => normalizedSimplexTensor_homotopicallyConstant A
      ((framedLimitProbeFunctor A).obj X) f)

end SerrePositivity.EInfinity.PowerOperation
