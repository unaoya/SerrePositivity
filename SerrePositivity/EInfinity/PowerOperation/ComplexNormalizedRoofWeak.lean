module

public import SerrePositivity.EInfinity.PowerOperation.ComplexNormalizedRoofMaps
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.RightFrames
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FibrantSourceReducedFirst
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.WeakAnodyneLocalization

/-!
# 同じ正規化テンソル屋根族の弱同値性

DAG XIII §2.2 の native な降下への前段。標準 frame の指定屋根から共通 frame を
通して、正規化テンソル frame の同じ屋根写像そのものを検証する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory Opposite _root_.HomotopicalAlgebra _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock
open SerrePositivity.DifferentialGraded SerrePositivity.Reedy
open SerrePositivity.HomotopyFunctionComplex _root_.SerrePositivity.ComplexLimits
open SerrePositivity.SimplicialModel
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma complexNormalizedCommonLeftIndex_localized_isIso :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (nerveMap (complexNormalizedCommonLeftIndex A X Y))) := by
  have := _root_.SerrePositivity.ComplexLimits.normalizedProbeStandardHom_kanComplex A (op X) Y
  have := _root_.SerrePositivity.ComplexLimits.normalizedProbeHomMiddle_kanComplex A (op X) Y
  have hw := ulift_homotopyEquivalence
    (_root_.SerrePositivity.ComplexLimits.normalizedProbeHomFromStandard_homotopyEquivalence A (op X) Y)
  exact _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.frameSpanSourceIndexMap_localized_isIso _ _ _
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.anodyneQ_map_isIso_of_weak _ hw.isQCatEquivalence.isWeakHomotopyEquivalence)

lemma complexNormalizedCommonRightIndex_localized_isIso :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (nerveMap (complexNormalizedCommonRightIndex A X Y))) := by
  have := _root_.SerrePositivity.ComplexLimits.normalizedProbeTensorHom_kanComplex A (op X) Y
  have := _root_.SerrePositivity.ComplexLimits.normalizedProbeHomMiddle_kanComplex A (op X) Y
  have hw := ulift_homotopyEquivalence
    (_root_.SerrePositivity.ComplexLimits.normalizedProbeHomFromTensor_homotopyEquivalence A (op X) Y)
  exact _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.frameSpanSourceIndexMap_localized_isIso _ _ _
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.anodyneQ_map_isIso_of_weak _ hw.isQCatEquivalence.isWeakHomotopyEquivalence)

lemma complexNormalizedCommonRoof_left_comparison :
    let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
    let q := (cosimplicialResolutionFamily (_root_.SerrePositivity.ComplexLimits.mappingCofibrantFactorization A)).atObject
      ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X)
    AnodyneHomotopy.anodyneQ.map (nerveMap (complexNormalizedCommonLeftIndex A X Y)) ≫
      AnodyneHomotopy.anodyneQ.map (complexNormalizedCommonRoof A X Y) =
      AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.resolutionLeftRoofColimitMap q Y) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  exact _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.frameLeftRoofColimitMap_comparison _ _ _ (weakEquivalences (Complex A))
    _ _ _ _ (fun f => complexNormalizedCommon_map_weak A X f)
    (fun f => ((cosimplicialResolutionFamily (_root_.SerrePositivity.ComplexLimits.mappingCofibrantFactorization A)).atObject
      ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X)).homotopicallyConstant f)
    (congr_app (complexNormalizedCommonLeft_over A) X)

lemma complexNormalizedCommonRoof_right_comparison :
    AnodyneHomotopy.anodyneQ.map (nerveMap (complexNormalizedCommonRightIndex A X Y)) ≫
      AnodyneHomotopy.anodyneQ.map (complexNormalizedCommonRoof A X Y) =
      AnodyneHomotopy.anodyneQ.map (complexNormalizedTensorRoof A X Y) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  exact _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.frameLeftRoofColimitMap_comparison _ _ _ (weakEquivalences (Complex A))
    _ _ _ _ (fun f => complexNormalizedCommon_map_weak A X f)
    (fun f => _root_.SerrePositivity.ComplexLimits.normalizedSimplexTensor_homotopicallyConstant A
      ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X) f) rfl

lemma complexNormalizedCommonRoof_weak :
    IsWeakHomotopyEquivalence (complexNormalizedCommonRoof A X Y) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  have := BarrattEccles.CarrierDiagram.complex_isFibrant A Y
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.AnodyneWeakDetection.isWeakHomotopyEquivalence
  have := complexNormalizedCommonLeftIndex_localized_isIso A X Y
  have hc : IsIso (AnodyneHomotopy.anodyneQ.map
      (nerveMap (complexNormalizedCommonLeftIndex A X Y)) ≫
      AnodyneHomotopy.anodyneQ.map (complexNormalizedCommonRoof A X Y)) := by
    rw [complexNormalizedCommonRoof_left_comparison]
    exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.anodyneQ_map_isIso_of_weak _
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.resolutionLeftRoofColimitMap_isWeakHomotopyEquivalence_of_first _ Y
        (_root_.SerrePositivity.ComplexLimits.rightFrameFamily A) (_root_.SerrePositivity.ComplexLimits.mappingCofibrantFactorization A))
  exact (isIso_comp_left_iff _ _).mp hc

lemma complexNormalizedTensorRoof_weak :
    IsWeakHomotopyEquivalence (complexNormalizedTensorRoof A X Y) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.AnodyneWeakDetection.isWeakHomotopyEquivalence
  have := complexNormalizedCommonRightIndex_localized_isIso A X Y
  have := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.anodyneQ_map_isIso_of_weak _ (complexNormalizedCommonRoof_weak A X Y)
  rw [← complexNormalizedCommonRoof_right_comparison]
  infer_instance

end SerrePositivity.EInfinity.PowerOperation
