module

public import SerrePositivity.EInfinity.PowerOperation.ComplexNormalizedRoofMaps
public import SerrePositivity.EInfinity.ComplexLimits.RightFrames
public import SerrePositivity.EInfinity.FrameHom.FibrantSourceReducedFirst
public import SerrePositivity.EInfinity.Hammock.WeakAnodyneLocalization

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
open CategoryTheory Opposite HomotopicalAlgebra Hammock
open SerrePositivity.DifferentialGraded SerrePositivity.Reedy
open SerrePositivity.HomotopyFunctionComplex SerrePositivity.EInfinity.ComplexLimits
open SerrePositivity.SimplicialModel
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma complexNormalizedCommonLeftIndex_localized_isIso :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (nerveMap (complexNormalizedCommonLeftIndex A X Y))) := by
  have := normalizedProbeStandardHom_kanComplex A (op X) Y
  have := normalizedProbeHomMiddle_kanComplex A (op X) Y
  have hw := ulift_homotopyEquivalence
    (normalizedProbeHomFromStandard_homotopyEquivalence A (op X) Y)
  exact FrameHom.frameSpanSourceIndexMap_localized_isIso _ _ _
    (anodyneQ_map_isIso_of_weak _ hw.isQCatEquivalence.isWeakHomotopyEquivalence)

lemma complexNormalizedCommonRightIndex_localized_isIso :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (nerveMap (complexNormalizedCommonRightIndex A X Y))) := by
  have := normalizedProbeTensorHom_kanComplex A (op X) Y
  have := normalizedProbeHomMiddle_kanComplex A (op X) Y
  have hw := ulift_homotopyEquivalence
    (normalizedProbeHomFromTensor_homotopyEquivalence A (op X) Y)
  exact FrameHom.frameSpanSourceIndexMap_localized_isIso _ _ _
    (anodyneQ_map_isIso_of_weak _ hw.isQCatEquivalence.isWeakHomotopyEquivalence)

lemma complexNormalizedCommonRoof_left_comparison :
    let := projectiveModelCategory A
    let q := (cosimplicialResolutionFamily (mappingCofibrantFactorization A)).atObject
      ((framedLimitProbeFunctor A).obj X)
    AnodyneHomotopy.anodyneQ.map (nerveMap (complexNormalizedCommonLeftIndex A X Y)) ≫
      AnodyneHomotopy.anodyneQ.map (complexNormalizedCommonRoof A X Y) =
      AnodyneHomotopy.anodyneQ.map (FrameHom.resolutionLeftRoofColimitMap q Y) := by
  let := projectiveModelCategory A
  exact FrameHom.frameLeftRoofColimitMap_comparison _ _ _ (weakEquivalences (Complex A))
    _ _ _ _ (fun f => complexNormalizedCommon_map_weak A X f)
    (fun f => ((cosimplicialResolutionFamily (mappingCofibrantFactorization A)).atObject
      ((framedLimitProbeFunctor A).obj X)).homotopicallyConstant f)
    (congr_app (complexNormalizedCommonLeft_over A) X)

lemma complexNormalizedCommonRoof_right_comparison :
    AnodyneHomotopy.anodyneQ.map (nerveMap (complexNormalizedCommonRightIndex A X Y)) ≫
      AnodyneHomotopy.anodyneQ.map (complexNormalizedCommonRoof A X Y) =
      AnodyneHomotopy.anodyneQ.map (complexNormalizedTensorRoof A X Y) := by
  let := projectiveModelCategory A
  exact FrameHom.frameLeftRoofColimitMap_comparison _ _ _ (weakEquivalences (Complex A))
    _ _ _ _ (fun f => complexNormalizedCommon_map_weak A X f)
    (fun f => normalizedSimplexTensor_homotopicallyConstant A
      ((framedLimitProbeFunctor A).obj X) f) rfl

lemma complexNormalizedCommonRoof_weak :
    IsWeakHomotopyEquivalence (complexNormalizedCommonRoof A X Y) := by
  let := projectiveModelCategory A
  have := BarrattEccles.CarrierDiagram.complex_isFibrant A Y
  apply FrameHom.AnodyneWeakDetection.isWeakHomotopyEquivalence
  have := complexNormalizedCommonLeftIndex_localized_isIso A X Y
  have hc : IsIso (AnodyneHomotopy.anodyneQ.map
      (nerveMap (complexNormalizedCommonLeftIndex A X Y)) ≫
      AnodyneHomotopy.anodyneQ.map (complexNormalizedCommonRoof A X Y)) := by
    rw [complexNormalizedCommonRoof_left_comparison]
    exact anodyneQ_map_isIso_of_weak _
      (FrameHom.resolutionLeftRoofColimitMap_isWeakHomotopyEquivalence_of_first _ Y
        (rightFrameFamily A) (mappingCofibrantFactorization A))
  exact (isIso_comp_left_iff _ _).mp hc

lemma complexNormalizedTensorRoof_weak :
    IsWeakHomotopyEquivalence (complexNormalizedTensorRoof A X Y) := by
  apply FrameHom.AnodyneWeakDetection.isWeakHomotopyEquivalence
  have := complexNormalizedCommonRightIndex_localized_isIso A X Y
  have := anodyneQ_map_isIso_of_weak _ (complexNormalizedCommonRoof_weak A X Y)
  rw [← complexNormalizedCommonRoof_right_comparison]
  infer_instance

end SerrePositivity.EInfinity.PowerOperation
