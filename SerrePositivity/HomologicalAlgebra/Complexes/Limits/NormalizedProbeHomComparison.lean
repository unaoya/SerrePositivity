module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedProbeHomFrames
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Frames.FixedQuillenFrameComparison
public import SerrePositivity.EInfinity.BarrattEccles.CarrierDiagramModel

/-!
# 元の標準 frame と正規化テンソル Hom の実高次比較

概要：元の二つの全自然 Hom 比較射は同じ共通 Hom へのホモトピー同値。
方針：実 frame 条件と同じ augmentation を固定 Quillen 比較へ渡す。
規約：単体集合のモデル構造を入力にしない。
使われ方：元の DK Hom・標準 source frame・写像空間の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.HomotopicalAlgebra
open _root_.SerrePositivity.Reedy
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.HomotopyFunctionComplex
open _root_.SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

lemma normalizedProbeHomFromStandard_homotopyEquivalence (X : (Complex A)ᵒᵖ) (Y : Complex A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (((_root_.SerrePositivity.ComplexLimits.normalizedProbeHomFromStandard A).app X).app Y) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  have := _root_.SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.complex_isFibrant A Y
  exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.fixedFrameOverFunctor_homLeft_homotopyEquivalence (_root_.SerrePositivity.ComplexLimits.mappingCofibrantFactorization A)
    (cosimplicialResolutionFamily (_root_.SerrePositivity.ComplexLimits.mappingCofibrantFactorization A)) (_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A)
    (_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorFrame A) (_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorAugmentation A)
    (_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorAugmentation_weak A) X Y

lemma normalizedProbeHomFromTensor_homotopyEquivalence (X : (Complex A)ᵒᵖ) (Y : Complex A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (((_root_.SerrePositivity.ComplexLimits.normalizedProbeHomFromTensor A).app X).app Y) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  have := _root_.SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.complex_isFibrant A Y
  exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.fixedFrameOverFunctor_homRight_homotopyEquivalence (_root_.SerrePositivity.ComplexLimits.mappingCofibrantFactorization A)
    (cosimplicialResolutionFamily (_root_.SerrePositivity.ComplexLimits.mappingCofibrantFactorization A)) (_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A)
    (_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorFrame A) (_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorAugmentation A)
    (_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorAugmentation_weak A) (_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorFrame_cofibrant A)
    (fun X _ _ f => _root_.SerrePositivity.ComplexLimits.normalizedSimplexTensor_homotopicallyConstant A
      ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X) f) X Y

def normalizedProbeHomDoldKanIso (X Y : Complex A) :
    ((_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorHom A).obj (Opposite.op X)).obj Y ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanHomSpace (R := A) (D := Complex A)
        ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X) Y :=
  _root_.SerrePositivity.ComplexLimits.normalizedSimplexTensorHomIso A _ Y

end SerrePositivity.ComplexLimits
