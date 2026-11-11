module

public import SerrePositivity.EInfinity.ComplexLimits.NormalizedProbeHomFrames
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.FixedQuillenFrameComparison
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
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.Reedy
open SerrePositivity.DifferentialGraded SerrePositivity.HomotopyFunctionComplex
open SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

lemma normalizedProbeHomFromStandard_homotopyEquivalence (X : (Complex A)ᵒᵖ) (Y : Complex A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (((normalizedProbeHomFromStandard A).app X).app Y) := by
  let := projectiveModelCategory A
  have := BarrattEccles.CarrierDiagram.complex_isFibrant A Y
  exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.fixedFrameOverFunctor_homLeft_homotopyEquivalence (mappingCofibrantFactorization A)
    (cosimplicialResolutionFamily (mappingCofibrantFactorization A)) (framedLimitProbeFunctor A)
    (normalizedProbeTensorFrame A) (normalizedProbeTensorAugmentation A)
    (normalizedProbeTensorAugmentation_weak A) X Y

lemma normalizedProbeHomFromTensor_homotopyEquivalence (X : (Complex A)ᵒᵖ) (Y : Complex A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (((normalizedProbeHomFromTensor A).app X).app Y) := by
  let := projectiveModelCategory A
  have := BarrattEccles.CarrierDiagram.complex_isFibrant A Y
  exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.fixedFrameOverFunctor_homRight_homotopyEquivalence (mappingCofibrantFactorization A)
    (cosimplicialResolutionFamily (mappingCofibrantFactorization A)) (framedLimitProbeFunctor A)
    (normalizedProbeTensorFrame A) (normalizedProbeTensorAugmentation A)
    (normalizedProbeTensorAugmentation_weak A) (normalizedProbeTensorFrame_cofibrant A)
    (fun X _ _ f => normalizedSimplexTensor_homotopicallyConstant A
      ((framedLimitProbeFunctor A).obj X) f) X Y

def normalizedProbeHomDoldKanIso (X Y : Complex A) :
    ((normalizedProbeTensorHom A).obj (Opposite.op X)).obj Y ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanHomSpace (R := A) (D := Complex A)
        ((framedLimitProbeFunctor A).obj X) Y :=
  normalizedSimplexTensorHomIso A _ Y

end SerrePositivity.EInfinity.ComplexLimits
