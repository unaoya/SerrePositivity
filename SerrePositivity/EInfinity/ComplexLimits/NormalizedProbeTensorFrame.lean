module

public import SerrePositivity.EInfinity.ComplexLimits.NormalizedSimplexTensorFamily
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedSimplexTensorReedy
public import SerrePositivity.EInfinity.ComplexLimits.FramedLimitProbeFunctor

/-!
# 元の cofibrant probe の正規化テンソル frame

概要：同じ probe を X⊗N(Δ•) へ送り、全自然 augmentation と実 frame 条件を保持する。
方針：元の probe の cofibrancy と構成した実 Reedy cofibrancy を合成。
規約：元の複体の cofibrancy を入力にしない。
使われ方：標準 source frame との共通 Kan Hom 比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory Limits HomotopicalAlgebra
open SerrePositivity.DifferentialGraded SerrePositivity.Reedy
variable (A : Type u) [CommRing A]

def normalizedProbeTensorFrame : Complex A ⥤ (SimplexCategory ⥤ Complex A) :=
  framedLimitProbeFunctor A ⋙ normalizedSimplexTensorFamily A

def normalizedProbeTensorAugmentation :
    normalizedProbeTensorFrame A ⟶ framedLimitProbeFunctor A ⋙ Functor.const SimplexCategory :=
  Functor.whiskerLeft (framedLimitProbeFunctor A) (normalizedSimplexTensorFamilyAugmentation A)

lemma normalizedProbeTensorFrame_cofibrant (X : Complex A) :
    letI := projectiveModelCategory A
    reedyLeft simplex (cofibrations (Complex A))
      (initial.to ((normalizedProbeTensorFrame A).obj X)) := by
  let := projectiveModelCategory A
  have hc : IsCofibrant ((framedLimitProbeFunctor A).obj X) := framedLimitProbe_cofibrant A X
  have : Cofibration (0 : (HomologicalComplex.zero : Complex A) ⟶
      (framedLimitProbeFunctor A).obj X) :=
    (isCofibrant_iff_of_isInitial _ HomologicalComplex.isZero_zero.isInitial).mp hc
  exact normalizedSimplexTensor_reedyCofibrant A _
    (mem_cofibrations (0 : (HomologicalComplex.zero : Complex A) ⟶
      (framedLimitProbeFunctor A).obj X))

lemma normalizedProbeTensorAugmentation_weak (X : Complex A) (n : SimplexCategory) :
    QuasiIso (((normalizedProbeTensorAugmentation A).app X).app n) :=
  normalizedSimplexTensorAugmentation_quasiIso A _ n

end SerrePositivity.EInfinity.ComplexLimits
