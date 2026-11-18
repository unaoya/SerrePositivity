module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedSimplexTensorFamily
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedSimplexTensorReedy
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.FramedLimitProbeFunctor

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
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomotopicalAlgebra
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.Reedy
variable (A : Type u) [CommRing A]

def normalizedProbeTensorFrame : Complex A ⥤ (SimplexCategory ⥤ Complex A) :=
  _root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A ⋙ _root_.SerrePositivity.ComplexLimits.normalizedSimplexTensorFamily A

def normalizedProbeTensorAugmentation :
    _root_.SerrePositivity.ComplexLimits.normalizedProbeTensorFrame A ⟶ _root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A ⋙ Functor.const SimplexCategory :=
  Functor.whiskerLeft (_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A) (_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensorFamilyAugmentation A)

set_option synthInstance.maxHeartbeats 40000 in
lemma normalizedProbeTensorFrame_cofibrant (X : Complex A) :
    letI := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
    reedyLeft simplex (cofibrations (Complex A))
      (initial.to ((_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorFrame A).obj X)) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  have hc : IsCofibrant ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X) := _root_.SerrePositivity.ComplexLimits.framedLimitProbe_cofibrant A X
  have : Cofibration (0 : (HomologicalComplex.zero : Complex A) ⟶
      (_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X) :=
    (isCofibrant_iff_of_isInitial _ HomologicalComplex.isZero_zero.isInitial).mp hc
  exact _root_.SerrePositivity.ComplexLimits.normalizedSimplexTensor_reedyCofibrant A _
    (mem_cofibrations (0 : (HomologicalComplex.zero : Complex A) ⟶
      (_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X))

lemma normalizedProbeTensorAugmentation_weak (X : Complex A) (n : SimplexCategory) :
    QuasiIso (((_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorAugmentation A).app X).app n) :=
  _root_.SerrePositivity.ComplexLimits.normalizedSimplexTensorAugmentation_quasiIso A _ n

end SerrePositivity.ComplexLimits
