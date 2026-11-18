module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.KProjectiveDerivedSource
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.CofibrantKProjective
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.FramedLimitProbeFunctor
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.SemifreeResolutionValue
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.Resolutions.SemifreeKProjective

/-!
# 同じ probe と半自由標的の K-projective な値

概要：元の cofibrant probe と同じ実半自由分解を K-projective 部分圏で読む。
方針：証明済みの実 cofibrancy と半自由射影性を適用する。
規約：元の複体や分解を選び直さない。
使われ方：正規化テンソル Hom の D(R) 比較への具体的な代入。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomotopicalAlgebra
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

def framedLimitKProjectiveProbe (X : Complex A) : _root_.SerrePositivity.ComplexLimits.KProjectiveComplex A := by
  refine ⟨(_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X, ?_⟩
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  have hc : IsCofibrant ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X) := _root_.SerrePositivity.ComplexLimits.framedLimitProbe_cofibrant A X
  have : Cofibration (0 : (HomologicalComplex.zero : Complex A) ⟶
      (_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X) :=
    (isCofibrant_iff_of_isInitial _ HomologicalComplex.isZero_zero.isInitial).mp hc
  exact _root_.SerrePositivity.ComplexLimits.projectiveCofibrant_isKProjective _
    (mem_cofibrations (0 : (HomologicalComplex.zero : Complex A) ⟶
      (_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X))

def semifreeKProjectiveTarget (Y : Complex A) : _root_.SerrePositivity.ComplexLimits.KProjectiveComplex A :=
  ⟨(_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionValue A Y).val,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexSemifree_isKProjective A (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionValue A Y).property⟩

end SerrePositivity.ComplexLimits
