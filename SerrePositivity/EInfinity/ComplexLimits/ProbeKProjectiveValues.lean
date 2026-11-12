module

public import SerrePositivity.EInfinity.ComplexLimits.KProjectiveDerivedSource
public import SerrePositivity.EInfinity.ComplexLimits.CofibrantKProjective
public import SerrePositivity.EInfinity.ComplexLimits.FramedLimitProbeFunctor
public import SerrePositivity.EInfinity.ComplexLimits.SemifreeResolutionValue
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeKProjective

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
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory Limits HomotopicalAlgebra
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

def framedLimitKProjectiveProbe (X : Complex A) : KProjectiveComplex A := by
  refine ⟨(framedLimitProbeFunctor A).obj X, ?_⟩
  let := projectiveModelCategory A
  have hc : IsCofibrant ((framedLimitProbeFunctor A).obj X) := framedLimitProbe_cofibrant A X
  have : Cofibration (0 : (HomologicalComplex.zero : Complex A) ⟶
      (framedLimitProbeFunctor A).obj X) :=
    (isCofibrant_iff_of_isInitial _ HomologicalComplex.isZero_zero.isInitial).mp hc
  exact projectiveCofibrant_isKProjective _
    (mem_cofibrations (0 : (HomologicalComplex.zero : Complex A) ⟶
      (framedLimitProbeFunctor A).obj X))

def semifreeKProjectiveTarget (Y : Complex A) : KProjectiveComplex A :=
  ⟨(complexSemifreeResolutionValue A Y).val,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexSemifree_isKProjective A (complexSemifreeResolutionValue A Y).property⟩

end SerrePositivity.EInfinity.ComplexLimits
