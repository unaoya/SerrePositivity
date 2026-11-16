module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletedAlgebraH0

/-!
# 元の主元完備化の係数単位

## 概要
元の係数線形な主元完備化のH⁰比較は、同じ係数の像を保つ。

## 方針
既存の係数代数同値の可換性を適用する。

## 規約
自然数の座標に限らず、元の指定した主元を使う。

## 使われ方
二座標完備テンソル積の第二の完備化単位を照合する。
-/

public noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]

/-- 元の主元完備化比較は、元の同じ係数の単位を保つ。 -/
theorem principalCompletionCoefficientUnit (a : R) (b : B) :
    letI := derivedH0CommRing (completedAlgebra R a B)
    letI := derivedH0Algebra (completedAlgebra R a B)
    letI := completedAlgebraScalarAlgebra R a B
    letI := principalCompletionCommRing B (algebraMap R B a)
    letI := principalCompletionAlgebra B (algebraMap R B a)
    completedAlgebraPrincipalH0AlgEquiv R a B (completedAlgebraUnitAlgHom R a B b) =
      principalCompletionUnitRingHom B (algebraMap R B a) b := by
  let := derivedH0CommRing (completedAlgebra R a B)
  let := derivedH0Algebra (completedAlgebra R a B)
  let := completedAlgebraScalarAlgebra R a B
  let := principalCompletionCommRing B (algebraMap R B a)
  let := principalCompletionAlgebra B (algebraMap R B a)
  exact (completedAlgebraPrincipalH0AlgEquiv R a B).commutes b

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
