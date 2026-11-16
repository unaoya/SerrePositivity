module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.PrincipalCompletionCoefficientUnit

/-!
# 係数代数の完備化単位の元のH⁰写像

## 概要
係数代数の単位の台の関数を、元の標準完備化単位で計算する。

## 方針
元の代数単位の台の写像の法則を使う。

## 規約
標準単位を変更しない。

## 使われ方
二回完備化のH⁰同型の単位の正規化。
-/

public noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 係数代数の元の単位の関数は、標準H⁰同型で戻した元の完備化単位そのもの。 -/
theorem completedAlgebraUnitAlgHom_homology (a : R) (b : B) :
    letI := derivedH0CommRing (completedAlgebra R a B)
    letI := derivedH0Algebra (completedAlgebra R a B)
    completedAlgebraUnitAlgHom R a B b =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map
        ((derivedComplexCompletionUnit R a).app
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R B)))
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) 0).inv.app
          (ModuleCat.of R B) b) := by
  let := derivedH0CommRing (completedAlgebra R a B)
  let := derivedH0Algebra (completedAlgebra R a B)
  rw [completedAlgebraUnitAlgHom_apply]
  have h := derivedH0AlgMap_apply
    (boundedAboveCompletionAlgebraUnit R a (boundedAboveDerivedAlgebra (R := R) B))
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) 0).inv.app
      (ModuleCat.of R B) b)
  rw [boundedAboveCompletionAlgebraUnit_hom] at h
  exact h


end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
