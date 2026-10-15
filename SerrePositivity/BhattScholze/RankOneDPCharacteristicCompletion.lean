module

public import SerrePositivity.BhattScholze.RankOneDPEvaluatedDerivedFlat
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ComplexCompletionReconstruction

/-! # 標数pの実分冪導来拡大と実導来完備化

既存の標準完備化単位を使用する。混標数の古典的完備化への置換は含めない。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} {A : Type u} [CommRing A]
local notation "P₀" => Polynomial A
local notation "G₀" => DividedPowerAlgebra A A

/-- 標数pでは、P→Γへの任意の上有界実導来係数拡大は既に実導来p完備。 -/
theorem rankOneDPDerived_isComplete (hp : (p : A) = 0)
    (X : DerivedCategory.Minus (ModuleCat.{u} P₀)) :
    DerivedCompletion.IsComplete G₀ (p : G₀)
      (((boundedAboveDerivedBaseChange (rankOneDPPolynomialMap A).toRingHom).obj X).obj) := by
  have hpG : (p : G₀) = 0 := by
    rw [← map_natCast (algebraMap A G₀), hp, map_zero]
  apply DerivedCompletion.isComplete_of_scalar_pow_zero G₀ (p : G₀) _ 1
  rw [pow_one, hpG, zero_smul]

/-- 実導来p完備化は、標準完備化単位の逆により元の分冪導来拡大と同定される。 -/
def rankOneDPCharacteristicCompletionIso (hp : (p : A) = 0)
    (X : DerivedCategory.Minus (ModuleCat.{u} P₀)) :
    (DerivedCompletion.derivedComplexCompletionFunctor G₀ (p : G₀)).obj
        (((boundedAboveDerivedBaseChange (rankOneDPPolynomialMap A).toRingHom).obj X).obj) ≅
      (((boundedAboveDerivedBaseChange (rankOneDPPolynomialMap A).toRingHom).obj X).obj) :=
  (DerivedCompletion.derivedComplexCompletionUnitIso G₀ (p : G₀) _
    (rankOneDPDerived_isComplete hp X)).symm

/-- 標準完備化比較は、実導来ホモロジーの各次数を保つ。 -/
def rankOneDPCharacteristicCompletionHomologyIso (hp : (p : A) = 0)
    (X : DerivedCategory.Minus (ModuleCat.{u} P₀)) (n : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} G₀) n).obj
        ((DerivedCompletion.derivedComplexCompletionFunctor G₀ (p : G₀)).obj
          (((boundedAboveDerivedBaseChange (rankOneDPPolynomialMap A).toRingHom).obj X).obj)) ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{u} G₀) n).obj
        (((boundedAboveDerivedBaseChange (rankOneDPPolynomialMap A).toRingHom).obj X).obj) :=
  (DerivedCategory.homologyFunctor _ n).mapIso (rankOneDPCharacteristicCompletionIso hp X)

/-- 実導来p完備化後も、各ホモロジーの零性は実X^p Koszulホモロジーで判定できる。 -/
theorem rankOneDPCharacteristicCompletionHomology_isZero_iff
    (hprime : p.Prime) (hp : (p : A) = 0)
    (X : DerivedCategory.Minus (ModuleCat.{u} P₀)) (n : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} G₀) n).obj
      ((DerivedCompletion.derivedComplexCompletionFunctor G₀ (p : G₀)).obj
        (((boundedAboveDerivedBaseChange (rankOneDPPolynomialMap A).toRingHom).obj X).obj))) ↔
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} P₀) n).obj
      ((DerivedCompletion.derivedScalarConeFunctor P₀ ((Polynomial.X : P₀) ^ p)).obj X.obj)) :=
  (rankOneDPCharacteristicCompletionHomologyIso hp X n).isZero_iff.trans
    (rankOneDPDerivedKoszulHomology_isZero_iff hprime hp X n)

/-- 実導来p完備化後の各ホモロジーのA平坦性も、実KoszulホモロジーのA平坦性と同値。 -/
theorem rankOneDPCharacteristicCompletionHomology_flat_iff
    (hprime : p.Prime) (hp : (p : A) = 0)
    (X : DerivedCategory.Minus (ModuleCat.{u} P₀)) (n : ℤ) :
    Module.Flat A ((ModuleCat.restrictScalars (algebraMap A G₀)).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} G₀) n).obj
        ((DerivedCompletion.derivedComplexCompletionFunctor G₀ (p : G₀)).obj
          (((boundedAboveDerivedBaseChange (rankOneDPPolynomialMap A).toRingHom).obj X).obj)))) ↔
    Module.Flat A ((ModuleCat.restrictScalars (algebraMap A P₀)).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} P₀) n).obj
        ((DerivedCompletion.derivedScalarConeFunctor P₀ ((Polynomial.X : P₀) ^ p)).obj X.obj))) :=
  (Module.Flat.equiv_iff (((ModuleCat.restrictScalars (algebraMap A G₀)).mapIso
    (rankOneDPCharacteristicCompletionHomologyIso hp X n)).toLinearEquiv)).trans
    (rankOneDPDerivedKoszulHomology_flat_iff hprime hp X n)

/-- 具体的評価代数のKoszul消滅の下、実導来p完備化も通常評価環の次数零対象と一致する。 -/
def rankOneDPEvaluatedCompletedOrdinaryIso {B : Type u} [CommRing B] [Algebra A B]
    (hprime : p.Prime) (hp : (p : A) = 0) (y : B)
    (hK : letI := rankOneDPEvaluationAlgebra (A := A) y
      ∀ n : ℕ, 0 < n → IsZero
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} P₀) (-(n : ℤ))).obj
          ((DerivedCompletion.derivedScalarConeFunctor P₀ ((Polynomial.X : P₀) ^ p)).obj
            (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of P₀ B)).obj))) :
    letI := rankOneDPEvaluationAlgebra (A := A) y
    (DerivedCompletion.derivedComplexCompletionFunctor G₀ (p : G₀)).obj
        (((boundedAboveDerivedBaseChange (rankOneDPPolynomialMap A).toRingHom).obj
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of P₀ B))).obj) ≅
      (boundedAboveDerivedSingleFunctor.obj
        (ModuleCat.of G₀ (RankOneDPEvaluatedEnvelope A B y))).obj := by
  let := rankOneDPEvaluationAlgebra (A := A) y
  exact rankOneDPCharacteristicCompletionIso hp _ ≪≫
    DerivedCategory.Minus.ι.mapIso (rankOneDPEvaluatedDerivedOrdinaryIso hprime hp y hK)

end SerrePositivity.BhattScholze
