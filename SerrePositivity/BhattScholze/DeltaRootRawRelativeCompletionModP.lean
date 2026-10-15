module

public import SerrePositivity.BhattScholze.DeltaRootRawRelativeDerivedModP
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionQuotient

/-! # 元のA上の根関係raw包の実導来完備化とmod p比較 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard deltaRootRawCoefficientAlgebra
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (b : σ → A)
local notation "P" => MvPolynomial σ A
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "inputs" =>
  fun s ↦ DeltaStructure.frobeniusLift E (deltaRootRelationFamily (p := p) b s)
local notation "B" => DeltaAdjoinDivision E (p : P) inputs
local notation "QA" => A ⧸ Ideal.span {(p : A)}
local notation "qA" => Ideal.Quotient.mk (Ideal.span {(p : A)})

/-- 元のAがp正則なら、raw包の標準A導来完備化単位を実p還元した射は同型。 -/
theorem deltaRootRawRelativeCompletionUnit_modP_isIso
    (hpA : Function.Injective (fun x : A ↦ (p : A) * x)) :
    IsIso ((boundedAboveDerivedBaseChange qA).map
      ((DerivedCompletion.boundedAboveDerivedCompletionUnit A (p : A)).app
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A B)))) := by
  let X := boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A B)
  have hr : IsSMulRegular A (p : A) := hpA
  let F (x : A) := IsIso ((boundedAboveDerivedBaseChange
    (Ideal.Quotient.mk (Ideal.span {x}))).map
      ((DerivedCompletion.boundedAboveDerivedCompletionUnit A (p : A)).app X))
  have h : F ((p : A) ^ 1) :=
    DerivedCompletion.boundedAboveDerivedCompletion_quotient_unit_isIso A (p : A) hr 1 X
  exact Eq.mp (congrArg F (_root_.pow_one (p : A))) h

/-- 元のA上の実導来完備化を実p還元すると、標準A/p作用付きの実raw包/pとなる。 -/
def deltaRootRawRelativeCompletedDerivedModPIso
    (hpA : Function.Injective (fun x : A ↦ (p : A) * x))
    (hpB : Function.Injective (fun x : B ↦ (p : B) * x))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := MvPolynomial σ A) σ) →
        ℕ → RelativeFreeDeltaRing (R := MvPolynomial σ A) σ))
    (w : Aˣ) (hw : (w : A) = D.delta (p : A)) :
    letI := deltaRootRawModPBaseAlgebra D b hpA hg w hw
    (boundedAboveDerivedBaseChange qA).obj
        ((DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)).obj
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A B))) ≅
      boundedAboveDerivedSingleFunctor.obj (ModuleCat.of QA (B ⧸ Ideal.span {(p : B)})) := by
  let := deltaRootRawModPBaseAlgebra D b hpA hg w hw
  let X := boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A B)
  have := deltaRootRawRelativeCompletionUnit_modP_isIso D b hpA
  exact (asIso ((boundedAboveDerivedBaseChange qA).map
      ((DerivedCompletion.boundedAboveDerivedCompletionUnit A (p : A)).app X))).symm ≪≫
    deltaRootRawRelativeDerivedModPIso D b hpA hpB hg w hw

/-- 実mod p比較は元のA上の実導来完備化標準単位と両立する。 -/
theorem deltaRootRawRelativeCompletedDerivedModPIso_unit
    (hpA : Function.Injective (fun x : A ↦ (p : A) * x))
    (hpB : Function.Injective (fun x : B ↦ (p : B) * x))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := MvPolynomial σ A) σ) →
        ℕ → RelativeFreeDeltaRing (R := MvPolynomial σ A) σ))
    (w : Aˣ) (hw : (w : A) = D.delta (p : A)) :
    letI := deltaRootRawModPBaseAlgebra D b hpA hg w hw
    (boundedAboveDerivedBaseChange qA).map
        ((DerivedCompletion.boundedAboveDerivedCompletionUnit A (p : A)).app
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A B))) ≫
      (deltaRootRawRelativeCompletedDerivedModPIso D b hpA hpB hg w hw).hom =
        (deltaRootRawRelativeDerivedModPIso D b hpA hpB hg w hw).hom := by
  let := deltaRootRawModPBaseAlgebra D b hpA hg w hw
  let X := boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A B)
  let f := (boundedAboveDerivedBaseChange qA).map
    ((DerivedCompletion.boundedAboveDerivedCompletionUnit A (p : A)).app X)
  have := deltaRootRawRelativeCompletionUnit_modP_isIso D b hpA
  change (asIso f).hom ≫ ((asIso f).symm ≪≫
    deltaRootRawRelativeDerivedModPIso D b hpA hpB hg w hw).hom = _
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]

end SerrePositivity.BhattScholze
