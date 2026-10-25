module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.DeltaRoot.DeltaRootFamilyRegularGhost
public import SerrePositivity.CommutativeAlgebra.CompletelyFlatCriterion

/-! # 任意根族の実raw p除算包のp完全忠実平坦性 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open scoped TensorProduct
attribute [local instance] deltaRootRawCoefficientAlgebra
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (b : σ → A)
local notation "P" => MvPolynomial σ A
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => deltaRootRelationFamily (p := p) b
local notation "B" =>
  DeltaAdjoinDivision E (p : P) (fun s ↦ DeltaStructure.frobeniusLift E (r s))
local notation "I" => Ideal.span {(p : A)}
local notation "QA" => A ⧸ I

/-- G4でghost単射を供給した通常剰余テンソルの忠実平坦性。 -/
theorem deltaRootFamilyRaw_residueTensor_faithfullyFlat
    (hpA : Function.Injective (fun z : A => (p : A) * z))
    (w : Aˣ) (hw : (w : A) = D.delta (p : A)) :
    Module.FaithfullyFlat QA (QA ⊗[A] B) := by
  let hg := deltaRootSource_ghostMap_injective (σ := σ) hpA
  let := deltaRootRawModPBaseAlgebra D b hpA hg w hw
  have := deltaRootRawModP_moduleFaithfullyFlat D b hpA hg w hw
  exact Module.FaithfullyFlat.of_linearEquiv QA (B ⧸ Ideal.span {(p : B)})
    (deltaRootRawBaseChangeModPAlgEquiv D b hpA hg w hw).toLinearEquiv

/-- 実raw包のp正則性を、元のAの標準係数スカラーについて表す。 -/
theorem deltaRootFamilyRaw_p_smul_regular
    (hpA : Function.Injective (fun z : A => (p : A) * z))
    (w : Aˣ) (hw : (w : A) = D.delta (p : A)) :
    IsSMulRegular B (p : A) := by
  intro x y h
  apply deltaRootFamilyRaw_p_mul_injective_of_p_regular D b hpA w hw
  simp only [Algebra.smul_def, map_natCast] at h
  exact h

/-- 任意根族の実係数射A→Bは、G3によりp完全忠実平坦。 -/
theorem deltaRootFamilyRaw_isCompletelyFaithfullyFlat
    (hpA : Function.Injective (fun z : A => (p : A) * z))
    (w : Aˣ) (hw : (w : A) = D.delta (p : A)) :
    IsCompletelyFaithfullyFlat I B :=
  isCompletelyFaithfullyFlat_principal_of_regular (p : A) hpA B
    (deltaRootFamilyRaw_p_smul_regular D b hpA w hw)
    (deltaRootFamilyRaw_residueTensor_faithfullyFlat D b hpA w hw)

end SerrePositivity.BhattScholze
