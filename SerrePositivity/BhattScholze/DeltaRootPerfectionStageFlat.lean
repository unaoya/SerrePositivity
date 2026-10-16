module

public import SerrePositivity.BhattScholze.DeltaRootPerfectionStages
public import SerrePositivity.CommutativeAlgebra.AdicFaithfulDescentAlgebra

/-! # 完全係数環上の実Frobenius各段のp完全忠実平坦性 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open scoped TensorProduct
attribute [local instance] deltaRootPerfectionStageAlgebra adicQuotientAlgebra
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (b : σ → A) (hD : D.IsPerfect)
local notation "P" => MvPolynomial σ A
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => deltaRootRelationFamily (p := p) b
local notation "B" => DeltaAdjoinDivision E (p : P)
  (fun s ↦ DeltaStructure.frobeniusLift E (r s))
local notation "I" => Ideal.span ({(p : A)} : Set A)
local notation "Q" => A ⧸ I
include hD

/-- 完全係数環の実n段の通常剰余テンソルは忠実平坦。 -/
theorem deltaRootPerfectionStage_residueTensor_faithfullyFlat
    (w : Aˣ) (hw : (w : A) = D.delta (p : A)) (n : ℕ) :
    Module.FaithfullyFlat Q (Q ⊗[A] DeltaRootPerfectionStage D b n) := by
  let S := DeltaRootPerfectionStage D b n
  let J := Ideal.map (algebraMap A S) I
  have hJ : J = Ideal.span {(p : S)} := by
    change Ideal.map (algebraMap A S) I = _
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  let eR : S ⧸ J ≃+* (B ⧸ Ideal.span {(p : B)}) :=
    (Ideal.quotEquivOfEq hJ).trans
      (Ideal.quotientEquiv (Ideal.span {(p : B)}) (Ideal.span {(p : S)})
        (ULift.ringEquiv : S ≃+* B).symm
        (by rw [Ideal.map_span, Set.image_singleton, map_natCast])).symm
  have heR (x : S) : eR (Ideal.Quotient.mk J x) =
      Ideal.Quotient.mk (Ideal.span {(p : B)}) x.down := by
    rw [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk, Ideal.quotientEquiv_symm_mk]
    rfl
  let hg := deltaRootSource_ghostMap_injective (σ := σ) hD.p_mul_injective
  let := deltaRootRawModPBaseAlgebra D b hD.p_mul_injective hg w hw
  have : Module.FaithfullyFlat Q (B ⧸ Ideal.span {(p : B)}) :=
    deltaRootRawModP_moduleFaithfullyFlat D b hD.p_mul_injective hg w hw
  let K := ULift.{0} Q
  let eφ : Q ≃+* Q := Ideal.quotientEquiv I I
    (RingEquiv.ofBijective (D.frobeniusLift ^ n) (hD.iterate n))
    (by rw [Ideal.map_span, Set.image_singleton, map_natCast])
  have heφ (a : A) : eφ (Ideal.Quotient.mk I a) =
      Ideal.Quotient.mk I ((DeltaStructure.frobeniusLift D : A → A)^[n] a) := by
    dsimp only [eφ]
    rw [Ideal.quotientEquiv_mk]
    rfl
  let eK : Q ≃+* K := eφ.trans (ULift.ringEquiv : K ≃+* Q).symm
  let : Algebra Q K := eK.toRingHom.toAlgebra
  let : SMul Q K := Algebra.toSMul
  let : Module Q K := Algebra.toModule
  let : Algebra K Q := (ULift.ringEquiv : K ≃+* Q).toRingHom.toAlgebra
  let : SMul K Q := Algebra.toSMul
  let : Module K Q := Algebra.toModule
  let eA : Q ≃ₐ[Q] K := AlgEquiv.ofBijective (Algebra.ofId Q K) eK.bijective
  have : Module.FaithfullyFlat Q K :=
    Module.FaithfullyFlat.of_linearEquiv Q Q eA.symm.toLinearEquiv
  let eKA : K ≃ₐ[K] Q := AlgEquiv.ofBijective (Algebra.ofId K Q) ULift.ringEquiv.bijective
  have : Module.FaithfullyFlat K Q :=
    Module.FaithfullyFlat.of_linearEquiv K K eKA.symm.toLinearEquiv
  let γ := deltaRootRawModPBaseMap D b hD.p_mul_injective hg w hw
  let : Algebra K (B ⧸ Ideal.span {(p : B)}) :=
    (γ.comp (ULift.ringEquiv : K ≃+* Q).toRingHom).toAlgebra
  let : SMul K (B ⧸ Ideal.span {(p : B)}) := Algebra.toSMul
  let : Module K (B ⧸ Ideal.span {(p : B)}) := Algebra.toModule
  let : IsScalarTower K Q (B ⧸ Ideal.span {(p : B)}) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : Module.FaithfullyFlat K (B ⧸ Ideal.span {(p : B)}) :=
    Module.FaithfullyFlat.trans K Q (B ⧸ Ideal.span {(p : B)})
  let : Algebra K (S ⧸ J) :=
    (eR.symm.toRingHom.comp (γ.comp (ULift.ringEquiv : K ≃+* Q).toRingHom)).toAlgebra
  let : SMul K (S ⧸ J) := Algebra.toSMul
  let : Module K (S ⧸ J) := Algebra.toModule
  let eKR : (S ⧸ J) ≃ₐ[K] (B ⧸ Ideal.span {(p : B)}) :=
    { eR with commutes' := by intro k; exact eR.apply_symm_apply _ }
  have : Module.FaithfullyFlat K (S ⧸ J) :=
    Module.FaithfullyFlat.of_linearEquiv K _ eKR.toLinearEquiv
  have hTower : algebraMap Q (S ⧸ J) =
      (algebraMap K (S ⧸ J)).comp (algebraMap Q K) := by
    apply RingHom.ext
    intro a
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    apply eR.injective
    change eR (Ideal.Quotient.mk J (algebraMap A S a)) =
      eR (eR.symm (γ (eφ (Ideal.Quotient.mk I a))))
    rw [RingEquiv.apply_symm_apply, heR]
    change Ideal.Quotient.mk _ ((deltaRootPerfectionStageCoefficientMap D b n a).down) = _
    rw [deltaRootPerfectionStageCoefficientMap_apply, heφ]
    change Ideal.Quotient.mk _ (deltaRootRawCoefficientMap D b
      ((DeltaStructure.frobeniusLift D : A → A)^[n] a)) =
        γ (Ideal.Quotient.mk I ((DeltaStructure.frobeniusLift D : A → A)^[n] a))
    exact (deltaRootRawModPBaseMap_mk D b hD.p_mul_injective hg w hw _).symm
  let : IsScalarTower Q K (S ⧸ J) := IsScalarTower.of_algebraMap_eq' hTower
  have : Module.FaithfullyFlat Q (S ⧸ J) := Module.FaithfullyFlat.trans Q K (S ⧸ J)
  exact Module.FaithfullyFlat.of_linearEquiv Q (S ⧸ J)
    ((quotientTensorReductionEquiv I S).trans (adicReductionEquivAlgebraQuotient I S))

/-- 全実Frobenius段でpは元の係数環のスカラーとして正則。 -/
theorem deltaRootPerfectionStage_p_smul_regular
    (w : Aˣ) (hw : (w : A) = D.delta (p : A)) (n : ℕ) :
    IsSMulRegular (DeltaRootPerfectionStage D b n) (p : A) := by
  intro x y h
  apply ULift.ext
  apply deltaRootFamilyRaw_p_mul_injective_of_p_regular D b hD.p_mul_injective w hw
  simp only [Algebra.smul_def, map_natCast] at h
  exact congrArg ULift.down h

/-- 完全係数環に対し、実Frobenius完全化の全段はp完全忠実平坦。 -/
theorem deltaRootPerfectionStage_isCompletelyFaithfullyFlat
    (w : Aˣ) (hw : (w : A) = D.delta (p : A)) (n : ℕ) :
    IsCompletelyFaithfullyFlat I (DeltaRootPerfectionStage D b n) :=
  isCompletelyFaithfullyFlat_principal_of_regular (p : A) hD.p_mul_injective _
    (deltaRootPerfectionStage_p_smul_regular D b hD w hw n)
    (deltaRootPerfectionStage_residueTensor_faithfullyFlat D b hD w hw n)

end SerrePositivity.BhattScholze
