module

public import SerrePositivity.BhattScholze.Andre.RootedExtension.Supplement.DeltaRoot.DeltaRootPerfectionFaithful
public import SerrePositivity.BhattScholze.Prism.Perfection.PCompletedDeltaPerfection
public import SerrePositivity.CommutativeAlgebra.AdicCompletionOpenQuotient

/-! # 既存p進完備δ完全化への実係数射のp完全忠実平坦性 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open scoped TensorProduct
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (b : σ → A)
local notation "P" => MvPolynomial σ A
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => deltaRootRelationFamily (p := p) b
local notation "F" => deltaAdjoinDivisionStructure E (p : P)
  (fun s ↦ DeltaStructure.frobeniusLift E (r s))
local notation "C" => DeltaPerfection F
local notation "Z" => PCompletedDeltaPerfection F
local notation "I" => Ideal.span ({(p : A)} : Set A)
local notation "J" => Ideal.span ({(p : C)} : Set C)
local notation "Q" => A ⧸ I

/-- 既存完備化の、完備化前の実δ完全化に関する標準代数構造。 -/
abbrev deltaRootPCompletedPerfectionOverPerfection : Algebra C Z :=
  inferInstanceAs (Algebra C (AdicCompletion J C))

/-- 元のraw係数射と既存のp進完備δ完全化標準射の合成。 -/
def deltaRootPCompletedPerfectionCoefficientMap : A →+* Z :=
  (pCompletedDeltaPerfectionMap F).comp (deltaRootRawCoefficientMap D b)

/-- p進完備δ完全化の実A係数作用。 -/
abbrev deltaRootPCompletedPerfectionAlgebra : Algebra A Z :=
  (deltaRootPCompletedPerfectionCoefficientMap D b).toAlgebra

attribute [local instance] deltaRootPerfectionAlgebra deltaRootPCompletedPerfectionAlgebra
  adicQuotientAlgebra deltaRootPCompletedPerfectionOverPerfection
local notation "Kc" => Ideal.map (algebraMap A C) I
local notation "Kz" => Ideal.map (algebraMap A Z) I

/-- 実係数作用は、完備化前の係数射と標準完備化射の合成。 -/
theorem deltaRootPCompletedPerfectionCoefficientMap_comp :
    deltaRootPCompletedPerfectionCoefficientMap D b =
      (algebraMap C Z).comp (deltaRootPerfectionCoefficientMap D b) := rfl

/-- 正確なA係数のp商を、完備化前後で比較する実環同型。 -/
def deltaRootPCompletedPerfectionResidueEquiv : Z ⧸ Kz ≃+* C ⧸ Kc := by
  have hc : Kc = J := by rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have hz : Kz = Ideal.map (algebraMap C Z) J := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast,
      Ideal.map_span, Set.image_singleton, map_natCast]
  exact (Ideal.quotEquivOfEq hz).trans
    ((adicCompletionOpenQuotientEquiv J J 1 (by simp)
      (Submodule.fg_span (Set.toFinite _))).toRingEquiv.trans (Ideal.quotEquivOfEq hc.symm))

/-- 実剰余同型は、元の完備化前の標準係数像を保つ。 -/
theorem deltaRootPCompletedPerfectionResidueEquiv_mk (c : C) :
    deltaRootPCompletedPerfectionResidueEquiv D b
      (Ideal.Quotient.mk Kz (algebraMap C Z c)) = Ideal.Quotient.mk Kc c := by
  unfold deltaRootPCompletedPerfectionResidueEquiv
  rw [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk, RingEquiv.trans_apply]
  change Ideal.quotEquivOfEq _
    (adicCompletionOpenQuotientMap J J 1 (by simp) (algebraMap C Z c)) = _
  rw [adicCompletionOpenQuotientMap_algebraMap, Ideal.quotEquivOfEq_mk]

local instance deltaRootPCompletedPerfectionResidueAlgebra : Algebra Q (Z ⧸ Kz) :=
  adicQuotientAlgebra I Z
local instance deltaRootPerfectionActualResidueAlgebra : Algebra Q (C ⧸ Kc) :=
  adicQuotientAlgebra I C

local instance deltaRootPCompletedPerfectionResidueModule : Module Q (Z ⧸ Kz) := Algebra.toModule
local instance deltaRootPerfectionActualResidueModule : Module Q (C ⧸ Kc) := Algebra.toModule

set_option maxHeartbeats 800000 in
-- Check the two completion quotient scalar structures against the concrete ring comparison.
/-- 剰余比較は、元のA/pの標準作用について線形。 -/
def deltaRootPCompletedPerfectionResidueLinearEquiv : (Z ⧸ Kz) ≃ₗ[Q] C ⧸ Kc := by
  let : IsScalarTower A C Z := IsScalarTower.of_algebraMap_eq' rfl
  refine { (deltaRootPCompletedPerfectionResidueEquiv D b).toAddEquiv with map_smul' := ?_ }
  intro a x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  change deltaRootPCompletedPerfectionResidueEquiv D b
    ((Ideal.Quotient.mk Kz (algebraMap A Z a)) * x) =
      (Ideal.Quotient.mk Kc (algebraMap A C a)) *
        deltaRootPCompletedPerfectionResidueEquiv D b x
  rw [map_mul, IsScalarTower.algebraMap_apply A C Z,
    deltaRootPCompletedPerfectionResidueEquiv_mk]

/-- 通常の正確な標準剰余テンソルも、完備化前後でA/p線形に同型。 -/
def deltaRootPCompletedPerfectionResidueTensorEquiv :
    (Q ⊗[A] Z) ≃ₗ[Q] Q ⊗[A] C :=
  ((quotientTensorReductionEquiv I Z).trans (adicReductionEquivAlgebraQuotient I Z)).trans
    ((deltaRootPCompletedPerfectionResidueLinearEquiv D b).trans
      ((quotientTensorReductionEquiv I C).trans (adicReductionEquivAlgebraQuotient I C)).symm)

/-- 通常剰余テンソルの忠実平坦性は、既存p進完備δ完全化へ保存される。 -/
theorem deltaRootPCompletedPerfection_residueTensor_faithfullyFlat
    (hD : D.IsPerfect) (w : Aˣ) (hw : (w : A) = D.delta (p : A)) :
    Module.FaithfullyFlat Q (Q ⊗[A] Z) := by
  have := deltaRootPerfection_residueTensor_faithfullyFlat D b hD w hw
  exact Module.FaithfullyFlat.of_linearEquiv Q (Q ⊗[A] C)
    (deltaRootPCompletedPerfectionResidueTensorEquiv D b)

/-- p進完備δ完全化のp正則性は、元のAのpスカラーについても成り立つ。 -/
theorem deltaRootPCompletedPerfection_p_smul_regular : IsSMulRegular Z (p : A) := by
  intro x y h
  apply (pCompletedDeltaPerfection_isPerfect F).p_mul_injective
  simp only [Algebra.smul_def, map_natCast] at h
  exact h

/-- 完全係数環の任意根族raw包の既存p進完備δ完全化はp完全忠実平坦。 -/
theorem deltaRootPCompletedPerfection_isCompletelyFaithfullyFlat
    (hD : D.IsPerfect) (w : Aˣ) (hw : (w : A) = D.delta (p : A)) :
    IsCompletelyFaithfullyFlat I Z :=
  isCompletelyFaithfullyFlat_principal_of_regular (p : A) hD.p_mul_injective Z
    (deltaRootPCompletedPerfection_p_smul_regular D b)
    (deltaRootPCompletedPerfection_residueTensor_faithfullyFlat D b hD w hw)

end SerrePositivity.BhattScholze
