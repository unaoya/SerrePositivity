module

public import SerrePositivity.BhattScholze.PerfectPrismRootPrismCompletelyFlat
public import SerrePositivity.HomologicalAlgebra.AlgebraRestrictionSingle
public import SerrePositivity.HomologicalAlgebra.RegularPrincipalTor

/-! # 根prism候補の実生成元商と標準perfectoid商の同定 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard adicQuotientAlgebra
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect) (b : σ → A)
local notation "D" => OrientedPrism.deltaStructure P
local notation "d" => OrientedPrism.generator P
local notation "hd" => OrientedPrism.isDistinguished_of_perfect P hP
local notation "T" => DeltaRootPrismCarrier D d b
local notation "f" => deltaRootPrismCoefficientMap D d b
local notation "J" => Ideal.span {d}
local notation "R" => A ⧸ J
local notation "q" => Ideal.Quotient.mk J
local notation "P'" => deltaRootPrism D d b hd
local notation "S" => DeltaRootPerfectoidCandidate D d b hd
local notation "g" => deltaRootPerfectoidCandidateBaseMap D d b hd
local notation "M" => baseChangeScalarModule f
include hP

/-- 候補の生成元の正則性は、元Aのdによるスカラー作用の正則性でもある。 -/
theorem perfectPrismRootPrism_generator_smul_regular :
    letI := deltaRootPrismCommRing D d b
    IsSMulRegular (ModuleCat.carrier M) d := by
  let := deltaRootPrismCommRing D d b
  intro x y h
  change T at x y
  change f d * x = f d * y at h
  exact (P').generator_regular h

/-- 元と候補の生成元が正則なので、生成元商への実係数拡大はTor非輪状。 -/
theorem perfectPrismRootPrism_generator_torVanishing :
    letI := deltaRootPrismCommRing D d b
    scalarExtensionTorVanishing q M := by
  let := deltaRootPrismCommRing D d b
  exact scalarExtensionTorVanishing_principal_of_regular d P.generator_regular M
    (perfectPrismRootPrism_generator_smul_regular P hP b)

/-- 通常生成元商の標準係数作用を既存perfectoid候補の基底射と照合する。 -/
def perfectPrismRootPrism_ordinaryQuotientIso :
    letI := deltaRootPrismCommRing D d b
    (ModuleCat.extendScalars q).obj M ≅ baseChangeScalarModule g := by
  let := deltaRootPrismCommRing D d b
  let := deltaRootPrismCoefficientAlgebra D d b
  have hI : (J).map (algebraMap A T) = (P').ideal := by
    change (J).map f = (P').ideal
    exact deltaRootPrismCoefficientMap_ideal D d b hd
  let eR : (T ⧸ (J).map (algebraMap A T)) ≃+* S := Ideal.quotEquivOfEq hI
  let Mc : ModuleCat.{u} R := ModuleCat.of R (T ⧸ (J).map (algebraMap A T))
  let Nc : ModuleCat.{u} R := baseChangeScalarModule g
  let eA : Mc ≃ₗ[R] Nc :=
    { eR.toAddEquiv with
      map_smul' := by
        intro a x
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
        change eR (Ideal.Quotient.mk _ (f a) * x) =
          Ideal.Quotient.mk (P').ideal (f a) * eR x
        rw [map_mul]
        rfl }
  exact (ModuleCat.extendScalars q).mapIso (algebraSelfRestrictionIso A T) ≪≫
    (quotientAlgebraScalarExtensionEquiv J T).toModuleIso ≪≫ eA.toModuleIso

/-- 元の実生成元還元は、既存perfectoid商の同じ基底射付きsingle対象と同型。 -/
def perfectPrismRootPrism_derivedQuotientIso :
    letI := deltaRootPrismCommRing D d b
    (boundedAboveDerivedBaseChange q).obj (boundedAboveDerivedSingleFunctor.obj M) ≅
      boundedAboveDerivedSingleFunctor.obj (baseChangeScalarModule g) := by
  let := deltaRootPrismCommRing D d b
  exact boundedAboveDerivedBaseChangeModuleAugmentationIso q M
    (perfectPrismRootPrism_generator_torVanishing P hP b) ≪≫
      boundedAboveDerivedSingleFunctor.mapIso (perfectPrismRootPrism_ordinaryQuotientIso P hP b)

end SerrePositivity.BhattScholze
