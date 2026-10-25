module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.DeltaRoot.DeltaRootRawModPFlat
public import Mathlib.RingTheory.TensorProduct.Quotient

/-! # 元の係数射に沿う根関係raw包の実mod p基底変更 -/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open scoped TensorProduct
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (b : σ → A)
local notation "P" => MvPolynomial σ A
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "a" => fun s ↦ DeltaStructure.frobeniusLift E (deltaRootRelationFamily (p := p) b s)
local notation "B" => DeltaAdjoinDivision E (p : P) a
local notation "I" => Ideal.span {(p : A)}
local notation "QA" => A ⧸ I

/-- 元のδ係数環から多項式環を経由するraw包への実係数射。 -/
def deltaRootRawCoefficientMap : A →+* B :=
  (deltaAdjoinDivisionMap E (p : P) a).comp MvPolynomial.C

/-- 実係数射によるraw包のA代数構造。 -/
@[instance_reducible]
def deltaRootRawCoefficientAlgebra : Algebra A B :=
  inferInstance

/-- 既存のA代数構造の係数射は、公開した実係数射そのもの。 -/
theorem deltaRootRawCoefficientAlgebra_algebraMap :
    letI := deltaRootRawCoefficientAlgebra D b
    algebraMap A B = deltaRootRawCoefficientMap D b := rfl

/-- 元のp主イデアルのraw包への拡張は、raw包自身の実p主イデアル。 -/
theorem deltaRootRawCoefficient_map_span_p :
    letI := deltaRootRawCoefficientAlgebra D b
    (I).map (algebraMap A B) = Ideal.span {(p : B)} := by
  simp only [Ideal.map_span, Set.image_singleton, map_natCast]

variable (hpA : Function.Injective (fun x : A ↦ (p : A) * x))
variable (hg : Function.Injective (WittVector.ghostMap :
  WittVector p (RelativeFreeDeltaRing (R := MvPolynomial σ A) σ) →
    ℕ → RelativeFreeDeltaRing (R := MvPolynomial σ A) σ))
variable (w : Aˣ) (hw : (w : A) = D.delta (p : A))

/-- 元の係数pイデアルによる商とraw包の実p商の比較は標準A/p代数同型。 -/
def deltaRootRawCoefficientQuotientAlgEquiv :
    letI := deltaRootRawCoefficientAlgebra D b
    letI := deltaRootRawModPBaseAlgebra D b hpA hg w hw
    (B ⧸ (I).map (algebraMap A B)) ≃ₐ[QA] (B ⧸ Ideal.span {(p : B)}) := by
  let := deltaRootRawCoefficientAlgebra D b
  let := deltaRootRawModPBaseAlgebra D b hpA hg w hw
  apply AlgEquiv.ofRingEquiv (f := Ideal.quotEquivOfEq (deltaRootRawCoefficient_map_span_p D b))
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.quotEquivOfEq (deltaRootRawCoefficient_map_span_p D b)
    (Ideal.Quotient.mk _ (deltaRootRawCoefficientMap D b x)) =
      deltaRootRawModPBaseMap D b hpA hg w hw (Ideal.Quotient.mk I x)
  rw [Ideal.quotEquivOfEq_mk, deltaRootRawModPBaseMap_mk]
  rfl

/-- 元のA→A/pに沿う通常基底変更は実raw p商と標準同型。 -/
def deltaRootRawBaseChangeModPAlgEquiv :
    letI := deltaRootRawCoefficientAlgebra D b
    letI := deltaRootRawModPBaseAlgebra D b hpA hg w hw
    QA ⊗[A] B ≃ₐ[QA] (B ⧸ Ideal.span {(p : B)}) := by
  let := deltaRootRawCoefficientAlgebra D b
  let := deltaRootRawModPBaseAlgebra D b hpA hg w hw
  exact (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).symm.trans
    (deltaRootRawCoefficientQuotientAlgEquiv D b hpA hg w hw)

/-- 実基底変更同型は1⊗zをzの実p商像へ送る。 -/
theorem deltaRootRawBaseChangeModPAlgEquiv_one_tmul (z : B) :
    letI := deltaRootRawCoefficientAlgebra D b
    letI := deltaRootRawModPBaseAlgebra D b hpA hg w hw
    deltaRootRawBaseChangeModPAlgEquiv D b hpA hg w hw ((1 : QA) ⊗ₜ[A] z) =
      Ideal.Quotient.mk (Ideal.span {(p : B)}) z := by
  let := deltaRootRawCoefficientAlgebra D b
  let := deltaRootRawModPBaseAlgebra D b hpA hg w hw
  change deltaRootRawCoefficientQuotientAlgEquiv D b hpA hg w hw
    ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).symm _) = _
  rw [← Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk B I z,
    AlgEquiv.symm_apply_apply]
  exact Ideal.quotEquivOfEq_mk (deltaRootRawCoefficient_map_span_p D b) z

include hpA hg hw in
/-- 元の係数射に沿う実通常mod p基底変更加群はA/p上忠実平坦。 -/
theorem deltaRootRawBaseChangeModP_moduleFaithfullyFlat :
    letI := deltaRootRawCoefficientAlgebra D b
    Module.FaithfullyFlat QA (QA ⊗[A] B) := by
  let := deltaRootRawCoefficientAlgebra D b
  let := deltaRootRawModPBaseAlgebra D b hpA hg w hw
  let := deltaRootRawModP_moduleFaithfullyFlat D b hpA hg w hw
  exact Module.FaithfullyFlat.of_linearEquiv QA (B ⧸ Ideal.span {(p : B)})
    (deltaRootRawBaseChangeModPAlgEquiv D b hpA hg w hw).toLinearEquiv

end SerrePositivity.BhattScholze
