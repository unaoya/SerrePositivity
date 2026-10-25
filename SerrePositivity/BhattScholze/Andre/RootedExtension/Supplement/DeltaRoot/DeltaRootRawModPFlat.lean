module

public import SerrePositivity.BhattScholze.Andre.RootedExtension.Supplement.DeltaRoot.DeltaRootFrobeniusCoefficient

/-! # 根関係のraw p除算包の実mod p商の標準係数射と忠実平坦性 -/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

variable (D : DeltaStructure p A) (b : σ → A)
variable (hpA : Function.Injective (fun x : A ↦ (p : A) * x))
variable (hg : Function.Injective (WittVector.ghostMap :
  WittVector p (RelativeFreeDeltaRing (R := MvPolynomial σ A) σ) →
    ℕ → RelativeFreeDeltaRing (R := MvPolynomial σ A) σ))
variable (w : Aˣ) (hw : (w : A) = D.delta (p : A))
local notation "P" => MvPolynomial σ A
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "a" => fun s ↦ DeltaStructure.frobeniusLift E (deltaRootRelationFamily (p := p) b s)
local notation "Q" => DeltaRootFrobeniusCoefficientQuotient D b
local notation "Res" => DeltaAdjoinDivisionResidue E (p : P) a
local notation "B" => DeltaAdjoinDivision E (p : P) a
local notation "QA" => A ⧸ Ideal.span {(p : A)}
local notation "wp" => Units.map (RingHom.toMonoidHom (MvPolynomial.C : A →+* P)) w

/-- 根関係raw残余商の標準A/p係数射。 -/
def deltaRootRawResidueBaseMap : QA →+* Res := by
  have hP : IsSMulRegular P (p : P) := by
    simpa only [map_natCast] using
      (show IsSMulRegular A (p : A) from hpA).of_flat (S := P)
  have hpP : Function.Injective (fun x : P ↦ (p : P) * x) := hP
  let L := RelativeFreeDeltaRing (R := P) σ
  have hL : IsSMulRegular L (p : L) := by
    simpa only [map_natCast] using hP.of_flat (S := L)
  have hpL : Function.Injective (fun x : L ↦ (p : L) * x) := hL
  have hwp : (wp : P) = (E).delta (p : P) := by
    change MvPolynomial.C (w : A) = _
    rw [hw, ← polynomialRankOneDeltaStructure_delta_C σ D (p : A), map_natCast]
  exact (deltaAdjoinDivisionResidueBaseMap E hpP hpL hg
    (p : P) a wp hwp).comp (deltaRootFrobeniusCoefficientBaseMap D b)

/-- 残余係数射の元の係数上の具体的公式。 -/
theorem deltaRootRawResidueBaseMap_mk (x : A) :
    deltaRootRawResidueBaseMap D b hpA hg w hw (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (deltaAdjoinDivisionMap E (p : P) a (MvPolynomial.C x)) := by
  rw [deltaRootRawResidueBaseMap, RingHom.comp_apply,
    deltaRootFrobeniusCoefficientBaseMap_mk, deltaAdjoinDivisionResidueBaseMap_mk]

/-- 残余標準係数射のA/p代数構造。 -/
@[instance_reducible]
def deltaRootRawResidueBaseAlgebra : Algebra QA Res :=
  (deltaRootRawResidueBaseMap D b hpA hg w hw).toAlgebra

/-- raw残余商は標準A/p係数射に関して忠実平坦。添字集合の有限性は不要。 -/
theorem deltaRootRawResidue_moduleFaithfullyFlat :
    letI := deltaRootRawResidueBaseAlgebra D b hpA hg w hw
    Module.FaithfullyFlat QA Res := by
  have hP : IsSMulRegular P (p : P) := by
    simpa only [map_natCast] using
      (show IsSMulRegular A (p : A) from hpA).of_flat (S := P)
  have hpP : Function.Injective (fun x : P ↦ (p : P) * x) := hP
  let L := RelativeFreeDeltaRing (R := P) σ
  have hL : IsSMulRegular L (p : L) := by
    simpa only [map_natCast] using hP.of_flat (S := L)
  have hpL : Function.Injective (fun x : L ↦ (p : L) * x) := hL
  have hwp : (wp : P) = (E).delta (p : P) := by
    change MvPolynomial.C (w : A) = _
    rw [hw, ← polynomialRankOneDeltaStructure_delta_C σ D (p : A), map_natCast]
  let := deltaRootFrobeniusCoefficientBaseAlgebra D b
  let := deltaAdjoinDivisionResidueBaseAlgebra E hpP hpL
    hg (p : P) a wp hwp
  let := deltaRootRawResidueBaseAlgebra D b hpA hg w hw
  have : IsScalarTower QA Q Res := IsScalarTower.of_algebraMap_eq' rfl
  let := deltaRootFrobeniusCoefficient_moduleFaithfullyFlat D b
  let := deltaAdjoinDivisionResidue_moduleFaithfullyFlat E hpP
    hpL hg (p : P) a wp hwp
  exact Module.FaithfullyFlat.trans QA Q Res

/-- 実際のraw包のp商への標準A/p係数射。 -/
def deltaRootRawModPBaseMap : QA →+* (B ⧸ Ideal.span {(p : B)}) :=
  (deltaAdjoinDivisionPQuotientResidueEquiv E a).symm.toRingHom.comp
    (deltaRootRawResidueBaseMap D b hpA hg w hw)

/-- 実mod p係数射は元の係数の実標準商像を与える。 -/
theorem deltaRootRawModPBaseMap_mk (x : A) :
    deltaRootRawModPBaseMap D b hpA hg w hw (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (deltaAdjoinDivisionMap E (p : P) a (MvPolynomial.C x)) := by
  rw [deltaRootRawModPBaseMap, RingHom.comp_apply]
  apply (deltaAdjoinDivisionPQuotientResidueEquiv E a).injective
  change (deltaAdjoinDivisionPQuotientResidueEquiv E a)
    ((deltaAdjoinDivisionPQuotientResidueEquiv E a).symm _) = _
  rw [RingEquiv.apply_symm_apply, deltaRootRawResidueBaseMap_mk,
    deltaAdjoinDivisionPQuotientResidueEquiv_mk]

/-- 実mod p標準係数射のA/p代数構造。 -/
@[instance_reducible]
def deltaRootRawModPBaseAlgebra : Algebra QA (B ⧸ Ideal.span {(p : B)}) :=
  (deltaRootRawModPBaseMap D b hpA hg w hw).toAlgebra

/-- raw(p,p)残余と実p商の標準同型はA/p代数同型。 -/
def deltaRootRawModPResidueAlgEquiv :
    letI := deltaRootRawModPBaseAlgebra D b hpA hg w hw
    letI := deltaRootRawResidueBaseAlgebra D b hpA hg w hw
    (B ⧸ Ideal.span {(p : B)}) ≃ₐ[QA] Res := by
  let := deltaRootRawModPBaseAlgebra D b hpA hg w hw
  let := deltaRootRawResidueBaseAlgebra D b hpA hg w hw
  apply AlgEquiv.ofRingEquiv (f := deltaAdjoinDivisionPQuotientResidueEquiv E a)
  intro x
  change (deltaAdjoinDivisionPQuotientResidueEquiv E a)
    (deltaRootRawModPBaseMap D b hpA hg w hw x) =
      deltaRootRawResidueBaseMap D b hpA hg w hw x
  rw [deltaRootRawModPBaseMap, RingHom.comp_apply]
  exact (deltaAdjoinDivisionPQuotientResidueEquiv E a).apply_symm_apply _

/-- 根関係のraw同時p除算包の実p商は、標準A/p係数射に関して忠実平坦。 -/
theorem deltaRootRawModP_moduleFaithfullyFlat :
    letI := deltaRootRawModPBaseAlgebra D b hpA hg w hw
    Module.FaithfullyFlat QA (B ⧸ Ideal.span {(p : B)}) := by
  let := deltaRootRawModPBaseAlgebra D b hpA hg w hw
  let := deltaRootRawResidueBaseAlgebra D b hpA hg w hw
  let := deltaRootRawResidue_moduleFaithfullyFlat D b hpA hg w hw
  exact Module.FaithfullyFlat.of_linearEquiv QA Res
    (deltaRootRawModPResidueAlgEquiv D b hpA hg w hw).toLinearEquiv

end SerrePositivity.BhattScholze
