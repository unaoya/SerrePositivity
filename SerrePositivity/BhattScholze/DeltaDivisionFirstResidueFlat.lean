module

public import SerrePositivity.BhattScholze.DeltaDivisionFirstCoefficientPowerEquiv
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import SerrePositivity.CommutativeAlgebra.CompletelyFlat
public import SerrePositivity.HomologicalAlgebra.Tor

/-! # 初期δ剰余の適切な係数商上の自由性と忠実平坦性

通常の未完備商について、標準係数射を明示して既証明の表示から移す。
元のA上や全δ段・完備化後の平坦性とは区別する。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open scoped DirectSum
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 根添加多項式表示は、元の係数の標準商像を保つ。 -/
@[simp] theorem deltaDivisionFirstResiduePowerPolynomialEquiv_coeff
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d)
    (r : A) :
    deltaDivisionFirstResiduePowerPolynomialEquiv D d a u hu
      (Ideal.Quotient.mk (deltaDivisionFirstResidueIdeal D d a) (MvPolynomial.C r)) =
      algebraMap (A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a)
        (MvPolynomial (σ × ℕ) (DeltaDivisionFirstPowerCover D d a u)) (Ideal.Quotient.mk _ r) := by
  change MvPolynomial.mapEquiv _ _
    (deltaDivisionFirstResiduePolynomialEquiv D d a u hu _) = _
  rw [deltaDivisionFirstResiduePolynomialEquiv_coeff, MvPolynomial.mapEquiv_apply,
    MvPolynomial.map_C]
  change MvPolynomial.C _ = MvPolynomial.C _
  exact congrArg MvPolynomial.C (deltaDivisionFirstCoefficientPowerEquiv_coeff D d a u r)

/-- 適切な係数商から実際の初期δ剰余への具体的な係数射。 -/
def deltaDivisionFirstResidueBaseMap
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d) :
    A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a →+*
      RelativeFreeDeltaRing (R := A) σ ⧸ deltaDivisionFirstResidueIdeal D d a :=
  (deltaDivisionFirstResiduePowerPolynomialEquiv D d a u hu).symm.toRingHom.comp
    (algebraMap (A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a)
      (MvPolynomial (σ × ℕ) (DeltaDivisionFirstPowerCover D d a u)))

/-- この係数射は元の係数の標準商射に一致する。 -/
@[simp] theorem deltaDivisionFirstResidueBaseMap_mk
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d)
    (r : A) :
    deltaDivisionFirstResidueBaseMap D d a u hu (Ideal.Quotient.mk _ r) =
      Ideal.Quotient.mk (deltaDivisionFirstResidueIdeal D d a) (MvPolynomial.C r) := by
  apply (deltaDivisionFirstResiduePowerPolynomialEquiv D d a u hu).injective
  change (deltaDivisionFirstResiduePowerPolynomialEquiv D d a u hu)
    ((deltaDivisionFirstResiduePowerPolynomialEquiv D d a u hu).symm _) = _
  rw [RingEquiv.apply_symm_apply, deltaDivisionFirstResiduePowerPolynomialEquiv_coeff]

/-- 標準係数射による、適切な係数商上の実際の初期剰余の代数構造。 -/
@[instance_reducible] def deltaDivisionFirstResidueAlgebra
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d) :
    Algebra (A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a)
      (RelativeFreeDeltaRing (R := A) σ ⧸ deltaDivisionFirstResidueIdeal D d a) :=
  (deltaDivisionFirstResidueBaseMap D d a u hu).toAlgebra

/-- 初期根添加多項式表示は標準係数射について代数同型。 -/
def deltaDivisionFirstResiduePowerPolynomialAlgEquiv
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d) :
    letI := deltaDivisionFirstResidueAlgebra D d a u hu
    (RelativeFreeDeltaRing (R := A) σ ⧸ deltaDivisionFirstResidueIdeal D d a) ≃ₐ[
      A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a]
      MvPolynomial (σ × ℕ) (DeltaDivisionFirstPowerCover D d a u) := by
  letI := deltaDivisionFirstResidueAlgebra D d a u hu
  apply AlgEquiv.ofRingEquiv (f := deltaDivisionFirstResiduePowerPolynomialEquiv D d a u hu)
  intro r
  exact (deltaDivisionFirstResiduePowerPolynomialEquiv D d a u hu).apply_symm_apply _

/-- 初期根添加環の後続多項式環は、適切な係数商上自由。 -/
theorem deltaDivisionFirstPowerPolynomial_moduleFree
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) :
    Module.Free (A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a)
      (MvPolynomial (σ × ℕ) (DeltaDivisionFirstPowerCover D d a u)) := by
  let R := A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a
  let C := DeltaDivisionFirstPowerCover D d a u
  let := monicPowerFamilyCover_moduleFree p σ R (deltaDivisionFirstPowerCoefficients D d a u)
    (Fact.out : p.Prime).pos
  exact Module.Free.of_equiv
    ((MvPolynomial.basisMonomials (σ × ℕ) C).repr.restrictScalars R).symm

/-- 実際の初期δ剰余は、適切な係数商上自由。 -/
theorem deltaDivisionFirstResidue_moduleFree
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d) :
    letI := deltaDivisionFirstResidueAlgebra D d a u hu
    Module.Free (A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a)
      (RelativeFreeDeltaRing (R := A) σ ⧸ deltaDivisionFirstResidueIdeal D d a) := by
  let := deltaDivisionFirstResidueAlgebra D d a u hu
  let := deltaDivisionFirstPowerPolynomial_moduleFree D d a u
  exact Module.Free.of_equiv
    (deltaDivisionFirstResiduePowerPolynomialAlgEquiv D d a u hu).symm.toLinearEquiv

/-- 実際の初期δ剰余は適切な係数商上平坦。 -/
theorem deltaDivisionFirstResidue_moduleFlat
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d) :
    letI := deltaDivisionFirstResidueAlgebra D d a u hu
    Module.Flat (A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a)
      (RelativeFreeDeltaRing (R := A) σ ⧸ deltaDivisionFirstResidueIdeal D d a) := by
  let := deltaDivisionFirstResidueAlgebra D d a u hu
  let := deltaDivisionFirstResidue_moduleFree D d a u hu
  infer_instance

/-- 初期根添加環の後続多項式環は適切な係数商上忠実平坦。零環も含む。 -/
theorem deltaDivisionFirstPowerPolynomial_moduleFaithfullyFlat
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) :
    Module.FaithfullyFlat (A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a)
      (MvPolynomial (σ × ℕ) (DeltaDivisionFirstPowerCover D d a u)) := by
  classical
  let R := A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a
  let C := DeltaDivisionFirstPowerCover D d a u
  let ι := (σ × ℕ) →₀ ℕ
  let := monicPowerFamilyCover_moduleFaithfullyFlat_all p σ R
    (deltaDivisionFirstPowerCoefficients D d a u) (Fact.out : p.Prime).pos
  let : Module.FaithfullyFlat R (ι →₀ C) :=
    Module.FaithfullyFlat.of_linearEquiv R (⨁ _ : ι, C) (finsuppLEquivDirectSum R C ι)
  exact Module.FaithfullyFlat.of_linearEquiv R (ι →₀ C)
    ((MvPolynomial.basisMonomials (σ × ℕ) C).repr.restrictScalars R)

/-- 実際の初期δ剰余は適切な係数商上忠実平坦。零環も含む。 -/
theorem deltaDivisionFirstResidue_moduleFaithfullyFlat
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d) :
    letI := deltaDivisionFirstResidueAlgebra D d a u hu
    Module.FaithfullyFlat (A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a)
      (RelativeFreeDeltaRing (R := A) σ ⧸ deltaDivisionFirstResidueIdeal D d a) := by
  let := deltaDivisionFirstResidueAlgebra D d a u hu
  let := deltaDivisionFirstPowerPolynomial_moduleFaithfullyFlat D d a u
  exact Module.FaithfullyFlat.of_linearEquiv _ _
    (deltaDivisionFirstResiduePowerPolynomialAlgEquiv D d a u hu).toLinearEquiv

/-- 実際の初期δ剰余は、適切な係数商の任意イデアルに関して完全平坦。 -/
theorem deltaDivisionFirstResidue_isCompletelyFlat
    (σ : Type u) (D : DeltaStructure p A) (d : A) (a : σ → A)
    (u : Aˣ) (hu : (u : A) = D.delta d)
    (I : Ideal (A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a)) :
    letI := deltaDivisionFirstResidueAlgebra D d a u hu
    IsCompletelyFlat I
      (RelativeFreeDeltaRing (R := A) σ ⧸ deltaDivisionFirstResidueIdeal D d a) := by
  let := deltaDivisionFirstResidueAlgebra D d a u hu
  let := deltaDivisionFirstResidue_moduleFlat D d a u hu
  intro N _ _ _
  rw [isConcentratedInDegreeZero_derivedTensor_iff]
  intro i hi
  cases i with
  | zero => exact (Nat.lt_irrefl 0 hi).elim
  | succ i =>
      exact torModule_subsingleton_of_flat (R := A ⧸ deltaDivisionFirstBaseIdeal d a)
        (RelativeFreeDeltaRing (R := A) σ ⧸ deltaDivisionFirstResidueIdeal D d a) N i

/-- 実際の初期δ剰余は適切な係数商上完全忠実平坦。零環も含む。 -/
theorem deltaDivisionFirstResidue_isCompletelyFaithfullyFlat
    (σ : Type u) (D : DeltaStructure p A) (d : A) (a : σ → A)
    (u : Aˣ) (hu : (u : A) = D.delta d)
    (I : Ideal (A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a)) :
    letI := deltaDivisionFirstResidueAlgebra D d a u hu
    IsCompletelyFaithfullyFlat I
      (RelativeFreeDeltaRing (R := A) σ ⧸ deltaDivisionFirstResidueIdeal D d a) := by
  let := deltaDivisionFirstResidueAlgebra D d a u hu
  let := deltaDivisionFirstResidue_moduleFaithfullyFlat D d a u hu
  refine ⟨deltaDivisionFirstResidue_isCompletelyFlat σ D d a u hu I, ?_⟩
  infer_instance

end SerrePositivity.BhattScholze
