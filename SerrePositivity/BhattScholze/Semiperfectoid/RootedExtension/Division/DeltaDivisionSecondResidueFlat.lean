module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.Division.DeltaDivisionSecondCoefficientPowerEquiv
public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.MonicPowerFamilyPolynomialFlat
public import SerrePositivity.CommutativeAlgebra.CompletelyFlat
public import SerrePositivity.HomologicalAlgebra.Tor

/-! # 第2通常δ剰余の適切な係数商上の自由性と忠実平坦性

通常の未完備商について、標準係数射を明示して既証明の表示から移す。
元のA上や全δ段・完備化後の平坦性とは区別する。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 根添加多項式表示は、元の係数の標準商像を保つ。 -/
@[simp] theorem deltaDivisionSecondResiduePowerPolynomialEquiv_coeff
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d)
    (r : A) :
    deltaDivisionSecondResiduePowerPolynomialEquiv D d a u hu
      (Ideal.Quotient.mk (deltaDivisionSecondResidueIdeal D d a) (MvPolynomial.C r)) =
      algebraMap (A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a)
        (MvPolynomial (σ × ℕ) (DeltaDivisionSecondPowerCover D d a u)) (Ideal.Quotient.mk _ r) := by
  change MvPolynomial.mapEquiv _ _
    (deltaDivisionSecondResiduePolynomialEquiv D d a u hu _) = _
  rw [deltaDivisionSecondResiduePolynomialEquiv_coeff, MvPolynomial.mapEquiv_apply,
    MvPolynomial.map_C]
  change MvPolynomial.C _ = MvPolynomial.C _
  exact congrArg MvPolynomial.C (deltaDivisionSecondCoefficientPowerEquiv_coeff D d a u r)

/-- 適切な係数商から実際の第2通常δ剰余への具体的な係数射。 -/
def deltaDivisionSecondResidueBaseMap
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d) :
    A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a →+*
      RelativeFreeDeltaRing (R := A) σ ⧸ deltaDivisionSecondResidueIdeal D d a :=
  (deltaDivisionSecondResiduePowerPolynomialEquiv D d a u hu).symm.toRingHom.comp
    (algebraMap (A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a)
      (MvPolynomial (σ × ℕ) (DeltaDivisionSecondPowerCover D d a u)))

/-- この係数射は元の係数の標準商射に一致する。 -/
@[simp] theorem deltaDivisionSecondResidueBaseMap_mk
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d)
    (r : A) :
    deltaDivisionSecondResidueBaseMap D d a u hu (Ideal.Quotient.mk _ r) =
      Ideal.Quotient.mk (deltaDivisionSecondResidueIdeal D d a) (MvPolynomial.C r) := by
  apply (deltaDivisionSecondResiduePowerPolynomialEquiv D d a u hu).injective
  change (deltaDivisionSecondResiduePowerPolynomialEquiv D d a u hu)
    ((deltaDivisionSecondResiduePowerPolynomialEquiv D d a u hu).symm _) = _
  rw [RingEquiv.apply_symm_apply, deltaDivisionSecondResiduePowerPolynomialEquiv_coeff]

/-- 標準係数射による、適切な係数商上の実際の第2剰余の代数構造。 -/
@[instance_reducible] def deltaDivisionSecondResidueAlgebra
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d) :
    Algebra (A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a)
      (RelativeFreeDeltaRing (R := A) σ ⧸ deltaDivisionSecondResidueIdeal D d a) :=
  (deltaDivisionSecondResidueBaseMap D d a u hu).toAlgebra

/-- 同時根添加多項式表示は標準係数射について代数同型。 -/
def deltaDivisionSecondResiduePowerPolynomialAlgEquiv
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d) :
    letI := deltaDivisionSecondResidueAlgebra D d a u hu
    (RelativeFreeDeltaRing (R := A) σ ⧸ deltaDivisionSecondResidueIdeal D d a) ≃ₐ[
      A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a]
      MvPolynomial (σ × ℕ) (DeltaDivisionSecondPowerCover D d a u) := by
  letI := deltaDivisionSecondResidueAlgebra D d a u hu
  apply AlgEquiv.ofRingEquiv (f := deltaDivisionSecondResiduePowerPolynomialEquiv D d a u hu)
  intro r
  exact (deltaDivisionSecondResiduePowerPolynomialEquiv D d a u hu).apply_symm_apply _

/-- 同時根添加環の後続多項式環は、適切な係数商上自由。 -/
theorem deltaDivisionSecondPowerPolynomial_moduleFree
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) :
    Module.Free (A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a)
      (MvPolynomial (σ × ℕ) (DeltaDivisionSecondPowerCover D d a u)) := by
  exact monicPowerFamilyPolynomial_moduleFree p (σ × Fin 2) (σ × ℕ)
    (A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a)
    (fun z => Ideal.Quotient.mk _ (deltaDivisionTwoPowerCoefficients D d a u z))
    (Fact.out : p.Prime).pos

/-- 実際の第2通常δ剰余は、適切な係数商上自由。 -/
theorem deltaDivisionSecondResidue_moduleFree
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d) :
    letI := deltaDivisionSecondResidueAlgebra D d a u hu
    Module.Free (A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a)
      (RelativeFreeDeltaRing (R := A) σ ⧸ deltaDivisionSecondResidueIdeal D d a) := by
  let := deltaDivisionSecondResidueAlgebra D d a u hu
  let := deltaDivisionSecondPowerPolynomial_moduleFree D d a u
  exact Module.Free.of_equiv
    (deltaDivisionSecondResiduePowerPolynomialAlgEquiv D d a u hu).symm.toLinearEquiv

/-- 実際の第2通常δ剰余は適切な係数商上平坦。 -/
theorem deltaDivisionSecondResidue_moduleFlat
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d) :
    letI := deltaDivisionSecondResidueAlgebra D d a u hu
    Module.Flat (A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a)
      (RelativeFreeDeltaRing (R := A) σ ⧸ deltaDivisionSecondResidueIdeal D d a) := by
  let := deltaDivisionSecondResidueAlgebra D d a u hu
  let := deltaDivisionSecondResidue_moduleFree D d a u hu
  infer_instance

/-- 同時根添加環の後続多項式環は適切な係数商上忠実平坦。零環も含む。 -/
theorem deltaDivisionSecondPowerPolynomial_moduleFaithfullyFlat
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) :
    Module.FaithfullyFlat (A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a)
      (MvPolynomial (σ × ℕ) (DeltaDivisionSecondPowerCover D d a u)) := by
  exact monicPowerFamilyPolynomial_moduleFaithfullyFlat p (σ × Fin 2) (σ × ℕ)
    (A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a)
    (fun z => Ideal.Quotient.mk _ (deltaDivisionTwoPowerCoefficients D d a u z))
    (Fact.out : p.Prime).pos

/-- 実際の第2通常δ剰余は適切な係数商上忠実平坦。零環も含む。 -/
theorem deltaDivisionSecondResidue_moduleFaithfullyFlat
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d) :
    letI := deltaDivisionSecondResidueAlgebra D d a u hu
    Module.FaithfullyFlat (A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a)
      (RelativeFreeDeltaRing (R := A) σ ⧸ deltaDivisionSecondResidueIdeal D d a) := by
  let := deltaDivisionSecondResidueAlgebra D d a u hu
  let := deltaDivisionSecondPowerPolynomial_moduleFaithfullyFlat D d a u
  exact Module.FaithfullyFlat.of_linearEquiv _ _
    (deltaDivisionSecondResiduePowerPolynomialAlgEquiv D d a u hu).toLinearEquiv

/-- 実際の第2通常δ剰余は、適切な係数商の任意イデアルに関して完全平坦。 -/
theorem deltaDivisionSecondResidue_isCompletelyFlat
    (σ : Type u) (D : DeltaStructure p A) (d : A) (a : σ → A)
    (u : Aˣ) (hu : (u : A) = D.delta d)
    (I : Ideal (A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a)) :
    letI := deltaDivisionSecondResidueAlgebra D d a u hu
    IsCompletelyFlat I
      (RelativeFreeDeltaRing (R := A) σ ⧸ deltaDivisionSecondResidueIdeal D d a) := by
  let := deltaDivisionSecondResidueAlgebra D d a u hu
  let := deltaDivisionSecondResidue_moduleFlat D d a u hu
  intro N _ _ _
  rw [isConcentratedInDegreeZero_derivedTensor_iff]
  intro i hi
  cases i with
  | zero => exact (Nat.lt_irrefl 0 hi).elim
  | succ i =>
      exact torModule_subsingleton_of_flat (R := A ⧸ deltaDivisionFirstBaseIdeal d a)
        (RelativeFreeDeltaRing (R := A) σ ⧸ deltaDivisionSecondResidueIdeal D d a) N i

/-- 実際の第2通常δ剰余は適切な係数商上完全忠実平坦。零環も含む。 -/
theorem deltaDivisionSecondResidue_isCompletelyFaithfullyFlat
    (σ : Type u) (D : DeltaStructure p A) (d : A) (a : σ → A)
    (u : Aˣ) (hu : (u : A) = D.delta d)
    (I : Ideal (A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a)) :
    letI := deltaDivisionSecondResidueAlgebra D d a u hu
    IsCompletelyFaithfullyFlat I
      (RelativeFreeDeltaRing (R := A) σ ⧸ deltaDivisionSecondResidueIdeal D d a) := by
  let := deltaDivisionSecondResidueAlgebra D d a u hu
  let := deltaDivisionSecondResidue_moduleFaithfullyFlat D d a u hu
  refine ⟨deltaDivisionSecondResidue_isCompletelyFlat σ D d a u hu I, ?_⟩
  infer_instance

end SerrePositivity.BhattScholze
