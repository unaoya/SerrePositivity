module

public import SerrePositivity.BhattScholze.Andre.RootedExtension.Supplement.DeltaRoot.DeltaRootPowerSubsetBaseQuotient
public import SerrePositivity.BhattScholze.Andre.RootedExtension.Supplement.Division.DeltaPDivisionNextInput

/-! # Frobenius根関係の係数商のp²乗根表示と忠実平坦性 -/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 標数pで全根関係のp乗は指数p²のモニック関係式イデアルを与える。 -/
theorem deltaRootPowerRelationIdeal_eq_monic (hp : (p : A) = 0) (b : σ → A) :
    Ideal.span (Set.range fun s ↦ (deltaRootRelationFamily (p := p) b s) ^ p) =
      monicPowerFamilyRelationIdeal (p * p) σ A (fun s ↦ b s ^ p) := by
  have hrange (f : σ → MvPolynomial σ A) :
      Set.range (fun s : (Set.univ : Set σ) ↦ f s) = Set.range f := by
    ext x
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨s, rfl⟩
    · rintro ⟨s, rfl⟩
      exact ⟨⟨s, Set.mem_univ s⟩, rfl⟩
  have h := deltaRootSubset_powerRelationIdeal_eq hp (Set.univ : Set σ) b
  unfold deltaRootSubsetRelationIdeal at h
  rw [hrange (fun s ↦ (deltaRootRelationFamily (p := p) b s) ^ p),
    hrange (deltaRootRelationFamily (p := p * p) (fun s ↦ b s ^ p))] at h
  exact h

variable (D : DeltaStructure p A) (b : σ → A)
local notation "P" => MvPolynomial σ A
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => deltaRootRelationFamily (p := p) b
local notation "a" => fun s ↦ DeltaStructure.frobeniusLift E (r s)
local notation "I" => Ideal.span {(p : A)}
local notation "QA" => A ⧸ I
local notation "c" => fun s ↦ (Ideal.Quotient.mk I (b s)) ^ p
local notation "C" => MonicPowerFamilyCover (p * p) σ QA c
local notation "J" => deltaDivisionFirstBaseIdeal (p := p) (p : P) a

/-- raw Frobenius除算の初期係数商。 -/
abbrev DeltaRootFrobeniusCoefficientQuotient := P ⧸ J

/-- 初期係数イデアルは係数のpと先行根関係のp乗で生成される。 -/
theorem deltaRootFrobeniusCoefficientIdeal_eq :
    J = (I).map (MvPolynomial.C : A →+* P) ⊔ Ideal.span
      (Set.range fun s : (Set.univ : Set σ) ↦ (r s) ^ p) := by
  rw [deltaPDivisionFirstBaseIdeal_frobenius_eq_power]
  unfold deltaDivisionFirstBaseIdeal
  have hpp : Ideal.span {(p : P), (p : P)} = Ideal.span {(p : P)} :=
    congrArg Ideal.span (Set.insert_eq_of_mem (Set.mem_singleton (p : P)))
  rw [hpp]
  simp only [Ideal.map_span, Set.image_singleton, map_natCast]
  congr 1
  congr 1
  ext x
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨⟨s, Set.mem_univ s⟩, rfl⟩
  · rintro ⟨s, rfl⟩
    exact ⟨s, rfl⟩

/-- 標準p商の上で、根関係p乗イデアルは指数p²の通常根関係に一致する。 -/
theorem deltaRootFrobeniusCoefficientResidueIdeal_eq :
    Ideal.span (Set.range fun s : (Set.univ : Set σ) ↦
      (deltaRootRelationFamily (p := p) (fun t ↦ Ideal.Quotient.mk I (b t)) s) ^ p) =
      monicPowerFamilyRelationIdeal (p * p) σ QA c := by
  have hp : (p : QA) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk I)]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have hrange : Set.range (fun s : (Set.univ : Set σ) ↦
      (deltaRootRelationFamily (p := p) (fun t ↦ Ideal.Quotient.mk I (b t)) s) ^ p) =
      Set.range (fun s : σ ↦
        (deltaRootRelationFamily (p := p) (fun t ↦ Ideal.Quotient.mk I (b t)) s) ^ p) := by
    ext x
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨s, rfl⟩
    · rintro ⟨s, rfl⟩
      exact ⟨⟨s, Set.mem_univ s⟩, rfl⟩
  rw [hrange]
  exact deltaRootPowerRelationIdeal_eq_monic hp (fun t ↦ Ideal.Quotient.mk I (b t))

/-- 初期係数商はA/p上の既存p²乗根添加環と標準同型。 -/
def deltaRootFrobeniusCoefficientEquiv : DeltaRootFrobeniusCoefficientQuotient D b ≃+* C :=
  (((Ideal.quotEquivOfEq (deltaRootFrobeniusCoefficientIdeal_eq D b)).trans
    (deltaRootPowerSubsetBaseQuotientEquiv (p := p) I Set.univ b)).trans
    (Ideal.quotEquivOfEq (deltaRootFrobeniusCoefficientResidueIdeal_eq (p := p) b))).trans
    (monicPowerFamilyPresentationEquiv (p * p) σ QA c)

/-- 標準同型は任意多項式代表元の係数をmod pへ送る公式で与えられる。 -/
theorem deltaRootFrobeniusCoefficientEquiv_mk (x : P) :
    deltaRootFrobeniusCoefficientEquiv D b (Ideal.Quotient.mk J x) =
      monicPowerFamilyQuotientMap (p * p) σ QA c
        (Ideal.Quotient.mk _ (MvPolynomial.map (Ideal.Quotient.mk I) x)) := by
  rw [deltaRootFrobeniusCoefficientEquiv, RingEquiv.trans_apply, RingEquiv.trans_apply,
    RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk, deltaRootPowerSubsetBaseQuotientEquiv_mk,
    Ideal.quotEquivOfEq_mk]
  rfl

/-- 初期係数商表示は元の基底係数の標準像を保つ。 -/
theorem deltaRootFrobeniusCoefficientEquiv_C (x : A) :
    deltaRootFrobeniusCoefficientEquiv D b (Ideal.Quotient.mk J (MvPolynomial.C x)) =
      algebraMap QA C (Ideal.Quotient.mk I x) := by
  rw [deltaRootFrobeniusCoefficientEquiv_mk, MvPolynomial.map_C]
  change monicPowerFamilyEvaluation (p * p) σ QA c (MvPolynomial.C _) = _
  simp [monicPowerFamilyEvaluation]

/-- 初期係数商の標準A/p係数射。 -/
def deltaRootFrobeniusCoefficientBaseMap : QA →+* DeltaRootFrobeniusCoefficientQuotient D b :=
  (deltaRootFrobeniusCoefficientEquiv D b).symm.toRingHom.comp (algebraMap QA C)

/-- 標準係数射は元の係数を二つの商の実標準像へ送る。 -/
theorem deltaRootFrobeniusCoefficientBaseMap_mk (x : A) :
    deltaRootFrobeniusCoefficientBaseMap D b (Ideal.Quotient.mk I x) =
      Ideal.Quotient.mk J (MvPolynomial.C x) := by
  apply (deltaRootFrobeniusCoefficientEquiv D b).injective
  change (deltaRootFrobeniusCoefficientEquiv D b)
    ((deltaRootFrobeniusCoefficientEquiv D b).symm _) = _
  rw [RingEquiv.apply_symm_apply, deltaRootFrobeniusCoefficientEquiv_C]

/-- 標準係数射による初期係数商のA/p代数構造。 -/
@[instance_reducible] def deltaRootFrobeniusCoefficientBaseAlgebra :
    Algebra QA (DeltaRootFrobeniusCoefficientQuotient D b) :=
  (deltaRootFrobeniusCoefficientBaseMap D b).toAlgebra

/-- 表示同型は実際のA/p係数射に関する代数同型。 -/
def deltaRootFrobeniusCoefficientAlgEquiv :
    letI := deltaRootFrobeniusCoefficientBaseAlgebra D b
    DeltaRootFrobeniusCoefficientQuotient D b ≃ₐ[QA] C := by
  let := deltaRootFrobeniusCoefficientBaseAlgebra D b
  apply AlgEquiv.ofRingEquiv (f := deltaRootFrobeniusCoefficientEquiv D b)
  intro x
  exact (deltaRootFrobeniusCoefficientEquiv D b).apply_symm_apply _

/-- 初期係数商は標準A/p係数射に関して忠実平坦。有限性・p正則性は不要。 -/
theorem deltaRootFrobeniusCoefficient_moduleFaithfullyFlat :
    letI := deltaRootFrobeniusCoefficientBaseAlgebra D b
    Module.FaithfullyFlat QA (DeltaRootFrobeniusCoefficientQuotient D b) := by
  let := deltaRootFrobeniusCoefficientBaseAlgebra D b
  let := monicPowerFamilyCover_moduleFaithfullyFlat_all (p * p) σ QA c
    (Nat.mul_pos (Fact.out : p.Prime).pos (Fact.out : p.Prime).pos)
  exact Module.FaithfullyFlat.of_linearEquiv _ _
    (deltaRootFrobeniusCoefficientAlgEquiv D b).toLinearEquiv

end SerrePositivity.BhattScholze
