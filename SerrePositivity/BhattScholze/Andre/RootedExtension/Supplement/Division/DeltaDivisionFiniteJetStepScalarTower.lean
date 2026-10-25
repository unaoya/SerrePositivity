module

public import SerrePositivity.BhattScholze.Andre.RootedExtension.Supplement.Division.DeltaDivisionFiniteJetStepComparison
public import SerrePositivity.BhattScholze.Andre.RootedExtension.Supplement.Division.DeltaDivisionNormalizedStepTor

/-! # 元のδ段間射の標準係数射・スカラー塔と係数環上の平坦性 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A)
variable (hpA : Function.Injective (fun z : A ↦ (p : A) * z))
variable (hpL : Function.Injective (fun z : RelativeFreeDeltaRing (R := A) σ ↦
  (p : RelativeFreeDeltaRing (R := A) σ) * z))
variable (hg : Function.Injective (WittVector.ghostMap :
  WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
variable (d : A) (a : σ → A) (v : Aˣ) (hv : (v : A) = D.delta d) (N : ℕ)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "R₀" => L₀ ⧸ (Ideal.span {(p : L₀), MvPolynomial.C d} ⊔
  deltaDivisionFiniteRelationIdeal D d a (N + 1))
local notation "R₁" => L₀ ⧸ (Ideal.span {(p : L₀), MvPolynomial.C d} ⊔
  deltaDivisionFiniteRelationIdeal D d a (N + 2))
local notation "Q₀" => DeltaDivisionFiniteNormalizedQuotient D d a v N
local notation "Q₁" => DeltaDivisionFiniteNormalizedQuotient D d a v (N + 1)
local notation "S₀" => MvPolynomial (σ × Fin (N + 2)) A ⧸
  deltaDivisionNormalizedStepSourceIdeal D d a v N

/-- 前段正規化商から元の下位δ関係商への標準係数射。 -/
def deltaDivisionFiniteJetSourceCoefficientMap : Q₀ →+* R₀ :=
  (deltaDivisionFiniteJetStepSourceEquiv D hpA hpL hg d a v hv N).symm.toRingHom.comp
    ((MvPolynomial.C : S₀ →+* MvPolynomial (σ × ℕ) S₀).comp
      (deltaDivisionNormalizedStepSourceCoefficientMap D d a v N))

/-- 前段正規化商から元の次段δ関係商への標準係数射。 -/
def deltaDivisionFiniteJetTargetCoefficientMap : Q₀ →+* R₁ :=
  (deltaDivisionFiniteJetStepTargetEquiv D hpA hpL hg d a v hv N).symm.toRingHom.comp
    ((MvPolynomial.C : Q₁ →+* MvPolynomial (σ × ℕ) Q₁).comp
      (deltaDivisionFiniteNormalizedStepMap D d a v N))

/-- 元の段間射と標準係数射の合成は、次段商の標準係数射。 -/
theorem deltaDivisionFiniteJetStepMap_comp_coefficient :
    (deltaDivisionFiniteJetStepMap D d a N).comp
      (deltaDivisionFiniteJetSourceCoefficientMap D hpA hpL hg d a v hv N) =
      deltaDivisionFiniteJetTargetCoefficientMap D hpA hpL hg d a v hv N := by
  apply RingHom.ext
  intro c
  let eS := deltaDivisionFiniteJetStepSourceEquiv D hpA hpL hg d a v hv N
  let eT := deltaDivisionFiniteJetStepTargetEquiv D hpA hpL hg d a v hv N
  apply eT.injective
  change eT (deltaDivisionFiniteJetStepMap D d a N
      (deltaDivisionFiniteJetSourceCoefficientMap D hpA hpL hg d a v hv N c)) =
    eT (eT.symm (MvPolynomial.C (deltaDivisionFiniteNormalizedStepMap D d a v N c)))
  rw [RingEquiv.apply_symm_apply]
  have h := RingHom.congr_fun
    (deltaDivisionFiniteJetStepComparison D hpA hpL hg d a v hv N)
    (deltaDivisionFiniteJetSourceCoefficientMap D hpA hpL hg d a v hv N c)
  change eT (deltaDivisionFiniteJetStepMap D d a N
      (deltaDivisionFiniteJetSourceCoefficientMap D hpA hpL hg d a v hv N c)) =
    MvPolynomial.map (deltaDivisionNormalizedStepNextMap D d a v N)
      (eS (eS.symm
        (MvPolynomial.C (deltaDivisionNormalizedStepSourceCoefficientMap D d a v N c)))) at h
  rw [RingEquiv.apply_symm_apply, MvPolynomial.map_C] at h
  exact h.trans (congrArg MvPolynomial.C
    (RingHom.congr_fun (deltaDivisionNormalizedStepNextMap_comp_coefficient D d a v N) c))

/-- 元の下位δ関係商の標準前段正規化商代数構造。 -/
@[instance_reducible] def deltaDivisionFiniteJetSourceAlgebra : Algebra Q₀ R₀ :=
  (deltaDivisionFiniteJetSourceCoefficientMap D hpA hpL hg d a v hv N).toAlgebra

/-- 元の次段δ関係商の標準前段正規化商代数構造。 -/
@[instance_reducible] def deltaDivisionFiniteJetTargetAlgebra : Algebra Q₀ R₁ :=
  (deltaDivisionFiniteJetTargetCoefficientMap D hpA hpL hg d a v hv N).toAlgebra

/-- 元の下位商の比較は、標準前段正規化商代数同型。 -/
def deltaDivisionFiniteJetSourceAlgEquiv :
    letI := deltaDivisionNormalizedStepSourceAlgebra D d a v N
    letI := deltaDivisionFiniteJetSourceAlgebra D hpA hpL hg d a v hv N
    R₀ ≃ₐ[Q₀] MvPolynomial (σ × ℕ) S₀ := by
  letI := deltaDivisionNormalizedStepSourceAlgebra D d a v N
  letI := deltaDivisionFiniteJetSourceAlgebra D hpA hpL hg d a v hv N
  apply AlgEquiv.ofRingEquiv (f := deltaDivisionFiniteJetStepSourceEquiv D hpA hpL hg d a v hv N)
  intro c
  exact (deltaDivisionFiniteJetStepSourceEquiv D hpA hpL hg d a v hv N).apply_symm_apply _

/-- 元の次段商の比較も、標準前段正規化商代数同型。 -/
def deltaDivisionFiniteJetTargetAlgEquiv :
    letI := deltaDivisionFiniteNormalizedStepAlgebra D d a v N
    letI := deltaDivisionFiniteJetTargetAlgebra D hpA hpL hg d a v hv N
    R₁ ≃ₐ[Q₀] MvPolynomial (σ × ℕ) Q₁ := by
  letI := deltaDivisionFiniteNormalizedStepAlgebra D d a v N
  letI := deltaDivisionFiniteJetTargetAlgebra D hpA hpL hg d a v hv N
  apply AlgEquiv.ofRingEquiv (f := deltaDivisionFiniteJetStepTargetEquiv D hpA hpL hg d a v hv N)
  intro c
  exact (deltaDivisionFiniteJetStepTargetEquiv D hpA hpL hg d a v hv N).apply_symm_apply _

/-- 元の下位商は標準前段正規化商射により自由。 -/
theorem deltaDivisionFiniteJetSource_moduleFree :
    letI := deltaDivisionFiniteJetSourceAlgebra D hpA hpL hg d a v hv N
    Module.Free Q₀ R₀ := by
  let := deltaDivisionNormalizedStepSourceAlgebra D d a v N
  let := deltaDivisionFiniteJetSourceAlgebra D hpA hpL hg d a v hv N
  let := deltaDivisionNormalizedStepSource_moduleFree D d a v N
  let : Module.Free Q₀ (MvPolynomial (σ × ℕ) S₀) :=
    Module.Free.of_equiv ((MvPolynomial.basisMonomials (σ × ℕ) S₀).repr.restrictScalars Q₀).symm
  exact Module.Free.of_equiv
    (deltaDivisionFiniteJetSourceAlgEquiv D hpA hpL hg d a v hv N).symm.toLinearEquiv

/-- 元の次段商も標準前段正規化商射により自由。 -/
theorem deltaDivisionFiniteJetTarget_moduleFree :
    letI := deltaDivisionFiniteJetTargetAlgebra D hpA hpL hg d a v hv N
    Module.Free Q₀ R₁ := by
  let := deltaDivisionFiniteNormalizedStepAlgebra D d a v N
  let := deltaDivisionFiniteJetTargetAlgebra D hpA hpL hg d a v hv N
  let := deltaDivisionFiniteNormalizedStep_moduleFree D d a v N
  let : Module.Free Q₀ (MvPolynomial (σ × ℕ) Q₁) :=
    Module.Free.of_equiv ((MvPolynomial.basisMonomials (σ × ℕ) Q₁).repr.restrictScalars Q₀).symm
  exact Module.Free.of_equiv
    (deltaDivisionFiniteJetTargetAlgEquiv D hpA hpL hg d a v hv N).symm.toLinearEquiv

/-- 元の下位商は標準係数射で前段正規化商上平坦。 -/
theorem deltaDivisionFiniteJetSource_moduleFlat :
    letI := deltaDivisionFiniteJetSourceAlgebra D hpA hpL hg d a v hv N
    Module.Flat Q₀ R₀ := by
  let := deltaDivisionFiniteJetSourceAlgebra D hpA hpL hg d a v hv N
  let := deltaDivisionFiniteJetSource_moduleFree D hpA hpL hg d a v hv N
  infer_instance

/-- 元の次段商も標準係数射で前段正規化商上平坦。 -/
theorem deltaDivisionFiniteJetTarget_moduleFlat :
    letI := deltaDivisionFiniteJetTargetAlgebra D hpA hpL hg d a v hv N
    Module.Flat Q₀ R₁ := by
  let := deltaDivisionFiniteJetTargetAlgebra D hpA hpL hg d a v hv N
  let := deltaDivisionFiniteJetTarget_moduleFree D hpA hpL hg d a v hv N
  infer_instance

/-- 前段正規化商・元の下位商・元の次段商の標準スカラー塔。 -/
theorem deltaDivisionFiniteJetStep_isScalarTower :
    letI := deltaDivisionFiniteJetSourceAlgebra D hpA hpL hg d a v hv N
    letI := deltaDivisionFiniteJetTargetAlgebra D hpA hpL hg d a v hv N
    letI := deltaDivisionFiniteJetStepAlgebra D d a N
    IsScalarTower Q₀ R₀ R₁ := by
  let := deltaDivisionFiniteJetSourceAlgebra D hpA hpL hg d a v hv N
  let := deltaDivisionFiniteJetTargetAlgebra D hpA hpL hg d a v hv N
  let := deltaDivisionFiniteJetStepAlgebra D d a N
  exact IsScalarTower.of_algebraMap_eq'
    (deltaDivisionFiniteJetStepMap_comp_coefficient D hpA hpL hg d a v hv N).symm

end SerrePositivity.BhattScholze
