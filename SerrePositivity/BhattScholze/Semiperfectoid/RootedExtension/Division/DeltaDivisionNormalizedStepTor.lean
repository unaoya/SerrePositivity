module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.Division.DeltaDivisionNormalizedStepResolution
public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.Division.DeltaDivisionFiniteNormalizedStepFlat
public import SerrePositivity.HomologicalAlgebra.TorFlatBaseChangeVanishing

/-! # 実正規化一段の標準スカラー塔と係数拡大加群に対するTor消滅

この計算には添字集合の有限性は不要。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (a : σ → A) (v : Aˣ) (N : ℕ)
local notation "Q₀" => DeltaDivisionFiniteNormalizedQuotient D d a v N
local notation "Q₁" => DeltaDivisionFiniteNormalizedQuotient D d a v (N + 1)
local notation "R₀" =>
  MvPolynomial (σ × Fin (N + 2)) A ⧸ deltaDivisionNormalizedStepSourceIdeal D d a v N

/-- 前段商から実源商への標準係数射。 -/
def deltaDivisionNormalizedStepSourceCoefficientMap : Q₀ →+* R₀ :=
  (deltaDivisionNormalizedStepSourceQuotientEquiv D d a v N).symm.toRingHom.comp MvPolynomial.C

/-- 標準係数射は元の下位多項式の包含像と一致する。 -/
theorem deltaDivisionNormalizedStepSourceCoefficientMap_mk
    (f : MvPolynomial (σ × Fin (N + 1)) A) :
    deltaDivisionNormalizedStepSourceCoefficientMap D d a v N (Ideal.Quotient.mk _ f) =
      Ideal.Quotient.mk _ (relativeFreeFiniteStepInclusion N σ f) := by
  apply (deltaDivisionNormalizedStepSourceQuotientEquiv D d a v N).injective
  change (deltaDivisionNormalizedStepSourceQuotientEquiv D d a v N)
    ((deltaDivisionNormalizedStepSourceQuotientEquiv D d a v N).symm _) = _
  rw [RingEquiv.apply_symm_apply, deltaDivisionNormalizedStepSourceQuotientEquiv_mk,
    deltaDivisionNormalizedStepPolynomialMap_inclusion]

/-- 実源商を経由する標準射は既存の標準一段射に一致する。 -/
theorem deltaDivisionNormalizedStepNextMap_comp_coefficient :
    (deltaDivisionNormalizedStepNextMap D d a v N).comp
      (deltaDivisionNormalizedStepSourceCoefficientMap D d a v N) =
      deltaDivisionFiniteNormalizedStepMap D d a v N := by
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro f
  change deltaDivisionNormalizedStepNextMap D d a v N
    (deltaDivisionNormalizedStepSourceCoefficientMap D d a v N (Ideal.Quotient.mk _ f)) =
    deltaDivisionFiniteNormalizedStepMap D d a v N (Ideal.Quotient.mk _ f)
  rw [deltaDivisionNormalizedStepSourceCoefficientMap_mk,
    deltaDivisionNormalizedStepNextMap_mk, deltaDivisionFiniteNormalizedStepMap_mk]

/-- 実源商の標準前段商代数構造。 -/
@[instance_reducible] def deltaDivisionNormalizedStepSourceAlgebra : Algebra Q₀ R₀ :=
  (deltaDivisionNormalizedStepSourceCoefficientMap D d a v N).toAlgebra

/-- 実源商の多項式表示は標準前段商代数同型。 -/
def deltaDivisionNormalizedStepSourceAlgEquiv :
    letI := deltaDivisionNormalizedStepSourceAlgebra D d a v N
    R₀ ≃ₐ[Q₀] MvPolynomial σ Q₀ := by
  letI := deltaDivisionNormalizedStepSourceAlgebra D d a v N
  apply AlgEquiv.ofRingEquiv (f := deltaDivisionNormalizedStepSourceQuotientEquiv D d a v N)
  intro c
  exact (deltaDivisionNormalizedStepSourceQuotientEquiv D d a v N).apply_symm_apply _

/-- 実源商は標準前段商射により自由。 -/
theorem deltaDivisionNormalizedStepSource_moduleFree :
    letI := deltaDivisionNormalizedStepSourceAlgebra D d a v N
    Module.Free Q₀ R₀ := by
  let := deltaDivisionNormalizedStepSourceAlgebra D d a v N
  exact Module.Free.of_equiv
    (deltaDivisionNormalizedStepSourceAlgEquiv D d a v N).symm.toLinearEquiv

/-- 実源商は標準前段商射により平坦。 -/
theorem deltaDivisionNormalizedStepSource_moduleFlat :
    letI := deltaDivisionNormalizedStepSourceAlgebra D d a v N
    Module.Flat Q₀ R₀ := by
  let := deltaDivisionNormalizedStepSourceAlgebra D d a v N
  let := deltaDivisionNormalizedStepSource_moduleFree D d a v N
  infer_instance

/-- 前段商・実源商・次段商の標準射はスカラー塔を構成する。 -/
theorem deltaDivisionNormalizedStep_isScalarTower :
    letI := deltaDivisionNormalizedStepSourceAlgebra D d a v N
    letI := deltaDivisionNormalizedStepNextAlgebra D d a v N
    letI := deltaDivisionFiniteNormalizedStepAlgebra D d a v N
    IsScalarTower Q₀ R₀ Q₁ := by
  let := deltaDivisionNormalizedStepSourceAlgebra D d a v N
  let := deltaDivisionNormalizedStepNextAlgebra D d a v N
  let := deltaDivisionFiniteNormalizedStepAlgebra D d a v N
  exact IsScalarTower.of_algebraMap_eq'
    (deltaDivisionNormalizedStepNextMap_comp_coefficient D d a v N).symm

/-- 任意前段商加群の係数拡大に対し、実源商上の次段実商の高次Torは零。 -/
theorem deltaDivisionNormalizedStep_tor_subsingleton
    (M : Type u) [AddCommGroup M] [Module Q₀ M] (i : ℕ) :
    letI := deltaDivisionNormalizedStepSourceAlgebra D d a v N
    letI := deltaDivisionNormalizedStepNextAlgebra D d a v N
    letI := deltaDivisionFiniteNormalizedStepAlgebra D d a v N
    Subsingleton (TorModule R₀ (i + 1) Q₁ (TensorProduct Q₀ R₀ M)) := by
  let := deltaDivisionNormalizedStepSourceAlgebra D d a v N
  let := deltaDivisionNormalizedStepNextAlgebra D d a v N
  let := deltaDivisionFiniteNormalizedStepAlgebra D d a v N
  let := deltaDivisionNormalizedStepSource_moduleFlat D d a v N
  let := deltaDivisionNormalizedStep_isScalarTower D d a v N
  let := deltaDivisionFiniteNormalizedStep_moduleFaithfullyFlat D d a v N
  exact torModule_baseChange_subsingleton Q₀ R₀ Q₁ M (i + 1)
    (torModule_subsingleton_of_flat Q₁ M i)

/-- 同じ実導来テンソルは次数零に集中する。 -/
theorem deltaDivisionNormalizedStep_derivedTensor_concentrated
    (M : Type u) [AddCommGroup M] [Module Q₀ M] :
    letI := deltaDivisionNormalizedStepSourceAlgebra D d a v N
    letI := deltaDivisionNormalizedStepNextAlgebra D d a v N
    letI := deltaDivisionFiniteNormalizedStepAlgebra D d a v N
    IsConcentratedInDegreeZero (derivedTensor R₀ Q₁ (TensorProduct Q₀ R₀ M)) := by
  let := deltaDivisionNormalizedStepSourceAlgebra D d a v N
  let := deltaDivisionNormalizedStepNextAlgebra D d a v N
  let := deltaDivisionFiniteNormalizedStepAlgebra D d a v N
  rw [isConcentratedInDegreeZero_derivedTensor_iff]
  intro i hi
  cases i with
  | zero => exact (Nat.lt_irrefl 0 hi).elim
  | succ i => exact deltaDivisionNormalizedStep_tor_subsingleton D d a v N M i

variable [Fintype σ]
local notation "g" => fun i : Fin (Fintype.card σ) ↦
  Ideal.Quotient.mk (deltaDivisionNormalizedStepSourceIdeal D d a v N)
    (deltaDivisionWittNormalizedPolynomial D d a v (Equiv.symm (Fintype.equivFin σ) i) N)

/-- 有限最高段の実Koszulホモロジーと、実際の次段商のTorとの比較。 -/
def deltaDivisionNormalizedStepKoszulTorIso
    (M : Type u) [AddCommGroup M] [Module Q₀ M] (i : ℕ) :
    letI := deltaDivisionNormalizedStepSourceAlgebra D d a v N
    letI := deltaDivisionNormalizedStepNextAlgebra D d a v N
    letI := deltaDivisionFiniteNormalizedStepAlgebra D d a v N
    ModuleCat.of R₀ (TorModule R₀ i Q₁ (TensorProduct Q₀ R₀ M)) ≅
      ((koszulModuleFunctor g).obj
        (ModuleCat.of R₀ (TensorProduct Q₀ R₀ M))).homology (-(i : ℤ)) := by
  letI := deltaDivisionNormalizedStepSourceAlgebra D d a v N
  letI := deltaDivisionNormalizedStepNextAlgebra D d a v N
  letI := deltaDivisionFiniteNormalizedStepAlgebra D d a v N
  exact torModuleIsoCochainLeft (TensorProduct Q₀ R₀ M)
    (deltaDivisionNormalizedStepResolution D d a v N) i ≪≫
    (HomologicalComplex.homologyFunctor _ _ (-(i : ℤ))).mapIso
      (koszulTensorConeIso g (ModuleCat.of R₀ (TensorProduct Q₀ R₀ M)))

/-- 任意前段商加群を係数拡大した実最高段Koszul複体の負次ホモロジーは零。 -/
theorem deltaDivisionNormalizedStepKoszulHomology_isZero
    (M : Type u) [AddCommGroup M] [Module Q₀ M] (i : ℕ) :
    letI := deltaDivisionNormalizedStepSourceAlgebra D d a v N
    letI := deltaDivisionNormalizedStepNextAlgebra D d a v N
    letI := deltaDivisionFiniteNormalizedStepAlgebra D d a v N
    IsZero (((koszulModuleFunctor g).obj
      (ModuleCat.of R₀ (TensorProduct Q₀ R₀ M))).homology (-((i + 1 : ℕ) : ℤ))) := by
  let := deltaDivisionNormalizedStepSourceAlgebra D d a v N
  let := deltaDivisionNormalizedStepNextAlgebra D d a v N
  let := deltaDivisionFiniteNormalizedStepAlgebra D d a v N
  let := deltaDivisionNormalizedStep_tor_subsingleton D d a v N M i
  exact IsZero.of_iso (ModuleCat.isZero_of_subsingleton _)
    (deltaDivisionNormalizedStepKoszulTorIso D d a v N M (i + 1)).symm

end SerrePositivity.BhattScholze
