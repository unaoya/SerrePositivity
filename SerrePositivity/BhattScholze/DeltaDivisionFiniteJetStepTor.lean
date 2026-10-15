module

public import SerrePositivity.BhattScholze.DeltaDivisionFiniteJetStepScalarTower

/-! # 元のδ段間射の係数拡大加群に対する実Tor・Koszul計算 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A)
variable (hpA : Function.Injective (fun z : A ↦ (p : A) * z))
variable (hpL : Function.Injective (fun z : RelativeFreeDeltaRing (R := A) σ ↦
  (p : RelativeFreeDeltaRing (R := A) σ) * z))
variable (hg : Function.Injective (WittVector.ghostMap :
  WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
variable (d : A) (a : σ → A) (v : Aˣ) (hv : (v : A) = D.delta d) (N : ℕ)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "I₀" => Ideal.span {(p : L₀), MvPolynomial.C d} ⊔
  deltaDivisionFiniteRelationIdeal D d a (N + 1)
local notation "R₀" => L₀ ⧸ I₀
local notation "R₁" => L₀ ⧸ (Ideal.span {(p : L₀), MvPolynomial.C d} ⊔
  deltaDivisionFiniteRelationIdeal D d a (N + 2))
local notation "Q₀" => DeltaDivisionFiniteNormalizedQuotient D d a v N

/-- 任意前段正規化商加群の係数拡大に対し、元の段間射の高次Torは零。 -/
theorem deltaDivisionFiniteJetStep_tor_subsingleton
    (M : Type u) [AddCommGroup M] [Module Q₀ M] (i : ℕ) :
    letI := deltaDivisionFiniteJetSourceAlgebra D hpA hpL hg d a v hv N
    letI := deltaDivisionFiniteJetTargetAlgebra D hpA hpL hg d a v hv N
    letI := deltaDivisionFiniteJetStepAlgebra D d a N
    Subsingleton (TorModule R₀ (i + 1) R₁ (TensorProduct Q₀ R₀ M)) := by
  let := deltaDivisionFiniteJetSourceAlgebra D hpA hpL hg d a v hv N
  let := deltaDivisionFiniteJetTargetAlgebra D hpA hpL hg d a v hv N
  let := deltaDivisionFiniteJetStepAlgebra D d a N
  let := deltaDivisionFiniteJetSource_moduleFlat D hpA hpL hg d a v hv N
  let := deltaDivisionFiniteJetTarget_moduleFlat D hpA hpL hg d a v hv N
  let := deltaDivisionFiniteJetStep_isScalarTower D hpA hpL hg d a v hv N
  exact torModule_baseChange_subsingleton Q₀ R₀ R₁ M (i + 1)
    (torModule_subsingleton_of_flat R₁ M i)

/-- 同じ元の実導来テンソルは次数零に集中する。添字集合の有限性は不要。 -/
theorem deltaDivisionFiniteJetStep_derivedTensor_concentrated
    (M : Type u) [AddCommGroup M] [Module Q₀ M] :
    letI := deltaDivisionFiniteJetSourceAlgebra D hpA hpL hg d a v hv N
    letI := deltaDivisionFiniteJetTargetAlgebra D hpA hpL hg d a v hv N
    letI := deltaDivisionFiniteJetStepAlgebra D d a N
    IsConcentratedInDegreeZero (derivedTensor R₀ R₁ (TensorProduct Q₀ R₀ M)) := by
  let := deltaDivisionFiniteJetSourceAlgebra D hpA hpL hg d a v hv N
  let := deltaDivisionFiniteJetTargetAlgebra D hpA hpL hg d a v hv N
  let := deltaDivisionFiniteJetStepAlgebra D d a N
  rw [isConcentratedInDegreeZero_derivedTensor_iff]
  intro i hi
  cases i with
  | zero => exact (Nat.lt_irrefl 0 hi).elim
  | succ i => exact deltaDivisionFiniteJetStep_tor_subsingleton D hpA hpL hg d a v hv N M i

variable [Fintype σ]
local notation "g" => fun i : Fin (Fintype.card σ) ↦ Ideal.Quotient.mk I₀
  (deltaDivisionIteratedRelation D d a (Equiv.symm (Fintype.equivFin σ) i) (N + 2))

/-- 元の有限δ関係の実Koszulホモロジーと実次段商のTorとの比較。 -/
def deltaDivisionFiniteJetStepKoszulTorIso
    (M : Type u) [AddCommGroup M] [Module Q₀ M] (i : ℕ) :
    letI := deltaDivisionFiniteJetSourceAlgebra D hpA hpL hg d a v hv N
    letI := deltaDivisionFiniteJetTargetAlgebra D hpA hpL hg d a v hv N
    letI := deltaDivisionFiniteJetStepAlgebra D d a N
    ModuleCat.of R₀ (TorModule R₀ i R₁ (TensorProduct Q₀ R₀ M)) ≅
      ((koszulModuleFunctor g).obj
        (ModuleCat.of R₀ (TensorProduct Q₀ R₀ M))).homology (-(i : ℤ)) := by
  letI := deltaDivisionFiniteJetSourceAlgebra D hpA hpL hg d a v hv N
  letI := deltaDivisionFiniteJetTargetAlgebra D hpA hpL hg d a v hv N
  letI := deltaDivisionFiniteJetStepAlgebra D d a N
  exact torModuleIsoCochainLeft (TensorProduct Q₀ R₀ M)
    (deltaDivisionFiniteJetStepResolution D hpA hpL hg d a v hv N) i ≪≫
    (HomologicalComplex.homologyFunctor _ _ (-(i : ℤ))).mapIso
      (koszulTensorConeIso g (ModuleCat.of R₀ (TensorProduct Q₀ R₀ M)))

/-- 任意係数加群の拡大上で元の全同段δ関係の負次Koszulホモロジーは零。 -/
theorem deltaDivisionFiniteJetStepKoszulHomology_isZero
    (M : Type u) [AddCommGroup M] [Module Q₀ M] (i : ℕ) :
    letI := deltaDivisionFiniteJetSourceAlgebra D hpA hpL hg d a v hv N
    letI := deltaDivisionFiniteJetTargetAlgebra D hpA hpL hg d a v hv N
    letI := deltaDivisionFiniteJetStepAlgebra D d a N
    IsZero (((koszulModuleFunctor g).obj
      (ModuleCat.of R₀ (TensorProduct Q₀ R₀ M))).homology (-((i + 1 : ℕ) : ℤ))) := by
  let := deltaDivisionFiniteJetSourceAlgebra D hpA hpL hg d a v hv N
  let := deltaDivisionFiniteJetTargetAlgebra D hpA hpL hg d a v hv N
  let := deltaDivisionFiniteJetStepAlgebra D d a N
  let := deltaDivisionFiniteJetStep_tor_subsingleton D hpA hpL hg d a v hv N M i
  exact IsZero.of_iso (ModuleCat.isZero_of_subsingleton _)
    (deltaDivisionFiniteJetStepKoszulTorIso D hpA hpL hg d a v hv N M (i + 1)).symm

end SerrePositivity.BhattScholze
