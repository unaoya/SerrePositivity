module

public import SerrePositivity.BhattScholze.Delta.Division.DeltaDivisionSourceTensor
public import SerrePositivity.BhattScholze.RootedExtension.Division.DeltaAdjoinDivisionResiduePresentation
public import Mathlib.RingTheory.TensorProduct.Quotient

/-! # 実残余自由δ射の通常テンソルとraw(p,d)商

既存の通常pushout比較と標準テンソル商比較を合成する。
完備化・Tor消滅・対象残余商のδ構造は要求しない。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open scoped TensorProduct
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (d : A) (c : σ → A)
local notation "P₀" => RelativeFreeDeltaRing (R := A) σ
local notation "I₀" => Ideal.span {(p : P₀), MvPolynomial.C d}
local notation "Q₀" => P₀ ⧸ I₀
local notation "B₀" => DeltaAdjoinDivision D d c
local notation "R₀" => DeltaAdjoinDivisionResidue D d c
local notation "j₀" => deltaAdjoinDivisionMap D d c
local notation "q₀" => Ideal.Quotient.mk
  (DeltaStructure.deltaClosure (relativeFreeDeltaStructure σ D) (deltaDivisionRelationIdeal d c))

/-- 実残余自由δ射による源作用。標準商代数構造を既存のα作用から誘導する。 -/
@[instance_reducible] def deltaDivisionSourceResidueTargetAlgebra : Algebra P₀ Q₀ := by
  letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
  letI : Module P₀ P₀ := Algebra.toModule
  infer_instance

/-- 実残余源作用の係数射は、標準商射と自由δ射αの合成そのもの。 -/
theorem deltaDivisionSourceResidueTargetAlgebra_algebraMap :
    letI := deltaDivisionSourceResidueTargetAlgebra (σ := σ) D d
    letI : Module P₀ Q₀ := Algebra.toModule
    algebraMap P₀ Q₀ = (Ideal.Quotient.mk I₀).comp
      (deltaDivisionSourceMap (σ := σ) D d) := rfl

/-- 通常pushout比較の下で、右因子の(p,Cd)イデアルはraw包の実(p,d)イデアルとなる。 -/
theorem deltaDivisionSourceTensor_residueIdeal_map :
    letI := deltaDivisionSourceEvaluationAlgebra D c
    letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
    letI : Module P₀ P₀ := Algebra.toModule
    ((I₀).map (Algebra.TensorProduct.includeRight (R := P₀) (A := A) (B := P₀)).toRingHom).map
      (deltaDivisionSourceTensorEquiv D d c).toRingHom = deltaAdjoinDivisionResidueIdeal D d c := by
  let := deltaDivisionSourceEvaluationAlgebra D c
  let := deltaDivisionSourceTargetAlgebra (σ := σ) D d
  let : Module P₀ P₀ := Algebra.toModule
  rw [Ideal.map_map]
  have he : (deltaDivisionSourceTensorEquiv D d c).toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := P₀) (A := A) (B := P₀)).toRingHom = q₀ := by
    apply RingHom.ext
    intro r
    change deltaDivisionSourceTensorEquiv D d c (1 ⊗ₜ[P₀] r) = q₀ r
    rw [deltaDivisionSourceTensorEquiv_tmul, map_one, one_mul]
  rw [he]
  exact (deltaAdjoinDivisionResidueIdeal_eq_map D d c).symm

/-- 実残余通常テンソルは、既存rawδ包の実(p,d)商と標準的に環同型。 -/
def deltaDivisionSourceResidueTensorEquiv :
    letI := deltaDivisionSourceEvaluationAlgebra D c
    letI := deltaDivisionSourceResidueTargetAlgebra (σ := σ) D d
    letI : Module P₀ Q₀ := Algebra.toModule
    A ⊗[P₀] Q₀ ≃+* R₀ := by
  letI := deltaDivisionSourceEvaluationAlgebra D c
  letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
  letI : Module P₀ P₀ := Algebra.toModule
  letI := deltaDivisionSourceResidueTargetAlgebra (σ := σ) D d
  letI : Module P₀ Q₀ := Algebra.toModule
  exact (Algebra.TensorProduct.tensorQuotientEquiv (R := P₀) A P₀ A I₀).toRingEquiv.trans
    (Ideal.quotientEquiv _ _ (deltaDivisionSourceTensorEquiv D d c)
      (deltaDivisionSourceTensor_residueIdeal_map D d c).symm)

/-- 残余テンソル比較は、各純テンソルを標準基底像と標準商像の積へ送る。 -/
theorem deltaDivisionSourceResidueTensorEquiv_tmul (a : A) (r : P₀) :
    letI := deltaDivisionSourceEvaluationAlgebra D c
    letI := deltaDivisionSourceResidueTargetAlgebra (σ := σ) D d
    letI : Module P₀ Q₀ := Algebra.toModule
    deltaDivisionSourceResidueTensorEquiv D d c (a ⊗ₜ[P₀] Ideal.Quotient.mk I₀ r) =
      Ideal.Quotient.mk (deltaAdjoinDivisionResidueIdeal D d c) (j₀ a * q₀ r) := by
  let := deltaDivisionSourceEvaluationAlgebra D c
  let := deltaDivisionSourceTargetAlgebra (σ := σ) D d
  let : Module P₀ P₀ := Algebra.toModule
  let := deltaDivisionSourceResidueTargetAlgebra (σ := σ) D d
  let : Module P₀ Q₀ := Algebra.toModule
  change Ideal.Quotient.mk (deltaAdjoinDivisionResidueIdeal D d c)
    (deltaDivisionSourceTensorEquiv D d c (a ⊗ₜ[P₀] r)) = _
  rw [deltaDivisionSourceTensorEquiv_tmul]

/-- 実残余テンソル比較は元の係数A作用を保つ。 -/
def deltaDivisionSourceResidueTensorAlgEquiv :
    letI := deltaDivisionSourceEvaluationAlgebra D c
    letI := deltaDivisionSourceResidueTargetAlgebra (σ := σ) D d
    letI : Module P₀ Q₀ := Algebra.toModule
    A ⊗[P₀] Q₀ ≃ₐ[A] R₀ := by
  letI := deltaDivisionSourceEvaluationAlgebra D c
  letI := deltaDivisionSourceResidueTargetAlgebra (σ := σ) D d
  letI : Module P₀ Q₀ := Algebra.toModule
  apply AlgEquiv.ofRingEquiv (f := deltaDivisionSourceResidueTensorEquiv D d c)
  intro a
  change deltaDivisionSourceResidueTensorEquiv D d c (a ⊗ₜ[P₀] 1) =
    Ideal.Quotient.mk (deltaAdjoinDivisionResidueIdeal D d c) (j₀ a)
  have h := deltaDivisionSourceResidueTensorEquiv_tmul D d c a 1
  simpa only [map_one, mul_one] using h

end SerrePositivity.BhattScholze
