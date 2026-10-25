module

public import SerrePositivity.BhattScholze.RootedExtension.Division.DeltaPDivisionSourceTensor
public import SerrePositivity.BhattScholze.RootedExtension.Division.DeltaPDivisionRawRegular

/-! # 実通常テンソルのp正則性と旧ねじれ商の標準比較

raw包の既存正則性と標準比較同型を利用する。G7やCFFを仮定した結論ではない。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open scoped TensorProduct
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (y : A)
variable (hpA : Function.Injective (fun x : A => (p : A) * x))
variable (hg : Function.Injective (WittVector.ghostMap :
  WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
variable (v : Aˣ) (hv : (v : A) = D.delta (p : A))
variable (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
  (Ideal.Quotient.mk (Ideal.span {(p : A)}) y))
local notation "P₀" => RelativeFreeDeltaRing (R := A) σ
local notation "a₀" => fun _ : σ ↦ D.frobeniusLift y
local notation "q₀" => Ideal.Quotient.mk
  (DeltaStructure.deltaClosure (relativeFreeDeltaStructure σ D)
    (deltaDivisionRelationIdeal (p : A) a₀))
include hpA hg hv hy

/-- 正則一元入力では、実自由δ射の通常テンソル積にpねじれがない。 -/
theorem deltaPDivisionSourceTensor_p_mul_injective :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    Function.Injective (fun x : A ⊗[P₀] P₀ => (p : A ⊗[P₀] P₀) * x) := by
  let := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  let := deltaPDivisionSourceTargetAlgebra (σ := σ) D
  let : Module P₀ P₀ := Algebra.toModule
  let e := deltaPDivisionSourceTensorEquiv (σ := σ) D y
  have hp := deltaPDivisionRaw_p_mul_injective (σ := σ) D y hpA hg v hv hy
  intro x z hxz
  apply e.injective
  apply hp
  have h := congrArg e hxz
  simpa only [map_mul, map_natCast] using h

/-- 実通常テンソル積と、実導来完備化の既存入力となる旧ねじれ除去商との環同型。 -/
def deltaPDivisionSourceTensorTorsionEquiv :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    A ⊗[P₀] P₀ ≃+* DeltaDivisionTorsionQuotient D (p : A) a₀ := by
  letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
  letI : Module P₀ P₀ := Algebra.toModule
  exact (deltaPDivisionSourceTensorEquiv D y).trans
    (deltaPDivisionRawTorsionEquiv (σ := σ) D y hpA hg v hv hy)

/-- 実通常テンソルと旧ねじれ商の同型は、両因子の標準像を保つ。 -/
theorem deltaPDivisionSourceTensorTorsionEquiv_tmul (a : A) (b : P₀) :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    deltaPDivisionSourceTensorTorsionEquiv D y hpA hg v hv hy (a ⊗ₜ[P₀] b) =
      deltaDivisionTorsionMap D (p : A) a₀ a * Ideal.Quotient.mk _ (q₀ b) := by
  let := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  let := deltaPDivisionSourceTargetAlgebra (σ := σ) D
  let : Module P₀ P₀ := Algebra.toModule
  rw [deltaPDivisionSourceTensorTorsionEquiv, RingEquiv.trans_apply,
    deltaPDivisionSourceTensorEquiv_tmul, map_mul,
    deltaPDivisionRawTorsionEquiv_apply, deltaPDivisionRawTorsionEquiv_apply]
  rfl

/-- 実通常テンソルから旧ねじれ商への比較は、元の基底Aの標準射を保つ。 -/
theorem deltaPDivisionSourceTensorTorsionEquiv_comp_base :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    (deltaPDivisionSourceTensorTorsionEquiv D y hpA hg v hv hy).toRingHom.comp
      Algebra.TensorProduct.includeLeftRingHom = deltaDivisionTorsionMap D (p : A) a₀ := by
  let := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  let := deltaPDivisionSourceTargetAlgebra (σ := σ) D
  let : Module P₀ P₀ := Algebra.toModule
  apply RingHom.ext
  intro a
  change deltaPDivisionSourceTensorTorsionEquiv D y hpA hg v hv hy (a ⊗ₜ[P₀] 1) = _
  rw [deltaPDivisionSourceTensorTorsionEquiv_tmul, map_one, map_one, mul_one]

end SerrePositivity.BhattScholze
