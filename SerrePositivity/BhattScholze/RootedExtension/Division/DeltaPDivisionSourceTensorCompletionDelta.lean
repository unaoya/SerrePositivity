module

public import SerrePositivity.BhattScholze.RootedExtension.Division.DeltaPDivisionSourceTensorDelta
public import SerrePositivity.BhattScholze.RootedExtension.Division.DeltaPDivisionSourceTensorCompletion

/-! # 実通常テンソルの実導来完備化H⁰と標準比較のδ両立

実H⁰の既存δ延長と環射の普遍性を用いる。
原典の導来δpushout比較・分冪包比較・CFFはここでは結論しない。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (y : A)
local notation "P₀" => RelativeFreeDeltaRing (R := A) σ
local notation "R₀" => TensorProduct P₀ A P₀
local notation "a₀" => fun _ : σ ↦ D.frobeniusLift y
local notation "U₀" => DeltaDivisionTorsionQuotient D (p : A) a₀
local notation "d₀" => deltaDivisionTorsionMap D (p : A) a₀ (p : A)
local notation "C₀" => DerivedDeltaDivisionCompletion D (p : A) a₀
local notation "H₀" => PDCompletionH0 R₀ p (p : R₀)

/-- 実通常テンソルの実(p,p)導来完備化H⁰上の、既存の標準δ延長。 -/
def deltaPDivisionSourceTensorCompletionDelta :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    letI := pdCompletionCommRing R₀ p (p : R₀)
    DeltaStructure p H₀ := by
  letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
  letI : Module P₀ P₀ := Algebra.toModule
  exact deltaPDCompletionStructure (deltaPDivisionSourceTensorDelta (σ := σ) D y) (p : R₀)

/-- 元の基底から通常テンソルの実導来完備化H⁰への標準射はδ射。 -/
theorem deltaPDivisionSourceTensorCompletion_base_isDeltaHom :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    letI := pdCompletionCommRing R₀ p (p : R₀)
    D.IsDeltaHom (deltaPDivisionSourceTensorCompletionDelta (σ := σ) D y)
      ((pdCompletionUnit R₀ p (p : R₀)).comp Algebra.TensorProduct.includeLeftRingHom) := by
  let := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  let := deltaPDivisionSourceTargetAlgebra (σ := σ) D
  let : Module P₀ P₀ := Algebra.toModule
  let := pdCompletionCommRing R₀ p (p : R₀)
  exact (pdCompletionUnit_isDeltaHom
    (deltaPDivisionSourceTensorDelta (σ := σ) D y) (p : R₀)).comp
      (deltaPDivisionSourceTensor_includeLeft_isDeltaHom (σ := σ) D y)

variable [Unique σ]
variable (hpA : Function.Injective (fun x : A => (p : A) * x))
variable (hg : Function.Injective (WittVector.ghostMap :
  WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
variable (v : Aˣ) (hv : (v : A) = D.delta (p : A))
variable (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
  (Ideal.Quotient.mk (Ideal.span {(p : A)}) y))
include hpA hg hv hy

/-- 正則一元入力の通常テンソルと旧ねじれ商の標準比較は両方向にδ射。 -/
theorem deltaPDivisionSourceTensorTorsionEquiv_isDeltaHom :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    (deltaPDivisionSourceTensorDelta (σ := σ) D y).IsDeltaHom
        (deltaDivisionTorsionStructure D (p : A) a₀)
        (deltaPDivisionSourceTensorTorsionEquiv D y hpA hg v hv hy).toRingHom ∧
      (deltaDivisionTorsionStructure D (p : A) a₀).IsDeltaHom
        (deltaPDivisionSourceTensorDelta (σ := σ) D y)
        (deltaPDivisionSourceTensorTorsionEquiv D y hpA hg v hv hy).symm.toRingHom := by
  let := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  let := deltaPDivisionSourceTargetAlgebra (σ := σ) D
  let : Module P₀ P₀ := Algebra.toModule
  have h := deltaPDivisionRawTorsionEquiv_isDeltaHom (σ := σ) D y hpA hg v hv hy
  exact ⟨h.1.comp (deltaPDivisionSourceTensorEquiv_isDeltaHom (σ := σ) D y),
    (deltaPDivisionSourceTensorEquiv_symm_isDeltaHom (σ := σ) D y).comp h.2⟩

/-- 実導来完備化H⁰の標準比較同型は、両側の既存の標準δ延長と両立する。 -/
theorem deltaPDivisionSourceTensorCompletionEquiv_isDeltaHom :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    letI := pdCompletionCommRing R₀ p (p : R₀)
    letI := derivedDeltaDivisionCommRing D (p : A) a₀
    (deltaPDivisionSourceTensorCompletionDelta (σ := σ) D y).IsDeltaHom
      (derivedDeltaDivisionStructure D (p : A) a₀)
      (deltaPDivisionSourceTensorCompletionEquiv D y hpA hg v hv hy).toRingHom := by
  let := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  let := deltaPDivisionSourceTargetAlgebra (σ := σ) D
  let : Module P₀ P₀ := Algebra.toModule
  let := pdCompletionCommRing R₀ p (p : R₀)
  let := derivedDeltaDivisionCommRing D (p : A) a₀
  let g := (pdCompletionUnit U₀ p d₀).comp
    (deltaPDivisionSourceTensorTorsionEquiv D y hpA hg v hv hy).toRingHom
  have hgδ := (pdCompletionUnit_isDeltaHom (deltaDivisionTorsionStructure D (p : A) a₀)
    d₀).comp (deltaPDivisionSourceTensorTorsionEquiv_isDeltaHom D y hpA hg v hv hy).1
  have hpC := pdCompletionH0_self_complete_p U₀ p d₀
  have hdC : IsModuleComplete C₀ (g (p : R₀)) (ModuleCat.of C₀ C₀) := by
    simpa only [map_natCast] using hpC
  exact pdCompletionRingHom_isDeltaHom (deltaPDivisionSourceTensorDelta (σ := σ) D y)
    (p : R₀) (derivedDeltaDivisionStructure D (p : A) a₀) g hgδ hpC hdC
      (deltaPDivisionSourceTensorCompletionEquiv D y hpA hg v hv hy).toRingHom
      (deltaPDivisionSourceTensorCompletionEquiv_comp_unit D y hpA hg v hv hy)

/-- 実導来完備化H⁰の標準逆同型もδ射。 -/
theorem deltaPDivisionSourceTensorCompletionEquiv_symm_isDeltaHom :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    letI := pdCompletionCommRing R₀ p (p : R₀)
    letI := derivedDeltaDivisionCommRing D (p : A) a₀
    (derivedDeltaDivisionStructure D (p : A) a₀).IsDeltaHom
      (deltaPDivisionSourceTensorCompletionDelta (σ := σ) D y)
      (deltaPDivisionSourceTensorCompletionEquiv D y hpA hg v hv hy).symm.toRingHom := by
  let := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  let := deltaPDivisionSourceTargetAlgebra (σ := σ) D
  let : Module P₀ P₀ := Algebra.toModule
  let := pdCompletionCommRing R₀ p (p : R₀)
  let := derivedDeltaDivisionCommRing D (p : A) a₀
  let e := deltaPDivisionSourceTensorCompletionEquiv D y hpA hg v hv hy
  intro r
  apply e.injective
  change e (e.symm ((derivedDeltaDivisionStructure D (p : A) a₀).delta r)) =
    e ((deltaPDivisionSourceTensorCompletionDelta (σ := σ) D y).delta (e.symm r))
  rw [RingEquiv.apply_symm_apply]
  have h := deltaPDivisionSourceTensorCompletionEquiv_isDeltaHom D y hpA hg v hv hy (e.symm r)
  change e ((deltaPDivisionSourceTensorCompletionDelta (σ := σ) D y).delta (e.symm r)) =
    (derivedDeltaDivisionStructure D (p : A) a₀).delta (e (e.symm r)) at h
  rw [RingEquiv.apply_symm_apply] at h
  exact h.symm

end SerrePositivity.BhattScholze
