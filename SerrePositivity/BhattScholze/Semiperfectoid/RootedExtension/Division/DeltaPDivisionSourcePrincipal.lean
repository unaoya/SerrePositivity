module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.Division.DeltaPDivisionRawRelativeModP
public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.Division.DeltaPDivisionSourceTensor

/-! # 実自由δ射の通常テンソルと具体的分冪表示環

自由δ射の導来テンソルの離散性は主張しない。A上の導来完備化と実p還元は別に明示する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (y : A)
local notation "P₀" => RelativeFreeDeltaRing (R := A) σ
local notation "T₀" => TensorProduct P₀ A P₀
local notation "a₀" => fun _ : σ ↦ D.frobeniusLift y
local notation "qraw₀" => Ideal.Quotient.mk
  (DeltaStructure.deltaClosure (relativeFreeDeltaStructure σ D)
    (deltaDivisionRelationIdeal (p : A) a₀))
local notation "Q₀" => A ⧸ Ideal.span {(p : A)}
local notation "q₀" => Ideal.Quotient.mk (Ideal.span {(p : A)})

/-- 指定した実自由δ射の通常テンソルと、分冪表示環との標準環同型。 -/
def deltaPDivisionSourcePrincipalEquiv
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    T₀ ≃+* PrincipalDPPresentation A y := by
  letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
  letI : Module P₀ P₀ := Algebra.toModule
  exact (deltaPDivisionSourceTensorEquiv (σ := σ) D y).trans
    (deltaPDivisionRawPrincipalEquiv (σ := σ) hA hpA D y hg v hv hy)

/-- 全純テンソルの像は、左係数と右因子の実商像で計算できる。 -/
theorem deltaPDivisionSourcePrincipalEquiv_tmul
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) (a : A) (b : P₀) :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    deltaPDivisionSourcePrincipalEquiv D y hA hpA hg v hv hy (a ⊗ₜ[P₀] b) =
      algebraMap A (PrincipalDPPresentation A y) a *
        deltaPDivisionRawPrincipalEquiv (σ := σ) hA hpA D y hg v hv hy (qraw₀ b) := by
  let := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  let := deltaPDivisionSourceTargetAlgebra (σ := σ) D
  let : Module P₀ P₀ := Algebra.toModule
  rw [deltaPDivisionSourcePrincipalEquiv, RingEquiv.trans_apply,
    deltaPDivisionSourceTensorEquiv_tmul, map_mul, deltaPDivisionRawPrincipalEquiv_coeff]

/-- 通常テンソル比較は、元の自然な左A係数作用を保つA代数同型。 -/
def deltaPDivisionSourcePrincipalAlgEquiv
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    T₀ ≃ₐ[A] PrincipalDPPresentation A y := by
  letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
  letI : Module P₀ P₀ := Algebra.toModule
  refine { deltaPDivisionSourcePrincipalEquiv D y hA hpA hg v hv hy with commutes' := ?_ }
  intro a
  change deltaPDivisionSourcePrincipalEquiv D y hA hpA hg v hv hy (a ⊗ₜ[P₀] 1) = _
  rw [deltaPDivisionSourcePrincipalEquiv_tmul]
  simp only [map_one, mul_one]

/-- この通常テンソルを元のA→A/pで実導来還元した具体的比較。 -/
def deltaPDivisionSourcePrincipalDerivedModPIso
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    (boundedAboveDerivedBaseChange q₀).obj
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A T₀)) ≅
      boundedAboveDerivedSingleFunctor.obj
        (ModuleCat.of Q₀ (PrincipalDPPresentation Q₀ (q₀ y))) := by
  letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
  letI : Module P₀ P₀ := Algebra.toModule
  let e := (deltaPDivisionSourcePrincipalAlgEquiv D y hA hpA hg v hv hy).toLinearEquiv.toModuleIso
  exact (boundedAboveDerivedBaseChange q₀).mapIso (boundedAboveDerivedSingleFunctor.mapIso e) ≪≫
    principalDPRelativeDerivedModPIso y hA hpA hy

/-- 通常テンソルのA上の実導来完備化を実p還元した具体的比較。 -/
def deltaPDivisionSourcePrincipalCompletedModPIso
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    (boundedAboveDerivedBaseChange q₀).obj
        ((DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)).obj
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A T₀))) ≅
      boundedAboveDerivedSingleFunctor.obj
        (ModuleCat.of Q₀ (PrincipalDPPresentation Q₀ (q₀ y))) := by
  letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
  letI : Module P₀ P₀ := Algebra.toModule
  let e := (deltaPDivisionSourcePrincipalAlgEquiv D y hA hpA hg v hv hy).toLinearEquiv.toModuleIso
  exact (boundedAboveDerivedBaseChange q₀).mapIso
      ((DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)).mapIso
        (boundedAboveDerivedSingleFunctor.mapIso e)) ≪≫
    principalDPRelativeCompletedDerivedModPIso y hA hpA hy

/-- 通常テンソルの実p比較も、元のA上の標準導来完備化単位と両立する。 -/
theorem deltaPDivisionSourcePrincipalCompletedModPIso_unit
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    (boundedAboveDerivedBaseChange q₀).map
        ((DerivedCompletion.boundedAboveDerivedCompletionUnit A (p : A)).app
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A T₀))) ≫
      (deltaPDivisionSourcePrincipalCompletedModPIso D y hA hpA hg v hv hy).hom =
        (deltaPDivisionSourcePrincipalDerivedModPIso D y hA hpA hg v hv hy).hom := by
  let := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  let := deltaPDivisionSourceTargetAlgebra (σ := σ) D
  let : Module P₀ P₀ := Algebra.toModule
  let e := boundedAboveDerivedSingleFunctor.mapIso
    (deltaPDivisionSourcePrincipalAlgEquiv D y hA hpA hg v hv hy).toLinearEquiv.toModuleIso
  let F := boundedAboveDerivedBaseChange q₀
  let C := DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)
  let U := DerivedCompletion.boundedAboveDerivedCompletionUnit A (p : A)
  change F.map (U.app _) ≫
      (F.map (C.map e.hom) ≫ (principalDPRelativeCompletedDerivedModPIso y hA hpA hy).hom) =
    F.map e.hom ≫ (principalDPRelativeDerivedModPIso y hA hpA hy).hom
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, ← U.naturality e.hom,
    CategoryTheory.Functor.map_comp, Category.assoc,
    principalDPRelativeCompletedDerivedModPIso_unit]
  rfl

end SerrePositivity.BhattScholze
