module

public import SerrePositivity.BhattScholze.RankOneDPDerivedRelativeFlat

/-! # 具体的評価環の実導来比較とKoszul平坦性 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard rankOneDPPolynomialAlgebra
variable {p : ℕ} {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
local notation "P₀" => Polynomial A
local notation "G₀" => DividedPowerAlgebra A A

/-- 実係数拡大をAへ制限した加群と、元の係数作用を持つ評価テンソル環の線形同値。 -/
def rankOneDPEvaluatedScalarExtensionEquiv (y : B) :
    letI := rankOneDPEvaluationAlgebra (A := A) y
    ((ModuleCat.restrictScalars (algebraMap A G₀)).obj
      ((ModuleCat.extendScalars (rankOneDPPolynomialMap A).toRingHom).obj
        (ModuleCat.of P₀ B))) ≃ₗ[A] RankOneDPEvaluatedEnvelope A B y := by
  let := rankOneDPEvaluationAlgebra (A := A) y
  refine
    { toFun := fun z ↦ z
      invFun := fun z ↦ z
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := ?_ }
  intro a z
  induction z using TensorProduct.inductionOn (R := P₀) (M := G₀) (N := B) with
  | tmul g b =>
      change ((algebraMap A G₀ a) * (g : G₀)) ⊗ₜ[P₀] (b : B) =
        (a • (g : G₀)) ⊗ₜ[P₀] (b : B)
      rw [Algebra.smul_def]
  | add z w hz hw => simp only [smul_add, hz, hw]

/-- 実導来分冪拡大のH0は、元のA作用を保って通常評価環と一致する。 -/
def rankOneDPEvaluatedDerivedH0Equiv (y : B) :
    letI := rankOneDPEvaluationAlgebra (A := A) y
    ((ModuleCat.restrictScalars (algebraMap A G₀)).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} G₀) 0).obj
        (((boundedAboveDerivedBaseChange (rankOneDPPolynomialMap A).toRingHom).obj
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of P₀ B))).obj))) ≃ₗ[A]
      RankOneDPEvaluatedEnvelope A B y := by
  let := rankOneDPEvaluationAlgebra (A := A) y
  let eH := (DerivedCategory.homologyFunctor (ModuleCat.{u} G₀) 0).mapIso
      (boundedAboveDerivedBaseChangeModuleIso (rankOneDPPolynomialMap A).toRingHom
        (ModuleCat.of P₀ B)) ≪≫
    (derivedModuleBaseChangeH0Iso (rankOneDPPolynomialMap A).toRingHom).app (ModuleCat.of P₀ B)
  exact (((ModuleCat.restrictScalars (algebraMap A G₀)).mapIso eH).toLinearEquiv).trans
    (rankOneDPEvaluatedScalarExtensionEquiv y)

/-- 通常評価環のA平坦性は、実X^p Koszul H0のA平坦性と同値。 -/
theorem rankOneDPEvaluatedEnvelope_flat_iff_koszul_h0
    (hprime : p.Prime) (hp : (p : A) = 0) (y : B) :
    letI := rankOneDPEvaluationAlgebra (A := A) y
    Module.Flat A (RankOneDPEvaluatedEnvelope A B y) ↔
    Module.Flat A ((ModuleCat.restrictScalars (algebraMap A P₀)).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} P₀) 0).obj
        ((DerivedCompletion.derivedScalarConeFunctor P₀ ((Polynomial.X : P₀) ^ p)).obj
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of P₀ B)).obj))) := by
  let := rankOneDPEvaluationAlgebra (A := A) y
  exact (Module.Flat.equiv_iff (rankOneDPEvaluatedDerivedH0Equiv y)).symm.trans
    (rankOneDPDerivedKoszulHomology_flat_iff hprime hp
      (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of P₀ B)) 0)

/-- 実Koszul消滅を仮定したときの、実導来評価環から通常評価環への標準比較同型。 -/
def rankOneDPEvaluatedDerivedOrdinaryIso (hprime : p.Prime) (hp : (p : A) = 0) (y : B)
    (hK : letI := rankOneDPEvaluationAlgebra (A := A) y
      ∀ n : ℕ, 0 < n → IsZero
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} P₀) (-(n : ℤ))).obj
          ((DerivedCompletion.derivedScalarConeFunctor P₀ ((Polynomial.X : P₀) ^ p)).obj
            (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of P₀ B)).obj))) :
    letI := rankOneDPEvaluationAlgebra (A := A) y
    (boundedAboveDerivedBaseChange (rankOneDPPolynomialMap A).toRingHom).obj
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of P₀ B)) ≅
      boundedAboveDerivedSingleFunctor.obj
        (ModuleCat.of G₀ (RankOneDPEvaluatedEnvelope A B y)) := by
  let := rankOneDPEvaluationAlgebra (A := A) y
  exact rankOneDPDerivedOrdinaryIso_of_koszul hprime hp (ModuleCat.of P₀ B) hK

end SerrePositivity.BhattScholze
