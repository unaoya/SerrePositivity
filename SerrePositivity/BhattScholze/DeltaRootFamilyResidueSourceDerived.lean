module

public import SerrePositivity.BhattScholze.DeltaRootFamilySourceColimitTor
public import SerrePositivity.BhattScholze.DeltaRootResidueSourceDerived

/-! # 有限根族の実導来β拡大と既存raw残余商の標準比較 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (b : σ → A) {m : ℕ}
local notation "P₀" => MvPolynomial σ A
local notation "L₀" => RelativeFreeDeltaRing (R := P₀) σ
local notation "E₀" => polynomialRankOneDeltaStructure σ D
local notation "c₀" => deltaRootRelationFamily (p := p) b
local notation "K₀" => Ideal.span {(p : L₀), MvPolynomial.C (MvPolynomial.C d)}
local notation "Q₀" => L₀ ⧸ K₀
local notation "ψ₀" => RingHom.comp (Ideal.Quotient.mk K₀)
  (deltaDivisionSourceMap (σ := σ) E₀ (MvPolynomial.C d))
local notation "β₀" => deltaDivisionSourceEval E₀ c₀
local notation "Mψ" => baseChangeScalarModule ψ₀
local notation "Res₀" => DeltaAdjoinDivisionResidue E₀ (MvPolynomial.C d) c₀

/-- 有限根族について、実残余終域のβ導来拡大は既存raw残余商の次数零対象。 -/
def deltaRootFamilyResidueSourceDerivedIso (s : Fin m ≃ σ)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    (boundedAboveDerivedBaseChange β₀).obj (boundedAboveDerivedSingleFunctor.obj Mψ) ≅
      boundedAboveDerivedSingleFunctor.obj (ModuleCat.of P₀ Res₀) := by
  letI := deltaDivisionSourceEvaluationAlgebra E₀ c₀
  letI := deltaDivisionSourceResidueTargetAlgebra (σ := σ) E₀ (MvPolynomial.C d)
  letI : Module L₀ Q₀ := Algebra.toModule
  let e := (deltaRootResidueSourceEvalScalarEquiv D d b).trans
    (deltaDivisionSourceResidueTensorAlgEquiv E₀ (MvPolynomial.C d) c₀).toLinearEquiv
  exact boundedAboveDerivedBaseChangeModuleAugmentationIso β₀ Mψ
    (deltaRootFamilyResidueSourceEval_torVanishing
      (D := D) (a := b) (s := s) (d := d) hpA v hv) ≪≫
        boundedAboveDerivedSingleFunctor.mapIso e.toModuleIso

/-- 比較同型の順射は、標準導来augmentationと既存残余商比較の合成。 -/
theorem deltaRootFamilyResidueSourceDerivedIso_hom (s : Fin m ≃ σ)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    letI := deltaDivisionSourceEvaluationAlgebra E₀ c₀
    letI := deltaDivisionSourceResidueTargetAlgebra (σ := σ) E₀ (MvPolynomial.C d)
    letI : Module L₀ Q₀ := Algebra.toModule
    let e := (deltaRootResidueSourceEvalScalarEquiv D d b).trans
      (deltaDivisionSourceResidueTensorAlgEquiv E₀ (MvPolynomial.C d) c₀).toLinearEquiv
    (deltaRootFamilyResidueSourceDerivedIso D d b s hpA v hv).hom.hom =
      (boundedAboveDerivedBaseChangeModuleAugmentation β₀).app Mψ ≫
        (boundedAboveDerivedSingleFunctor.map e.toModuleIso.hom).hom := by
  rfl

end SerrePositivity.BhattScholze
