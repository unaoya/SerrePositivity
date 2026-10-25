module

public import SerrePositivity.BhattScholze.Delta.Division.DeltaDivisionSourceCoefficientQuotients
public import SerrePositivity.HomologicalAlgebra.BoundedAboveDerivedAssociator

/-! # 係数商還元を右因子へ移す実導来比較

共通の結合子と右係数拡大比較を使い、証明済みのα因子のTor消滅を供給する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard adicQuotientAlgebra
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (a : σ → A) (I : Ideal A)
local notation "P₀" => RelativeFreeDeltaRing (R := A) σ
local notation "J₀" => I.map (MvPolynomial.C : A →+* P₀)
local notation "Q₀" => P₀ ⧸ J₀
local notation "q₀" => Ideal.Quotient.mk J₀
local notation "α₀" => deltaDivisionSourceMap (σ := σ) D d
local notation "ψ₀" => RingHom.comp q₀ α₀
local notation "Mα" => baseChangeScalarModule α₀
local notation "Mβ" => baseChangeScalarModule (deltaDivisionSourceEval D a)
local notation "Mψ" => baseChangeScalarModule ψ₀

/-- 商へ降下したαbarの作用を係数制限すると、ψ=q∘αの実作用になる。 -/
def deltaDivisionSourceCoefficientTargetRestrictedScalarEquiv :
    letI := deltaDivisionSourceCoefficientTargetAlgebra (σ := σ) D d I
    letI : Module Q₀ Q₀ := Algebra.toModule
    (ModuleCat.restrictScalars q₀).obj (ModuleCat.of Q₀ Q₀) ≃ₗ[P₀] Mψ := by
  letI := deltaDivisionSourceCoefficientTargetAlgebra (σ := σ) D d I
  letI : Module Q₀ Q₀ := Algebra.toModule
  exact
    { toFun := fun z => z
      invFun := fun z => z
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro r z
        change deltaDivisionSourceCoefficientTargetMap D d I (q₀ r) * (show Q₀ from z) =
          ψ₀ r * (show Q₀ from z)
        rw [deltaDivisionSourceCoefficientTargetMap_mk]
        rfl }

/-- α因子の実導来係数拡大は、αbarの作用を持つ実商の次数零対象。 -/
def deltaDivisionSourceCoefficientTargetDerivedIso :
    letI := deltaDivisionSourceCoefficientTargetAlgebra (σ := σ) D d I
    letI : Module Q₀ Q₀ := Algebra.toModule
    (boundedAboveDerivedBaseChange q₀).obj (boundedAboveDerivedSingleFunctor.obj Mα) ≅
      boundedAboveDerivedSingleFunctor.obj (ModuleCat.of Q₀ Q₀) := by
  letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
  letI : Module P₀ P₀ := Algebra.toModule
  letI : Algebra Q₀ (P₀ ⧸ (J₀).map α₀) := adicQuotientAlgebra J₀ P₀
  letI := deltaDivisionSourceCoefficientTargetAlgebra (σ := σ) D d I
  letI : Module Q₀ Q₀ := Algebra.toModule
  exact derivedQuotientAlgebraIso J₀ P₀
    (deltaDivisionSourceTarget_coefficientTorVanishing (σ := σ) D d I) ≪≫
      boundedAboveDerivedSingleFunctor.mapIso
        (deltaDivisionSourceCoefficientTargetQuotientAlgEquiv
          (σ := σ) D d I).toLinearEquiv.toModuleIso

/-- 実導来α因子を商から係数制限すると、実残余射ψの次数零加群に一致する。 -/
def deltaDivisionSourceCoefficientTargetRestrictedIso :
    (boundedAboveDerivedRestrictScalars q₀).obj
      ((boundedAboveDerivedBaseChange q₀).obj (boundedAboveDerivedSingleFunctor.obj Mα)) ≅
        boundedAboveDerivedSingleFunctor.obj Mψ := by
  letI := deltaDivisionSourceCoefficientTargetAlgebra (σ := σ) D d I
  letI : Module Q₀ Q₀ := Algebra.toModule
  let e₁ := (boundedAboveDerivedRestrictScalars q₀).mapIso
    (deltaDivisionSourceCoefficientTargetDerivedIso (σ := σ) D d I)
  let e₂ : (boundedAboveDerivedRestrictScalars q₀).obj
      (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of Q₀ Q₀)) ≅
        boundedAboveDerivedSingleFunctor.obj
          ((ModuleCat.restrictScalars q₀).obj (ModuleCat.of Q₀ Q₀)) :=
    ObjectProperty.isoMk _ ((derivedRestrictScalarsSingleIso q₀ 0).app (ModuleCat.of Q₀ Q₀))
  exact e₁ ≪≫ e₂ ≪≫ boundedAboveDerivedSingleFunctor.mapIso
    (deltaDivisionSourceCoefficientTargetRestrictedScalarEquiv (σ := σ) D d I).toModuleIso

/-- α因子と実係数商の右導来テンソルは、実残余射ψの次数零加群。 -/
def deltaDivisionSourceCoefficientRightTensorIso :
    boundedAboveDerivedTensor.obj
        (boundedAboveDerivedSingleFunctor.obj Mα, derivedBaseChangeScalarObject q₀) ≅
      boundedAboveDerivedSingleFunctor.obj Mψ :=
  ((boundedAboveDerivedBaseChangeRightTensorNatIso q₀).app
    (boundedAboveDerivedSingleFunctor.obj Mα)).symm ≪≫
      deltaDivisionSourceCoefficientTargetRestrictedIso (σ := σ) D d I

/-- 結合子を用い、二因子の実係数商還元を実残余右因子との導来テンソルへ移す。 -/
def deltaDivisionSourceCoefficientAssociatorReductionIso :
    boundedAboveDerivedTensor.obj
        (boundedAboveDerivedTensor.obj
          (boundedAboveDerivedSingleFunctor.obj Mβ, boundedAboveDerivedSingleFunctor.obj Mα),
          derivedBaseChangeScalarObject q₀) ≅
      boundedAboveDerivedTensor.obj
        (boundedAboveDerivedSingleFunctor.obj Mβ, boundedAboveDerivedSingleFunctor.obj Mψ) :=
  boundedAboveDerivedTensorAssociator _ _ _ ≪≫ boundedAboveDerivedTensor.mapIso
    (Iso.prod (Iso.refl _) (deltaDivisionSourceCoefficientRightTensorIso (σ := σ) D d I))

/-- (p,d)係数還元を、実商射L→L/(p,Cd)との合成作用を持つ右因子へ移す。 -/
def deltaDivisionSourceResidueAssociatorReductionIso :
    boundedAboveDerivedTensor.obj
        (boundedAboveDerivedTensor.obj
          (boundedAboveDerivedSingleFunctor.obj Mβ, boundedAboveDerivedSingleFunctor.obj Mα),
          derivedBaseChangeScalarObject (Ideal.Quotient.mk
            (Ideal.span {(p : P₀), MvPolynomial.C d}))) ≅
      boundedAboveDerivedTensor.obj
        (boundedAboveDerivedSingleFunctor.obj Mβ,
          boundedAboveDerivedSingleFunctor.obj (baseChangeScalarModule
            ((Ideal.Quotient.mk (Ideal.span {(p : P₀), MvPolynomial.C d})).comp α₀))) := by
  have e := deltaDivisionSourceCoefficientAssociatorReductionIso D d a
    (Ideal.span {(p : A), d})
  let F := fun J : Ideal P₀ => boundedAboveDerivedTensor.obj
    (boundedAboveDerivedTensor.obj
      (boundedAboveDerivedSingleFunctor.obj Mβ, boundedAboveDerivedSingleFunctor.obj Mα),
        derivedBaseChangeScalarObject (Ideal.Quotient.mk J)) ≅
      boundedAboveDerivedTensor.obj
        (boundedAboveDerivedSingleFunctor.obj Mβ,
          boundedAboveDerivedSingleFunctor.obj
            (baseChangeScalarModule ((Ideal.Quotient.mk J).comp α₀)))
  change F ((Ideal.span {(p : A), d}).map (MvPolynomial.C : A →+* P₀)) at e
  change F (Ideal.span {(p : P₀), MvPolynomial.C d})
  exact Eq.mp (congrArg F (deltaDivisionSourceCoefficientIdeal_map (σ := σ) d)) e

end SerrePositivity.BhattScholze
