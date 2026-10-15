module

public import SerrePositivity.BhattScholze.DeltaDivisionSourceCoefficientMaps

/-! # 実係数商還元の両因子と降下作用の明示

商イデアルの一致だけで作用を省略せず、βbar・αbarの作用を持つ標準商と比較する。
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
local notation "β₀" => deltaDivisionSourceEval D a
local notation "α₀" => deltaDivisionSourceMap (σ := σ) D d

/-- βbarが定める実評価係数商の源商代数構造。 -/
@[instance_reducible] def deltaDivisionSourceCoefficientEvalAlgebra : Algebra Q₀ (A ⧸ I) :=
  (deltaDivisionSourceCoefficientEvalMap D a I).toAlgebra

/-- αbarが定める実終域係数商の源商代数構造。 -/
@[instance_reducible] def deltaDivisionSourceCoefficientTargetAlgebra : Algebra Q₀ Q₀ :=
  (deltaDivisionSourceCoefficientTargetMap (σ := σ) D d I).toAlgebra

/-- β側の通常商を、βbarの実源作用を保ってA/Iと比較する。 -/
def deltaDivisionSourceCoefficientEvalQuotientAlgEquiv :
    letI := deltaDivisionSourceEvaluationAlgebra D a
    letI : Algebra Q₀ (A ⧸ (J₀).map β₀) := adicQuotientAlgebra J₀ A
    letI := deltaDivisionSourceCoefficientEvalAlgebra D a I
    (A ⧸ (J₀).map β₀) ≃ₐ[Q₀] (A ⧸ I) := by
  letI := deltaDivisionSourceEvaluationAlgebra D a
  letI : Algebra Q₀ (A ⧸ (J₀).map β₀) := adicQuotientAlgebra J₀ A
  letI := deltaDivisionSourceCoefficientEvalAlgebra D a I
  apply AlgEquiv.ofRingEquiv
    (f := Ideal.quotEquivOfEq (deltaDivisionSourceEvaluation_coefficientIdeal_map D a I))
  intro x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.quotEquivOfEq _ (Ideal.Quotient.mk ((J₀).map β₀) (β₀ r)) =
    deltaDivisionSourceCoefficientEvalMap D a I (Ideal.Quotient.mk J₀ r)
  rw [Ideal.quotEquivOfEq_mk, deltaDivisionSourceCoefficientEvalMap_mk]

/-- α側の通常商を、αbarの実源作用を保ってL/Jと比較する。 -/
def deltaDivisionSourceCoefficientTargetQuotientAlgEquiv :
    letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
    letI : Module P₀ P₀ := Algebra.toModule
    letI : Algebra Q₀ (P₀ ⧸ (J₀).map α₀) := adicQuotientAlgebra J₀ P₀
    letI := deltaDivisionSourceCoefficientTargetAlgebra (σ := σ) D d I
    letI : Module Q₀ Q₀ := Algebra.toModule
    (P₀ ⧸ (J₀).map α₀) ≃ₐ[Q₀] Q₀ := by
  letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
  letI : Module P₀ P₀ := Algebra.toModule
  letI : Algebra Q₀ (P₀ ⧸ (J₀).map α₀) := adicQuotientAlgebra J₀ P₀
  letI := deltaDivisionSourceCoefficientTargetAlgebra (σ := σ) D d I
  letI : Module Q₀ Q₀ := Algebra.toModule
  apply AlgEquiv.ofRingEquiv
    (f := Ideal.quotEquivOfEq (deltaDivisionSourceTarget_coefficientIdeal_map (σ := σ) D d I))
  intro x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.quotEquivOfEq _ (Ideal.Quotient.mk ((J₀).map α₀) (α₀ r)) =
    deltaDivisionSourceCoefficientTargetMap (σ := σ) D d I (Ideal.Quotient.mk J₀ r)
  rw [Ideal.quotEquivOfEq_mk, deltaDivisionSourceCoefficientTargetMap_mk]

/-- 実二因子導来還元の右辺を、βbarで作用するA/Iとαbarで作用するL/Jで明示する。 -/
def deltaDivisionSourceCoefficientExplicitReductionIso :
    letI := deltaDivisionSourceEvaluationAlgebra D a
    letI : Algebra Q₀ (A ⧸ (J₀).map β₀) := adicQuotientAlgebra J₀ A
    letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
    letI : Module P₀ P₀ := Algebra.toModule
    letI : Algebra Q₀ (P₀ ⧸ (J₀).map α₀) := adicQuotientAlgebra J₀ P₀
    letI := deltaDivisionSourceCoefficientEvalAlgebra D a I
    letI := deltaDivisionSourceCoefficientTargetAlgebra (σ := σ) D d I
    letI : Module Q₀ Q₀ := Algebra.toModule
    boundedAboveDerivedTensor.obj
        (boundedAboveDerivedTensor.obj
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of P₀ A),
            boundedAboveDerivedSingleFunctor.obj (ModuleCat.of P₀ P₀)),
          derivedBaseChangeScalarObject (Ideal.Quotient.mk J₀)) ≅
      (boundedAboveDerivedRestrictScalars (Ideal.Quotient.mk J₀)).obj
        (boundedAboveDerivedTensor.obj
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of Q₀ (A ⧸ I)),
            boundedAboveDerivedSingleFunctor.obj (ModuleCat.of Q₀ Q₀))) := by
  letI := deltaDivisionSourceEvaluationAlgebra D a
  letI : Algebra Q₀ (A ⧸ (J₀).map β₀) := adicQuotientAlgebra J₀ A
  letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
  letI : Module P₀ P₀ := Algebra.toModule
  letI : Algebra Q₀ (P₀ ⧸ (J₀).map α₀) := adicQuotientAlgebra J₀ P₀
  letI := deltaDivisionSourceCoefficientEvalAlgebra D a I
  letI := deltaDivisionSourceCoefficientTargetAlgebra (σ := σ) D d I
  letI : Module Q₀ Q₀ := Algebra.toModule
  let eβ := (deltaDivisionSourceCoefficientEvalQuotientAlgEquiv D a I).toLinearEquiv.toModuleIso
  let eα :=
    (deltaDivisionSourceCoefficientTargetQuotientAlgEquiv (σ := σ) D d I).toLinearEquiv.toModuleIso
  exact deltaDivisionSourceCoefficientReductionIso D d a I ≪≫
    (boundedAboveDerivedRestrictScalars (Ideal.Quotient.mk J₀)).mapIso
      (boundedAboveDerivedTensor.mapIso
        (Iso.prod (boundedAboveDerivedSingleFunctor.mapIso eβ)
          (boundedAboveDerivedSingleFunctor.mapIso eα)))

end SerrePositivity.BhattScholze
