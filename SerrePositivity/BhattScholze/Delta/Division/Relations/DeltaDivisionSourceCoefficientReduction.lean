module

public import SerrePositivity.BhattScholze.Delta.Division.Relations.DeltaDivisionSourceCoefficientTor
public import SerrePositivity.HomologicalAlgebra.DerivedBaseChangeRightTensor

/-! # 自由δ射の両因子を伴う実係数商基底変更

共通の実導来テンソル商比較へ、証明済みの両因子のTor消滅を供給する。
残余環を係数側Koszul複体と同一視したり、完備化後CFFを結論したりしない。
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
local notation "q₀" => Ideal.Quotient.mk J₀
local notation "Mβ" => baseChangeScalarModule (deltaDivisionSourceEval D a)
local notation "Mα" => baseChangeScalarModule (deltaDivisionSourceMap (σ := σ) D d)

/-- β側の係数イデアル像は、元の係数イデアルIそのもの。 -/
theorem deltaDivisionSourceEvaluation_coefficientIdeal_map :
    (J₀).map (deltaDivisionSourceEval D a) = I := by
  rw [Ideal.map_map]
  have h : (deltaDivisionSourceEval D a).comp (MvPolynomial.C : A →+* P₀) =
      RingHom.id A := by
    apply RingHom.ext
    intro r
    exact deltaDivisionSourceEval_C D a r
  rw [h, Ideal.map_id]

/-- α側の係数イデアル像は同じ拡張イデアル。ただしαの源作用を保つ。 -/
theorem deltaDivisionSourceTarget_coefficientIdeal_map :
    (J₀).map (deltaDivisionSourceMap (σ := σ) D d) = J₀ := by
  rw [Ideal.map_map]
  have h : (deltaDivisionSourceMap (σ := σ) D d).comp (MvPolynomial.C : A →+* P₀) =
      (MvPolynomial.C : A →+* P₀) := by
    apply RingHom.ext
    intro r
    exact deltaDivisionSourceMap_C D d r
  rw [h]

/-- 実自由δ射の両因子のテンソルを係数商で実導来還元する標準比較。
両因子のTor仮定は既存の平坦基底変更から証明済みの補題で供給する。 -/
def deltaDivisionSourceCoefficientReductionIso :
    letI := deltaDivisionSourceEvaluationAlgebra D a
    letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
    letI : Module P₀ P₀ := Algebra.toModule
    boundedAboveDerivedTensor.obj
        (boundedAboveDerivedTensor.obj
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of P₀ A),
            boundedAboveDerivedSingleFunctor.obj (ModuleCat.of P₀ P₀)),
          derivedBaseChangeScalarObject q₀) ≅
      (boundedAboveDerivedRestrictScalars q₀).obj
        (boundedAboveDerivedTensor.obj
          (boundedAboveDerivedSingleFunctor.obj
            (ModuleCat.of (P₀ ⧸ J₀) (A ⧸ (J₀).map (algebraMap P₀ A))),
           boundedAboveDerivedSingleFunctor.obj
            (ModuleCat.of (P₀ ⧸ J₀) (P₀ ⧸ (J₀).map (algebraMap P₀ P₀))))) := by
  letI := deltaDivisionSourceEvaluationAlgebra D a
  letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
  letI : Module P₀ P₀ := Algebra.toModule
  exact restrictedDerivedTensorQuotientAlgebraIso J₀ A P₀
    (deltaDivisionSourceEvaluation_coefficientTorVanishing D a I)
    (deltaDivisionSourceTarget_coefficientTorVanishing D d I)

/-- 同じ両因子の比較を、実係数拡大の値そのものを用いる加群表示で与える。 -/
def deltaDivisionSourceCoefficientModuleReductionIso :
    boundedAboveDerivedTensor.obj
        (boundedAboveDerivedTensor.obj
          (boundedAboveDerivedSingleFunctor.obj Mβ, boundedAboveDerivedSingleFunctor.obj Mα),
          derivedBaseChangeScalarObject q₀) ≅
      (boundedAboveDerivedRestrictScalars q₀).obj
        (boundedAboveDerivedTensor.obj
          (boundedAboveDerivedSingleFunctor.obj ((ModuleCat.extendScalars q₀).obj Mβ),
            boundedAboveDerivedSingleFunctor.obj ((ModuleCat.extendScalars q₀).obj Mα))) :=
  ((boundedAboveDerivedBaseChangeRightTensorNatIso q₀).app _).symm ≪≫
    (boundedAboveDerivedRestrictScalars q₀).mapIso
      (boundedAboveDerivedTensorBaseChangeModuleIso q₀ Mβ Mα
        (deltaDivisionSourceEvaluation_coefficientTorVanishing D a I)
        (deltaDivisionSourceTarget_coefficientTorVanishing D d I))

end SerrePositivity.BhattScholze
