module

public import SerrePositivity.BhattScholze.Perfectoidization.FiniteComparisonExcision
public import SerrePositivity.BhattScholze.Perfectoidization.Excision
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
# KL の有限比較 excision の実証明

## 概要
有限表示な有限代数間の有限写像について、核の冪ねじれと余核の一様零化から
標準 perfectoid 化の四角形が引き戻しであることを証明する。

## 方針
有限表示から導来 p 完備性を得て、支持条件から主局所化の全単射性を得る。
有限写像の整性とともに BS Cor 8.12 の環版の系へ渡す。

## 使われ方
A と有限直積から共通モデルへの二つの比較に同じ証明を適用し、KL の全 Tor 入力を供給する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
open BhattScholze DerivedCompletion
set_option backward.isDefEq.respectTransparency false

/--
## 概要
有限表示な有限代数が a の外でエタールなら、元の perfectoid ideal の全元は
任意の p 冪ねじれ試験加群に対する正次数 Tor の元の係数作用を零化する。

## 方針
一つの André 拡大上で有限比較 excision を供給し、既存の忠実な Tor 検出で元の基底へ戻す。
拡大と比較モデルの選択は、全試験加群・全指数・全正次数に先行する。

## 使われ方
Prop 2.4.9(a) の入力 (a) として KL の全加群版とコホモロジー消滅に用いる。
-/
theorem perfectoidIdeal_powerTorsionTorInput
    {R A C : Type u} [CommRing R] [CommRing A] [CommRing C]
    [Algebra R A] [Algebra R C] [Module.Finite R A] [Algebra.FinitePresentation R A]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (a : R) (f : A →ₐ[R] C) (hf : IsPerfectoidization p f.toRingHom) :
    letI := GenericEtale.awayAlgebra R A a
    Algebra.Etale (Localization.Away a) (Localization.Away (algebraMap R A a)) →
      ∀ (N : ModuleCat.{u} R) (k : ℕ), (∀ x : N, (p : R) ^ k • x = 0) →
        ∀ i : ℕ, 0 < i → ∀ s ∈ perfectoidIdeal R p hR a,
          torCoefficientScalarEndomorphism C N i (algebraMap R C s) = 0 := by
  exact BhattScholze.perfectoidIdeal_powerTorsionTorInput_of_finiteComparison_excision p hR
    (fun E _ _ hE _ => BhattScholze.klFiniteComparisonExcision_of_perfectoid E p hE) a f hf

end SerrePositivity.CLMST
