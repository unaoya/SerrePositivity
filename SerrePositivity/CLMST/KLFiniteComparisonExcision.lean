module

public import SerrePositivity.CLMST.KLCohomologyFromExcision
public import SerrePositivity.BhattScholze.Perfectoidization.PerfectoidizationExcision
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
perfectoid 基底上の有限比較は KLFiniteComparisonExcision を満たす。

## 方針
元の有限性・有限表示性から始域・終域と主イデアルの導来完備性を供給する。
核・余核の支持条件で元の主局所化写像を全単射にし、整写像の標準 excision 定理を使う。

## 使われ方
共通モデルへの二写像の hPBu、hPBv を解消し、Prop 2.4.9(a) と KL-Q へ渡す。
-/
theorem klFiniteComparisonExcision_of_perfectoid
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) : KLFiniteComparisonExcision R p := by
  intro A B C D _ _ _ _ _ _ _ _ _ _ _ _ a q hq hk hc f g hf hg
  let : Module.FinitePresentation R A :=
    Module.FinitePresentation.of_finite_of_finitePresentation R A
  let : Module.FinitePresentation R B :=
    Module.FinitePresentation.of_finite_of_finitePresentation R B
  have hA := isModuleComplete_finitePresentation_algebra_principal R A
    (p : R) (algebraMap R A a) (hR.isModuleComplete R p)
  have hB := isModuleComplete_finitePresentation_algebra_principal R B
    (p : R) (algebraMap R B a) (hR.isModuleComplete R p)
  simp only [map_natCast] at hA hB
  let : Algebra A B := q.toRingHom.toAlgebra
  let : Module.Finite A B := hq
  obtain ⟨n, hn⟩ := hc
  have haway := localizationComparison_awayMap_bijective_of_power_bounds a q hk (by
    intro y
    refine ⟨n, ?_⟩
    apply (Submodule.Quotient.mk_eq_zero q.toLinearMap.range).mp
    change q.toLinearMap.range.mkQ (a ^ n • y) = 0
    exact (q.toLinearMap.range.mkQ.map_smul (a ^ n) y).trans (hn _))
  exact klCanonicalExcisionSquare_of_integral_away R p hR A B C D q a f g hf hg
    hA.2.1 hB.2.1 hA.2.2.1 haway

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
  exact perfectoidIdeal_powerTorsionTorInput_of_finiteComparison_excision p hR
    (fun E _ _ hE _ => klFiniteComparisonExcision_of_perfectoid E p hE) a f hf

end SerrePositivity.CLMST
