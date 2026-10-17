module

public import SerrePositivity.CLMST.ConditionalCohomologyFromPowerTorsion
public import SerrePositivity.CommutativeAlgebra.RootTower.Completion
public import SerrePositivity.CommutativeAlgebra.RegularParameters

/-!
# CompletedTower 上の指定二入力から全加群 Tor と両消滅へ

## 概要
CLMST v4 Thm 4.0.3(a), pp.27–28 と Cor 4.0.4, p.28 の条件付き接続を、
元の完備根の塔とその係数作用で具体化する。

## 方針
既存の全加群帰着と条件付き合流を適用し、正則パラメータの Koszul 分解を供給する。

## 規約
係数環 C は指定された perfectoid 代数を使う。別の perfectoid 化を選ばない。
BS 著者版 Prop 10.2, p.78 型の仮定と p 冪ねじれ版は明示引数として残す。

## 使われ方
レーン B の拡大閉性を受領後、その定理を hExt に直接適用できる。
Cor 8.12 と無関係に KL-Q の全量化・元の塔作用を検査する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
open CategoryTheory Section2 IsLocalRing
variable {A C : Type u} [CommRing A] [IsRegularLocalRing A] [CommRing C]
    {e : ℕ} (t : Fin e → A) (p : ℕ) [Fact p.Prime]
    [Algebra A C] [Algebra (CompletedTower A t p) C]
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p) (hC : IsIntegralPerfectoid C p)
    (g : A)

include hC

/-- 概要：指定した完備根の塔の ideal の全元が任意 A 加群の高次 Tor を消す。
方針：Thm 4.0.3(a), pp.27–28 の全加群帰着へ R=CompletedTower と元の作用を代入する。
規約：p 冪ねじれ試験と Prop 10.2 型の拡大閉性の型を変えない。
使われ方：実際の塔上で KL-Q に渡す hTor。二仮定の実供給は主張しない。 -/
theorem completedTower_allModule_tor_annihilated
    (hExt : ∀ (X : ShortComplex (ModuleCat.{u} (CompletedTower A t p))), X.ShortExact →
      DerivedCompletion.IsModuleComplete (CompletedTower A t p) (p : CompletedTower A t p) X.X₁ →
      DerivedCompletion.IsModuleComplete (CompletedTower A t p) (p : CompletedTower A t p) X.X₂ →
      DerivedCompletion.IsModuleComplete (CompletedTower A t p) (p : CompletedTower A t p) X.X₃ →
      Almost.IsAlmostZero (perfectoidIdeal (CompletedTower A t p) p hperf
        (algebraMap A (CompletedTower A t p) g)) X.X₁ →
      Almost.IsAlmostZero (perfectoidIdeal (CompletedTower A t p) p hperf
        (algebraMap A (CompletedTower A t p) g)) X.X₃ →
      Almost.IsAlmostZero (perfectoidIdeal (CompletedTower A t p) p hperf
        (algebraMap A (CompletedTower A t p) g)) X.X₂)
    (hTor : ∀ (N : ModuleCat.{u} A) (k : ℕ),
      (∀ x : N, (p : A) ^ k • x = 0) → ∀ j : ℕ, 0 < j →
        ∀ s ∈ perfectoidIdeal (CompletedTower A t p) p hperf
          (algebraMap A (CompletedTower A t p) g),
          torCoefficientScalarEndomorphism C N j (algebraMap (CompletedTower A t p) C s) = 0) :
    ∀ (N : ModuleCat.{u} A) (j : ℕ), 0 < j →
      ∀ s ∈ perfectoidIdeal (CompletedTower A t p) p hperf
        (algebraMap A (CompletedTower A t p) g),
        torCoefficientScalarEndomorphism C N j (algebraMap (CompletedTower A t p) C s) = 0 := by
  exact perfectoidIdeal_allModule_tor_annihilated p hperf
    (algebraMap A (CompletedTower A t p) g) (algebraMap (CompletedTower A t p) C) hC hExt hTor

/-- 概要：元の塔作用と二入力から、局所コホモロジーと全段 Koszul の両消滅を得る。
方針：正則局所環のパラメータの全冪を Koszul 分解とし、条件付き Cor 4.0.4 に適用する。
規約：CLMST Cor 4.0.4, p.28 の全有限段・任意パラメータ系を保持し、hI も明示する。
使われ方：KL-Q の実塔での受渡し。無条件の Thm 4.0.3(a) の完成とは数えない。 -/
theorem completedTower_cohomology_vanishing_of_powerTorsion_and_extension
    {D : Type u} [CommRing D] [IsLocalRing D] [IsNoetherianRing D]
    [Algebra A D] [Module.Finite A D] [Algebra D C] [IsScalarTower A D C]
    (ht : Ideal.span (Set.range t) = maximalIdeal A) (hdim : ringKrullDim A = e)
    (hsop : IsSystemOfParameters D (algebraMap A D ∘ t))
    (φ : ∀ n : ℕ, StageAlgebra A D t p n →+* C)
    (hφ : ∀ (n : ℕ) (x : A), φ n (algebraMap D (StageAlgebra A D t p n)
      (algebraMap A D x)) = algebraMap A C x)
    (j₀ : Fin e) (htp : t j₀ = (p : A))
    (hI : ∀ k : ℕ, 0 < k → IsIdempotentElem
      ((perfectoidIdeal (CompletedTower A t p) p hperf
        (algebraMap A (CompletedTower A t p) g)).map
          (Ideal.Quotient.mk (Ideal.span {(p : CompletedTower A t p) ^ k}))))
    (hExt : ∀ (X : ShortComplex (ModuleCat.{u} (CompletedTower A t p))), X.ShortExact →
      DerivedCompletion.IsModuleComplete (CompletedTower A t p) (p : CompletedTower A t p) X.X₁ →
      DerivedCompletion.IsModuleComplete (CompletedTower A t p) (p : CompletedTower A t p) X.X₂ →
      DerivedCompletion.IsModuleComplete (CompletedTower A t p) (p : CompletedTower A t p) X.X₃ →
      Almost.IsAlmostZero (perfectoidIdeal (CompletedTower A t p) p hperf
        (algebraMap A (CompletedTower A t p) g)) X.X₁ →
      Almost.IsAlmostZero (perfectoidIdeal (CompletedTower A t p) p hperf
        (algebraMap A (CompletedTower A t p) g)) X.X₃ →
      Almost.IsAlmostZero (perfectoidIdeal (CompletedTower A t p) p hperf
        (algebraMap A (CompletedTower A t p) g)) X.X₂)
    (hTor : ∀ (N : ModuleCat.{u} A) (k : ℕ),
      (∀ x : N, (p : A) ^ k • x = 0) → ∀ j : ℕ, 0 < j →
        ∀ s ∈ perfectoidIdeal (CompletedTower A t p) p hperf
          (algebraMap A (CompletedTower A t p) g),
          torCoefficientScalarEndomorphism C N j (algebraMap (CompletedTower A t p) C s) = 0) :
    (∀ i : ℕ, i < e →
      ∀ s ∈ perfectoidIdeal (CompletedTower A t p) p hperf
        (algebraMap A (CompletedTower A t p) g),
        HomologicalAlgebra.localCohomologyScalarEndomorphism (maximalIdeal D) i C
          (algebraMap (CompletedTower A t p) C s) = 0) ∧
    (∀ n : ℕ,
      let _ := stageAlgebra_isLocalRing_of_parameters A D t p hsop n
      ∀ y : Fin e → StageAlgebra A D t p n,
        IsSystemOfParameters (StageAlgebra A D t p n) y → ∀ i : ℕ, 0 < i →
          let _ := Module.compHom (koszulHomologySelf (φ n ∘ y) i)
            (algebraMap (CompletedTower A t p) C)
          perfectoidIdeal (CompletedTower A t p) p hperf
            (algebraMap A (CompletedTower A t p) g) ≤
              Module.annihilator (CompletedTower A t p) (koszulHomologySelf (φ n ∘ y) i)) := by
  apply conditional_corollary_4_0_4_of_powerTorsion_and_extension t p hsop
    (fun k => isKoszulResolution_all_powers t ht
      (isWeaklyRegular_of_span_eq_maximalIdeal A t ht hdim) k) φ hφ hperf
    (algebraMap A (CompletedTower A t p) g) hC (algebraMap (CompletedTower A t p) C)
    (p : CompletedTower A t p) j₀ ?_ hI hExt hTor
  simp only [htp, map_natCast]

end SerrePositivity.CLMST
