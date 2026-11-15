module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PowerTorsionTor
public import SerrePositivity.CommutativeAlgebra.Almost.Basic
public import SerrePositivity.BhattScholze.PerfectoidIdeal.Basic
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.IntegralPerfectoid
public import SerrePositivity.CLMST.KoszulAnnihilation
public import SerrePositivity.CommutativeAlgebra.RootTower.Completion
public import SerrePositivity.CommutativeAlgebra.RegularLocalRing.Basic
public import SerrePositivity.BhattScholze.Almost.PerfectoidAlmost

/-! # 全加群の Tor の消滅

## 概要

p 冪ねじれの係数の零化と、完備な almost 零加群の拡大閉性から、perfectoid イデアルが全ての加群の正の次数の Tor を零化することへ帰着する（`allModule_tor_annihilated_of_powerTorsion_and_extension`）。拡大閉性に BS 著者版 Proposition 10.2（p.78）を供給し、完備化した根の塔の上で具体化して、Cor 4.0.4 の二つの消滅へ条件つきで接続する。
BS 著者版 Proposition 10.2 の拡大閉性を、CLMST の高次 Tor の零化へ渡す。

## 方針

有限生成部分加群の有向余極限、正則局所環の上の有限自由分解、有界ねじれの塔の比較、Milnor 短完全列を使う。

## 規約

CLMST（arXiv:2209.04046v4）Thm 4.0.3(a)（pp.27–28）の全加群版。主経路（Cor 4.0.4 の証明）からは使われないが、論文の内容なので残す（2026-10-30 決定）。p 冪ねじれの検査は明示的な引数。旧 `CLMST/AllModuleAlmostTor`・`AllModuleTorFromBS`・`CompletedTowerAllModuleTor`・`ConditionalCohomologyFromPowerTorsion`・`KLAllModule`。

## 使われ方

いまは利用者がない。
-/

@[expose] public noncomputable section

universe u

section AllModuleAlmostTorPart

namespace SerrePositivity.CLMST
open _root_.CategoryTheory _root_.SerrePositivity.DerivedCompletion _root_.SerrePositivity.Almost

/-- 概要：p 冪ねじれ試験と完備 almost 拡大閉性から、任意加群の高次 Tor を零化する。
方針：CLMST Thm 4.0.3(a), pp.27–28 の Milnor 列と有限生成部分加群への帰着を使う。
規約：hTor の指数は全自然数で、hExt は実短完全列の三項の完備性を受け取る。
使われ方：perfectoid ideal の入口と条件付き Cor 4.0.4 の hTor を構成する。 -/
theorem allModule_tor_annihilated_of_powerTorsion_and_extension
    {A R C : Type u} [CommRing A] [IsRegularLocalRing A]
    [CommRing R] [CommRing C] [Algebra A C]
    (p : ℕ) (ψ : R →+* C) (I : Ideal R)
    (hC : IsModuleComplete A (p : A) (ModuleCat.of A C))
    (hExt : ∀ (S : ShortComplex (ModuleCat.{u} R)), S.ShortExact →
      IsModuleComplete R (p : R) S.X₁ → IsModuleComplete R (p : R) S.X₂ →
      IsModuleComplete R (p : R) S.X₃ →
      IsAlmostZero I S.X₁ → IsAlmostZero I S.X₃ → IsAlmostZero I S.X₂)
    (hTor : ∀ (N : ModuleCat.{u} A) (k : ℕ),
      (∀ x : N, (p : A) ^ k • x = 0) → ∀ j : ℕ, 0 < j →
        ∀ s ∈ I, torCoefficientScalarEndomorphism C N j (ψ s) = 0) :
    ∀ (N : ModuleCat.{u} A) (j : ℕ), 0 < j →
      ∀ s ∈ I, torCoefficientScalarEndomorphism C N j (ψ s) = 0 := by
  exact tor_eq_zero_of_power_torsion_and_complete_extensions p C R ψ I hC
    hExt (fun N k _hk hN => hTor N k hN)

/-- 概要：perfectoid 係数環について、指定された BS 著者版 Proposition 10.2 型の仮定とねじれ試験から
全 A 加群版の almost Tor 零化を得る（CLMST Thm 4.0.3(a), pp.27–28）。
方針：係数環の perfectoid 性から導来 p 完備性を供給し、前定理へ適用する。
規約：hExt はレーン B の公開予定型そのものであり、成立はここでは証明しない。
使われ方：R を CompletedTower、I を元の perfectoid ideal とする KL-Q の入口。 -/
theorem perfectoidIdeal_allModule_tor_annihilated
    {A R C : Type u} [CommRing A] [IsRegularLocalRing A]
    [CommRing R] [CommRing C] [Algebra A C]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) (g : R)
    (ψ : R →+* C) (hC : IsIntegralPerfectoid C p)
    (hExt : ∀ (S : ShortComplex (ModuleCat.{u} R)), S.ShortExact →
      IsModuleComplete R (p : R) S.X₁ → IsModuleComplete R (p : R) S.X₂ →
      IsModuleComplete R (p : R) S.X₃ →
      IsAlmostZero (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g) S.X₁ →
      IsAlmostZero (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g) S.X₃ →
      IsAlmostZero (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g) S.X₂)
    (hTor : ∀ (N : ModuleCat.{u} A) (k : ℕ),
      (∀ x : N, (p : A) ^ k • x = 0) → ∀ j : ℕ, 0 < j →
        ∀ s ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g,
          torCoefficientScalarEndomorphism C N j (ψ s) = 0) :
    ∀ (N : ModuleCat.{u} A) (j : ℕ), 0 < j →
      ∀ s ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g,
        torCoefficientScalarEndomorphism C N j (ψ s) = 0 := by
  exact allModule_tor_annihilated_of_powerTorsion_and_extension p ψ _
    (hC.isModuleComplete_algebra A C p) hExt hTor

end SerrePositivity.CLMST

end AllModuleAlmostTorPart

section ConditionalCohomologyFromPowerTorsionPart

namespace SerrePositivity.CLMST
open _root_.CategoryTheory _root_.SerrePositivity.Section2

/-- 概要：p 冪ねじれ版と完備 almost 拡大閉性から Cor 4.0.4 の両結論を得る。
方針：Thm 4.0.3(a), pp.27–28 の全加群帰着を既存 conditional_corollary_4_0_4 に渡す。
規約：hI と元の φ・ψ・パラメータ系を保ち、全加群版を追加の仮定にしない。
使われ方：KL-Q の条件付き合流。二入力の実供給と原典引用の置換は未完了。 -/
theorem conditional_corollary_4_0_4_of_powerTorsion_and_extension
    {A D C S : Type u} [CommRing A] [IsRegularLocalRing A]
    [CommRing D] [IsLocalRing D] [IsNoetherianRing D] [CommRing C] [CommRing S]
    [Algebra A D] [Module.Finite A D] [Algebra A C] [Algebra D C] [IsScalarTower A D C]
    {e : ℕ} (t : Fin e → A) (p : ℕ) [Fact p.Prime]
    (hsop : IsSystemOfParameters D (algebraMap A D ∘ t))
    (hres : ∀ k : ℕ, IsKoszulResolution (fun j => t j ^ k))
    (φ : ∀ n : ℕ, Section2.StageAlgebra A D t p n →+* C)
    (hφ : ∀ (n : ℕ) (x : A), φ n (algebraMap D (Section2.StageAlgebra A D t p n)
      (algebraMap A D x)) = algebraMap A C x)
    (hS : IsIntegralPerfectoid S p) (g : S) (hC : IsIntegralPerfectoid C p)
    (ψ : S →+* C) (a : S) (j₀ : Fin e)
    (ha : ψ a = algebraMap A C (t j₀))
    (hI : ∀ k : ℕ, 0 < k →
      IsIdempotentElem ((_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal S p hS g).map (Ideal.Quotient.mk (Ideal.span {a ^ k}))))
    (hExt : ∀ (X : ShortComplex (ModuleCat.{u} S)), X.ShortExact →
      DerivedCompletion.IsModuleComplete S (p : S) X.X₁ →
      DerivedCompletion.IsModuleComplete S (p : S) X.X₂ →
      DerivedCompletion.IsModuleComplete S (p : S) X.X₃ →
      Almost.IsAlmostZero (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal S p hS g) X.X₁ →
      Almost.IsAlmostZero (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal S p hS g) X.X₃ →
      Almost.IsAlmostZero (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal S p hS g) X.X₂)
    (hTor : ∀ (N : ModuleCat.{u} A) (k : ℕ),
      (∀ x : N, (p : A) ^ k • x = 0) → ∀ j : ℕ, 0 < j →
        ∀ s ∈ (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal S p hS g), torCoefficientScalarEndomorphism C N j (ψ s) = 0) :
    (∀ i : ℕ, i < e → ∀ s ∈ (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal S p hS g),
      HomologicalAlgebra.localCohomologyScalarEndomorphism
        (IsLocalRing.maximalIdeal D) i C (ψ s) = 0) ∧
    (∀ n : ℕ,
      let _ := Section2.stageAlgebra_isLocalRing_of_parameters A D t p hsop n
      ∀ (y : Fin e → Section2.StageAlgebra A D t p n),
        IsSystemOfParameters (Section2.StageAlgebra A D t p n) y → ∀ i : ℕ, 0 < i →
          let _ := Module.compHom (koszulHomologySelf (φ n ∘ y) i) ψ
          (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal S p hS g) ≤ Module.annihilator S (koszulHomologySelf (φ n ∘ y) i)) := by
  exact conditional_corollary_4_0_4 t p hsop hres φ hφ ψ
    (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal S p hS g) a j₀ ha hI
    (perfectoidIdeal_allModule_tor_annihilated p hS g ψ hC hExt hTor)

end SerrePositivity.CLMST

end ConditionalCohomologyFromPowerTorsionPart

section CompletedTowerAllModuleTorPart

namespace SerrePositivity.CLMST
open _root_.CategoryTheory _root_.SerrePositivity.Section2 _root_.IsLocalRing
variable {A C : Type u} [CommRing A] [IsRegularLocalRing A] [CommRing C]
    {e : ℕ} (t : Fin e → A) (p : ℕ) [Fact p.Prime]
    [Algebra A C] [Algebra (CompletedTower A t p) C]
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p) (hC : IsIntegralPerfectoid C p)
    (g : A)

include hC

/-- 概要：指定した完備根の塔の ideal の全元が任意 A 加群の高次 Tor を消す。
方針：Thm 4.0.3(a), pp.27–28 の全加群帰着へ R=CompletedTower と元の作用を代入する。
規約：p 冪ねじれ試験と BS 著者版 Proposition 10.2 型の拡大閉性の型を変えない。
使われ方：実際の塔上で KL-Q に渡す hTor。二仮定の実供給は主張しない。 -/
theorem completedTower_allModule_tor_annihilated
    (hExt : ∀ (X : ShortComplex (ModuleCat.{u} (CompletedTower A t p))), X.ShortExact →
      DerivedCompletion.IsModuleComplete (CompletedTower A t p) (p : CompletedTower A t p) X.X₁ →
      DerivedCompletion.IsModuleComplete (CompletedTower A t p) (p : CompletedTower A t p) X.X₂ →
      DerivedCompletion.IsModuleComplete (CompletedTower A t p) (p : CompletedTower A t p) X.X₃ →
      Almost.IsAlmostZero (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf
        (algebraMap A (CompletedTower A t p) g)) X.X₁ →
      Almost.IsAlmostZero (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf
        (algebraMap A (CompletedTower A t p) g)) X.X₃ →
      Almost.IsAlmostZero (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf
        (algebraMap A (CompletedTower A t p) g)) X.X₂)
    (hTor : ∀ (N : ModuleCat.{u} A) (k : ℕ),
      (∀ x : N, (p : A) ^ k • x = 0) → ∀ j : ℕ, 0 < j →
        ∀ s ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf
          (algebraMap A (CompletedTower A t p) g),
          torCoefficientScalarEndomorphism C N j (algebraMap (CompletedTower A t p) C s) = 0) :
    ∀ (N : ModuleCat.{u} A) (j : ℕ), 0 < j →
      ∀ s ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf
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
    (φ : ∀ n : ℕ, Section2.StageAlgebra A D t p n →+* C)
    (hφ : ∀ (n : ℕ) (x : A), φ n (algebraMap D (Section2.StageAlgebra A D t p n)
      (algebraMap A D x)) = algebraMap A C x)
    (j₀ : Fin e) (htp : t j₀ = (p : A))
    (hI : ∀ k : ℕ, 0 < k → IsIdempotentElem
      ((_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf
        (algebraMap A (CompletedTower A t p) g)).map
          (Ideal.Quotient.mk (Ideal.span {(p : CompletedTower A t p) ^ k}))))
    (hExt : ∀ (X : ShortComplex (ModuleCat.{u} (CompletedTower A t p))), X.ShortExact →
      DerivedCompletion.IsModuleComplete (CompletedTower A t p) (p : CompletedTower A t p) X.X₁ →
      DerivedCompletion.IsModuleComplete (CompletedTower A t p) (p : CompletedTower A t p) X.X₂ →
      DerivedCompletion.IsModuleComplete (CompletedTower A t p) (p : CompletedTower A t p) X.X₃ →
      Almost.IsAlmostZero (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf
        (algebraMap A (CompletedTower A t p) g)) X.X₁ →
      Almost.IsAlmostZero (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf
        (algebraMap A (CompletedTower A t p) g)) X.X₃ →
      Almost.IsAlmostZero (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf
        (algebraMap A (CompletedTower A t p) g)) X.X₂)
    (hTor : ∀ (N : ModuleCat.{u} A) (k : ℕ),
      (∀ x : N, (p : A) ^ k • x = 0) → ∀ j : ℕ, 0 < j →
        ∀ s ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf
          (algebraMap A (CompletedTower A t p) g),
          torCoefficientScalarEndomorphism C N j (algebraMap (CompletedTower A t p) C s) = 0) :
    (∀ i : ℕ, i < e →
      ∀ s ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf
        (algebraMap A (CompletedTower A t p) g),
        HomologicalAlgebra.localCohomologyScalarEndomorphism (maximalIdeal D) i C
          (algebraMap (CompletedTower A t p) C s) = 0) ∧
    (∀ n : ℕ,
      let _ := Section2.stageAlgebra_isLocalRing_of_parameters A D t p hsop n
      ∀ y : Fin e → Section2.StageAlgebra A D t p n,
        IsSystemOfParameters (Section2.StageAlgebra A D t p n) y → ∀ i : ℕ, 0 < i →
          let _ := Module.compHom (koszulHomologySelf (φ n ∘ y) i)
            (algebraMap (CompletedTower A t p) C)
          _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf
            (algebraMap A (CompletedTower A t p) g) ≤
              Module.annihilator (CompletedTower A t p) (koszulHomologySelf (φ n ∘ y) i)) := by
  apply conditional_corollary_4_0_4_of_powerTorsion_and_extension t p hsop
    (fun k => isKoszulResolution_all_powers t ht
      (isWeaklyRegular_of_span_eq_maximalIdeal A t ht hdim) k) φ hφ hperf
    (algebraMap A (CompletedTower A t p) g) hC (algebraMap (CompletedTower A t p) C)
    (p : CompletedTower A t p) j₀ ?_ hI hExt hTor
  simp only [htp, map_natCast]

end SerrePositivity.CLMST

end CompletedTowerAllModuleTorPart

section AllModuleTorFromBSPart

namespace SerrePositivity.CLMST
open _root_.CategoryTheory _root_.SerrePositivity.Section2 _root_.IsLocalRing

/-- 概要：p 冪ねじれ版だけから全 A 加群の高次 Tor 零化へ帰着する。
方針：CLMST Thm 4.0.3(a), pp.27–28 の Milnor 証明に 導来完備 almost 零加群の拡大閉性の証明を渡す。
規約：有限生成性・完備性を任意 N に追加せず、全自然数 k の試験を保つ。
使われ方：KL-Q へ渡す全加群 hTor。ねじれ版自体は未供給の明示入力である。 -/
theorem perfectoidIdeal_allModule_tor_annihilated_of_powerTorsion
    {A R C : Type u} [CommRing A] [IsRegularLocalRing A]
    [CommRing R] [CommRing C] [Algebra A C]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) (g : R)
    (ψ : R →+* C) (hC : IsIntegralPerfectoid C p)
    (hTor : ∀ (N : ModuleCat.{u} A) (k : ℕ),
      (∀ x : N, (p : A) ^ k • x = 0) → ∀ j : ℕ, 0 < j →
        ∀ s ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g,
          torCoefficientScalarEndomorphism C N j (ψ s) = 0) :
    ∀ (N : ModuleCat.{u} A) (j : ℕ), 0 < j →
      ∀ s ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g,
        torCoefficientScalarEndomorphism C N j (ψ s) = 0 := by
  exact perfectoidIdeal_allModule_tor_annihilated p hR g ψ hC
    (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal_isAlmostZero_extension R p hR g) hTor

/-- 概要：ねじれ版 Tor 零化から局所コホモロジー・全段 Koszul の条件付き両消滅を得る。
方針：BS 著者版 Proposition 10.2, p.78 を受領して拡大閉性を解消し、CLMST Cor 4.0.4, p.28 へ合流する。
規約：hI、元の φ・ψ と全有限段・全パラメータ系の量化を保つ。
使われ方：KL-Q の条件付き入口。Cor 4.0.4 の既存引用は置換しない。 -/
theorem conditional_corollary_4_0_4_of_powerTorsion
    {A D C S : Type u} [CommRing A] [IsRegularLocalRing A]
    [CommRing D] [IsLocalRing D] [IsNoetherianRing D] [CommRing C] [CommRing S]
    [Algebra A D] [Module.Finite A D] [Algebra A C] [Algebra D C] [IsScalarTower A D C]
    {e : ℕ} (t : Fin e → A) (p : ℕ) [Fact p.Prime]
    (hsop : IsSystemOfParameters D (algebraMap A D ∘ t))
    (hres : ∀ k : ℕ, IsKoszulResolution (fun j => t j ^ k))
    (φ : ∀ n : ℕ, Section2.StageAlgebra A D t p n →+* C)
    (hφ : ∀ (n : ℕ) (x : A), φ n (algebraMap D (Section2.StageAlgebra A D t p n)
      (algebraMap A D x)) = algebraMap A C x)
    (hS : IsIntegralPerfectoid S p) (g : S) (hC : IsIntegralPerfectoid C p)
    (ψ : S →+* C) (a : S) (j₀ : Fin e)
    (ha : ψ a = algebraMap A C (t j₀))
    (hI : ∀ k : ℕ, 0 < k →
      IsIdempotentElem ((_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal S p hS g).map (Ideal.Quotient.mk (Ideal.span {a ^ k}))))
    (hTor : ∀ (N : ModuleCat.{u} A) (k : ℕ),
      (∀ x : N, (p : A) ^ k • x = 0) → ∀ j : ℕ, 0 < j →
        ∀ s ∈ (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal S p hS g), torCoefficientScalarEndomorphism C N j (ψ s) = 0) :
    (∀ i : ℕ, i < e → ∀ s ∈ (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal S p hS g),
      HomologicalAlgebra.localCohomologyScalarEndomorphism
        (IsLocalRing.maximalIdeal D) i C (ψ s) = 0) ∧
    (∀ n : ℕ,
      let _ := Section2.stageAlgebra_isLocalRing_of_parameters A D t p hsop n
      ∀ (y : Fin e → Section2.StageAlgebra A D t p n),
        IsSystemOfParameters (Section2.StageAlgebra A D t p n) y → ∀ i : ℕ, 0 < i →
          let _ := Module.compHom (koszulHomologySelf (φ n ∘ y) i) ψ
          (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal S p hS g) ≤ Module.annihilator S (koszulHomologySelf (φ n ∘ y) i)) := by
  exact conditional_corollary_4_0_4_of_powerTorsion_and_extension
    t p hsop hres φ hφ hS g hC ψ a j₀ ha hI
    (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal_isAlmostZero_extension S p hS g) hTor

variable {A C : Type u} [CommRing A] [IsRegularLocalRing A] [CommRing C]
    {e : ℕ} (t : Fin e → A) (p : ℕ) [Fact p.Prime]
    [Algebra A C] [Algebra (CompletedTower A t p) C]
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p) (hC : IsIntegralPerfectoid C p)
    (g : A)

include hC

/-- 概要：元の CompletedTower で、ねじれ試験から KL-Q の両結論へ渡す。
方針：原典 CLMST Thm 4.0.3(a), pp.27–28・Cor 4.0.4, p.28 の適用に
証明済み BS 著者版 Proposition 10.2, p.78 を供給する。
規約：元の塔作用、パラメータ、全段写像を保ち、hI とねじれ試験のみを残す。
使われ方：拡大閉性の仮定解消済みの実塔の入口。KL-Q 全体の完成とは数えない。 -/
theorem completedTower_cohomology_vanishing_of_powerTorsion
    {D : Type u} [CommRing D] [IsLocalRing D] [IsNoetherianRing D]
    [Algebra A D] [Module.Finite A D] [Algebra D C] [IsScalarTower A D C]
    (ht : Ideal.span (Set.range t) = maximalIdeal A) (hdim : ringKrullDim A = e)
    (hsop : IsSystemOfParameters D (algebraMap A D ∘ t))
    (φ : ∀ n : ℕ, Section2.StageAlgebra A D t p n →+* C)
    (hφ : ∀ (n : ℕ) (x : A), φ n (algebraMap D (Section2.StageAlgebra A D t p n)
      (algebraMap A D x)) = algebraMap A C x)
    (j₀ : Fin e) (htp : t j₀ = (p : A))
    (hI : ∀ k : ℕ, 0 < k → IsIdempotentElem
      ((_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf
        (algebraMap A (CompletedTower A t p) g)).map
          (Ideal.Quotient.mk (Ideal.span {(p : CompletedTower A t p) ^ k}))))
    (hTor : ∀ (N : ModuleCat.{u} A) (k : ℕ),
      (∀ x : N, (p : A) ^ k • x = 0) → ∀ j : ℕ, 0 < j →
        ∀ s ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf
          (algebraMap A (CompletedTower A t p) g),
          torCoefficientScalarEndomorphism C N j (algebraMap (CompletedTower A t p) C s) = 0) :
    (∀ i : ℕ, i < e →
      ∀ s ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf
        (algebraMap A (CompletedTower A t p) g),
        HomologicalAlgebra.localCohomologyScalarEndomorphism (maximalIdeal D) i C
          (algebraMap (CompletedTower A t p) C s) = 0) ∧
    (∀ n : ℕ,
      let _ := Section2.stageAlgebra_isLocalRing_of_parameters A D t p hsop n
      ∀ y : Fin e → Section2.StageAlgebra A D t p n,
        IsSystemOfParameters (Section2.StageAlgebra A D t p n) y → ∀ i : ℕ, 0 < i →
          let _ := Module.compHom (koszulHomologySelf (φ n ∘ y) i)
            (algebraMap (CompletedTower A t p) C)
          _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf
            (algebraMap A (CompletedTower A t p) g) ≤
              Module.annihilator (CompletedTower A t p) (koszulHomologySelf (φ n ∘ y) i)) := by
  exact completedTower_cohomology_vanishing_of_powerTorsion_and_extension
    t p hperf hC g ht hdim hsop φ hφ j₀ htp hI
    (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal_isAlmostZero_extension (CompletedTower A t p) p hperf
      (algebraMap A (CompletedTower A t p) g)) hTor

end SerrePositivity.CLMST

end AllModuleTorFromBSPart

section KLAllModulePart

end KLAllModulePart
