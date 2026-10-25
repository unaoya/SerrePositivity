module

public import SerrePositivity.CLMST.CompletedTowerAllModuleTor
public import SerrePositivity.BhattScholze.Results.PerfectoidAlmostExtension

/-!
# BS Prop 10.2 を受領した全加群 Tor と条件付き KL-Q

## 概要
CLMST v4 Thm 4.0.3(a), pp.27–28 の全加群帰着に、証明済みの
BS 著者版 Prop 10.2, p.78 の拡大閉性を供給する。

## 方針
レーン B の perfectoidIdeal_isAlmostZero_extension を指定された型のまま適用し、
実 Milnor 列による既存の帰着の hExt 引数を解消する。

## 規約
p 冪ねじれ試験の入力は型を変えず残す。Cor 8.12 の主張や excision は使わない。

## 使われ方
KL-Q の両結論へ、全加群 Tor や拡大閉性を呼出し側に要求せず接続する。
(a) の実供給と既存文献入力の置換を完了したとは扱わない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
open CategoryTheory Section2 IsLocalRing

/-- 概要：p 冪ねじれ版だけから全 A 加群の高次 Tor 零化へ帰着する。
方針：CLMST Thm 4.0.3(a), pp.27–28 の Milnor 証明に BS Prop 10.2, p.78 の実証明を渡す。
規約：有限生成性・完備性を任意 N に追加せず、全自然数 k の試験を保つ。
使われ方：KL-Q へ渡す全加群 hTor。ねじれ版自体は未供給の明示入力である。 -/
theorem perfectoidIdeal_allModule_tor_annihilated_of_powerTorsion
    {A R C : Type u} [CommRing A] [IsRegularLocalRing A]
    [CommRing R] [CommRing C] [Algebra A C]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) (g : R)
    (ψ : R →+* C) (hC : IsIntegralPerfectoid C p)
    (hTor : ∀ (N : ModuleCat.{u} A) (k : ℕ),
      (∀ x : N, (p : A) ^ k • x = 0) → ∀ j : ℕ, 0 < j →
        ∀ s ∈ perfectoidIdeal R p hR g,
          torCoefficientScalarEndomorphism C N j (ψ s) = 0) :
    ∀ (N : ModuleCat.{u} A) (j : ℕ), 0 < j →
      ∀ s ∈ perfectoidIdeal R p hR g,
        torCoefficientScalarEndomorphism C N j (ψ s) = 0 := by
  exact perfectoidIdeal_allModule_tor_annihilated p hR g ψ hC
    (BhattScholze.perfectoidIdeal_isAlmostZero_extension R p hR g) hTor

/-- 概要：ねじれ版 Tor 零化から局所コホモロジー・全段 Koszul の条件付き両消滅を得る。
方針：BS Prop 10.2, p.78 を受領して拡大閉性を解消し、CLMST Cor 4.0.4, p.28 へ合流する。
規約：hI、元の φ・ψ と全有限段・全パラメータ系の量化を保つ。
使われ方：KL-Q の条件付き入口。Cor 4.0.4 の既存引用は置換しない。 -/
theorem conditional_corollary_4_0_4_of_powerTorsion
    {A D C S : Type u} [CommRing A] [IsRegularLocalRing A]
    [CommRing D] [IsLocalRing D] [IsNoetherianRing D] [CommRing C] [CommRing S]
    [Algebra A D] [Module.Finite A D] [Algebra A C] [Algebra D C] [IsScalarTower A D C]
    {e : ℕ} (t : Fin e → A) (p : ℕ) [Fact p.Prime]
    (hsop : IsSystemOfParameters D (algebraMap A D ∘ t))
    (hres : ∀ k : ℕ, IsKoszulResolution (fun j => t j ^ k))
    (φ : ∀ n : ℕ, StageAlgebra A D t p n →+* C)
    (hφ : ∀ (n : ℕ) (x : A), φ n (algebraMap D (StageAlgebra A D t p n)
      (algebraMap A D x)) = algebraMap A C x)
    (hS : IsIntegralPerfectoid S p) (g : S) (hC : IsIntegralPerfectoid C p)
    (ψ : S →+* C) (a : S) (j₀ : Fin e)
    (ha : ψ a = algebraMap A C (t j₀))
    (hI : ∀ k : ℕ, 0 < k →
      IsIdempotentElem ((perfectoidIdeal S p hS g).map (Ideal.Quotient.mk (Ideal.span {a ^ k}))))
    (hTor : ∀ (N : ModuleCat.{u} A) (k : ℕ),
      (∀ x : N, (p : A) ^ k • x = 0) → ∀ j : ℕ, 0 < j →
        ∀ s ∈ (perfectoidIdeal S p hS g), torCoefficientScalarEndomorphism C N j (ψ s) = 0) :
    (∀ i : ℕ, i < e → ∀ s ∈ (perfectoidIdeal S p hS g),
      HomologicalAlgebra.localCohomologyScalarEndomorphism
        (IsLocalRing.maximalIdeal D) i C (ψ s) = 0) ∧
    (∀ n : ℕ,
      let _ := stageAlgebra_isLocalRing_of_parameters A D t p hsop n
      ∀ (y : Fin e → StageAlgebra A D t p n),
        IsSystemOfParameters (StageAlgebra A D t p n) y → ∀ i : ℕ, 0 < i →
          let _ := Module.compHom (koszulHomologySelf (φ n ∘ y) i) ψ
          (perfectoidIdeal S p hS g) ≤ Module.annihilator S (koszulHomologySelf (φ n ∘ y) i)) := by
  exact conditional_corollary_4_0_4_of_powerTorsion_and_extension
    t p hsop hres φ hφ hS g hC ψ a j₀ ha hI
    (BhattScholze.perfectoidIdeal_isAlmostZero_extension S p hS g) hTor

variable {A C : Type u} [CommRing A] [IsRegularLocalRing A] [CommRing C]
    {e : ℕ} (t : Fin e → A) (p : ℕ) [Fact p.Prime]
    [Algebra A C] [Algebra (CompletedTower A t p) C]
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p) (hC : IsIntegralPerfectoid C p)
    (g : A)

include hC

/-- 概要：元の CompletedTower で、ねじれ試験から KL-Q の両結論へ渡す。
方針：原典 CLMST Thm 4.0.3(a), pp.27–28・Cor 4.0.4, p.28 の適用に
証明済み BS Prop 10.2, p.78 を供給する。
規約：元の塔作用、パラメータ、全段写像を保ち、hI とねじれ試験のみを残す。
使われ方：拡大閉性の仮定解消済みの実塔の入口。KL-Q 全体の完成とは数えない。 -/
theorem completedTower_cohomology_vanishing_of_powerTorsion
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
  exact completedTower_cohomology_vanishing_of_powerTorsion_and_extension
    t p hperf hC g ht hdim hsop φ hφ j₀ htp hI
    (BhattScholze.perfectoidIdeal_isAlmostZero_extension (CompletedTower A t p) p hperf
      (algebraMap A (CompletedTower A t p) g)) hTor

end SerrePositivity.CLMST
