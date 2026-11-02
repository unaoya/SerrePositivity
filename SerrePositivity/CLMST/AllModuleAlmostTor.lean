module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PowerTorsionTorExtension
public import SerrePositivity.CommutativeAlgebra.Almost.Basic
public import SerrePositivity.BhattScholze.PerfectoidIdeal.Basic
public import SerrePositivity.CommutativeAlgebra.PerfectoidDerivedComplete

/-!
# Thm 4.0.3(a) の全加群への帰着

## 概要
CLMST v4, Theorem 4.0.3(a), pp.27–28 の全加群版への帰着を、
p 冪ねじれ係数の零化と完備 almost 加群の拡大閉性を明示して与える。

## 方針
既存の有限生成部分加群の有向余極限、正則局所環上の有限自由分解、
有界ねじれの塔比較、および実係数線形 Milnor 短完全列を再利用する。
BS 著者版 Proposition 10.2, p.78 の適用部分は定理の引数であり、引用しない。

## 規約
係数源 R と正則局所基底 A は異なってよく、元の ψ による作用を保つ。
ねじれ試験の指数 k は 0 も含む。任意加群に有限生成性や完備性を要求しない。

## 使われ方
KL-Q の条件付き両消滅に渡す全 A 加群の hTor を供給する。
Cor 8.12 や excision の定式化・成立を前提にしない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
open CategoryTheory DerivedCompletion Almost

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

/-- 概要：perfectoid 係数環について、指定された Prop 10.2 型の仮定とねじれ試験から
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
      IsAlmostZero (perfectoidIdeal R p hR g) S.X₁ →
      IsAlmostZero (perfectoidIdeal R p hR g) S.X₃ →
      IsAlmostZero (perfectoidIdeal R p hR g) S.X₂)
    (hTor : ∀ (N : ModuleCat.{u} A) (k : ℕ),
      (∀ x : N, (p : A) ^ k • x = 0) → ∀ j : ℕ, 0 < j →
        ∀ s ∈ perfectoidIdeal R p hR g,
          torCoefficientScalarEndomorphism C N j (ψ s) = 0) :
    ∀ (N : ModuleCat.{u} A) (j : ℕ), 0 < j →
      ∀ s ∈ perfectoidIdeal R p hR g,
        torCoefficientScalarEndomorphism C N j (ψ s) = 0 := by
  exact allModule_tor_annihilated_of_powerTorsion_and_extension p ψ _
    (hC.isModuleComplete_algebra A C p) hExt hTor

end SerrePositivity.CLMST
