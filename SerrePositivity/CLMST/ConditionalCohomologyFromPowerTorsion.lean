module

public import SerrePositivity.CLMST.AllModuleAlmostTor
public import SerrePositivity.CLMST.ConditionalCohomologyVanishing

/-!
# 全加群帰着から KL-Q の条件付き両消滅へ

## 概要
CLMST v4 Thm 4.0.3(a), pp.27–28 の帰着を Cor 4.0.4, p.28 に接続する。

## 方針
全 A 加群版 Tor 零化を二入力から証明し、既存の両消滅定理へ渡す。

## 規約
p 冪ねじれ試験と BS 著者版 Prop 10.2, p.78 型の拡大閉性は明示引数。
商へのイデアル像の冪等性 hI は従来どおり残す。

## 使われ方
S を CompletedTower に、ψ を元の係数作用に具体化できる。
全段・任意のパラメータ系・全正次数の Koszul 結論を保つ。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
open CategoryTheory Section2

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
      IsIdempotentElem ((perfectoidIdeal S p hS g).map (Ideal.Quotient.mk (Ideal.span {a ^ k}))))
    (hExt : ∀ (X : ShortComplex (ModuleCat.{u} S)), X.ShortExact →
      DerivedCompletion.IsModuleComplete S (p : S) X.X₁ →
      DerivedCompletion.IsModuleComplete S (p : S) X.X₂ →
      DerivedCompletion.IsModuleComplete S (p : S) X.X₃ →
      Almost.IsAlmostZero (perfectoidIdeal S p hS g) X.X₁ →
      Almost.IsAlmostZero (perfectoidIdeal S p hS g) X.X₃ →
      Almost.IsAlmostZero (perfectoidIdeal S p hS g) X.X₂)
    (hTor : ∀ (N : ModuleCat.{u} A) (k : ℕ),
      (∀ x : N, (p : A) ^ k • x = 0) → ∀ j : ℕ, 0 < j →
        ∀ s ∈ (perfectoidIdeal S p hS g), torCoefficientScalarEndomorphism C N j (ψ s) = 0) :
    (∀ i : ℕ, i < e → ∀ s ∈ (perfectoidIdeal S p hS g),
      HomologicalAlgebra.localCohomologyScalarEndomorphism
        (IsLocalRing.maximalIdeal D) i C (ψ s) = 0) ∧
    (∀ n : ℕ,
      let _ := Section2.stageAlgebra_isLocalRing_of_parameters A D t p hsop n
      ∀ (y : Fin e → Section2.StageAlgebra A D t p n),
        IsSystemOfParameters (Section2.StageAlgebra A D t p n) y → ∀ i : ℕ, 0 < i →
          let _ := Module.compHom (koszulHomologySelf (φ n ∘ y) i) ψ
          (perfectoidIdeal S p hS g) ≤ Module.annihilator S (koszulHomologySelf (φ n ∘ y) i)) := by
  exact conditional_corollary_4_0_4 t p hsop hres φ hφ ψ
    (perfectoidIdeal S p hS g) a j₀ ha hI
    (perfectoidIdeal_allModule_tor_annihilated p hS g ψ hC hExt hTor)

end SerrePositivity.CLMST
