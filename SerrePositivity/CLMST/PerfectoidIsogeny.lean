module

public import SerrePositivity.CLMST.Inputs.PerfectoidIsogeny

/-! # 導来錐の零射から標準写像の核・余核の制御へ

CLMST Prop 2.4.7 は錐上の実導来射の零性として引用する。
その主張を、標準写像の核・余核の同じ冪による零化へ証明して接続する。
始域で g の作用が単射である場合には標準写像の単射性も導く。
その正則性を原典の引用へ混ぜず、具体的な適用で確認する条件として保持する。
-/

@[expose] public section
universe u
namespace SerrePositivity.CLMST
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Algebra.FinitePresentation R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (J : Ideal R) (hJ : J.FG)
    (hEtale : ∀ g ∈ J, let _ := GenericEtale.awayAlgebra R S g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R S g)))
    (hbounded : ∃ N : ℕ, ∀ (n : ℕ) (s : S),
      (p : S) ^ n * s = 0 → (p : S) ^ N * s = 0)

include hJ hEtale hbounded in
/-- 原典の錐の零射から、各 g∈J に対して核・余核を同じ冪で零化できる。 -/
theorem exists_pow_annihilates_ker_coker (g : R) (hg : g ∈ J) :
    ∃ N : ℕ,
      (∀ x : (perfectoidizationModuleMap R S p hR).ker, (g ^ N) • x = 0) ∧
      (∀ x : (Perfectoidization R S p hR) ⧸
        (perfectoidizationModuleMap R S p hR).range, (g ^ N) • x = 0) := by
  obtain ⟨N, hN⟩ := Inputs.proposition_2_4_7 R S p hR J hJ hEtale hbounded g hg
  exact ⟨N, moduleMapCone_pow_scalar_eq_zero_annihilates R
    (perfectoidizationModuleMap R S p hR) g N hN⟩

include hJ hEtale hbounded in
/-- 始域で g が正則なら標準写像は単射で、余核を g の同じ冪で消せる。
単射性そのものは外部引用の結論に追加せず、錐と正則性から証明する。 -/
theorem injective_and_exists_pow_annihilates_coker (g : R) (hg : g ∈ J)
    (hregular : IsSMulRegular S g) :
    Function.Injective (perfectoidizationModuleMap R S p hR) ∧
      ∃ N : ℕ, ∀ x : (Perfectoidization R S p hR) ⧸
        (perfectoidizationModuleMap R S p hR).range, (g ^ N) • x = 0 := by
  obtain ⟨N, hN⟩ := Inputs.proposition_2_4_7 R S p hR J hJ hEtale hbounded g hg
  obtain ⟨hinj, hcoker⟩ := moduleMapCone_pow_scalar_eq_zero_injective_of_regular R
    (perfectoidizationModuleMap R S p hR) g N hregular hN
  exact ⟨hinj, N, hcoker⟩

end SerrePositivity.CLMST
