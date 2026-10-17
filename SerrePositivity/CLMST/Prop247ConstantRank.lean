module

public import SerrePositivity.CLMST.Prop247AndreBase
public import SerrePositivity.CLMST.Prop247ConstantRankDescent

/-! # Prop 2.4.7：定 rank の原典の署名への条件付き接続

André 拡大の存在と元の標準比較・共通指数・実降下を全て構成する。
残る比較入力は perfectoid・絶対整閉基底上の KL の指定 excision 四角形である。
Cor 8.12 は引用せず、選択した perfectoid 化に既存 B-I のみを保持する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- 定 rank の原典の仮定から、指定した元の f の実錐・核・余核へ条件付きで接続する。
André 拡大の存在や底変換後の rank・bounded torsion を追加仮定にしない。 -/
theorem prop247_constantRank_isogeny_of_excision
    (R S C : Type u) [CommRing R] [CommRing S] [CommRing C]
    [Algebra R S] [Algebra R C] [Module.Finite R S] [Algebra.FinitePresentation R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (hExcision : ∀ (B : Type u) [CommRing B], IsIntegralPerfectoid B p →
      IsAbsolutelyIntegrallyClosed B → KLFiniteComparisonExcision B p)
    (f : S →ₐ[R] C) (hf : IsPerfectoidization p f.toRingHom)
    (hbounded : ∃ N : ℕ, ∀ n : ℕ, ∀ s : S,
      (p : S) ^ n * s = 0 → (p : S) ^ N * s = 0)
    (g : R) (hetale : letI := GenericEtale.awayAlgebra R S g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R S g)))
    (r : ℕ) (hRank : ∀ x : PrimeSpectrum.basicOpen g, prop247_awayRank R S g x = r) :
    ∃ q : ℕ, moduleMapConeScalar R f.toLinearMap (g ^ q) = 0 ∧
      (∀ x : f.toLinearMap.ker, g ^ q • x = 0) ∧
      (∀ y : C ⧸ f.toLinearMap.range, g ^ q • y = 0) := by
  obtain ⟨B, hB, hRB, hperf, hAIC, hflat⟩ := prop247_exists_andre_descent_base R p hR
  letI := hB
  letI := hRB
  exact prop247_constantRank_isogeny_of_andre_excision R S B C p hR hperf hAIC
    (hExcision B hperf hAIC) hflat f hf hbounded g hetale r hRank

/-- 同じ定 rank の条件付き結論を、原典の選択済み perfectoid 化の元の実写像へ適用する。 -/
theorem prop247_constantRank_actual_isogeny_of_excision
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Algebra.FinitePresentation R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (hExcision : ∀ (B : Type u) [CommRing B], IsIntegralPerfectoid B p →
      IsAbsolutelyIntegrallyClosed B → KLFiniteComparisonExcision B p)
    (hbounded : ∃ N : ℕ, ∀ n : ℕ, ∀ s : S,
      (p : S) ^ n * s = 0 → (p : S) ^ N * s = 0)
    (g : R) (hetale : letI := GenericEtale.awayAlgebra R S g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R S g)))
    (r : ℕ) (hRank : ∀ x : PrimeSpectrum.basicOpen g, prop247_awayRank R S g x = r) :
    ∃ q : ℕ, moduleMapConeScalar R (perfectoidizationModuleMap R S p hR) (g ^ q) = 0 ∧
      (∀ x : (perfectoidizationModuleMap R S p hR).ker, g ^ q • x = 0) ∧
      (∀ y : Perfectoidization R S p hR ⧸ (perfectoidizationModuleMap R S p hR).range,
        g ^ q • y = 0) := by
  let f := IsScalarTower.toAlgHom R S (Perfectoidization R S p hR)
  have hf : IsPerfectoidization p f.toRingHom := isPerfectoidization_toPerfectoidization R S p hR
  exact prop247_constantRank_isogeny_of_excision R S (Perfectoidization R S p hR) p hR
    hExcision f hf hbounded g hetale r hRank

end SerrePositivity.CLMST
