module

public import SerrePositivity.BhattScholze.Perfectoidization.Cone
public import SerrePositivity.CommutativeAlgebra.GenericEtale
public import SerrePositivity.CLMST.Prop247Proof

/-! # CLMST Proposition 2.4.7 の導来錐の零射（互換入口）

perfectoid 環 R、有限生成 J、有限かつ有限表示な R 代数 S、V(J) の外での
有限エタール性と S の有界 p 冪ねじれを明示する。
結論は実際の D(R) の錐のスカラー射の零性である。
核・余核の零化だけへ弱めたり、S の単射性や p ねじれなしを追加したりしない。

証明は `SerrePositivity.CLMST.proposition_2_4_7_proved` に置く。
元の文献入力と同じ署名を保ち、BS の存在と excision の二入力に相対的に証明する。
-/

public section
universe u
namespace SerrePositivity.CLMST.Inputs
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard

/-- CLMST Prop 2.4.7：標準 perfectoid 化への写像の錐は J-isogeny。
証明済みの `proposition_2_4_7_proved` を呼ぶ互換入口である。
有界 p∞ねじれは、p の冪で消える任意の元を一つの共通冪が消すという条件で記す。
開集合の条件には標準の局所化間の代数構造を使う。 -/
theorem proposition_2_4_7
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Algebra.FinitePresentation R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (J : Ideal R) (hJ : J.FG)
    (hEtale : ∀ g ∈ J, let _ := GenericEtale.awayAlgebra R S g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R S g)))
    (hbounded : ∃ N : ℕ, ∀ (n : ℕ) (s : S),
      (p : S) ^ n * s = 0 → (p : S) ^ N * s = 0) :
    ∀ g ∈ J, ∃ N : ℕ,
      moduleMapConeScalar R (BhattScholze.perfectoidizationModuleMap R S p hR) (g ^ N) = 0 := by
  exact proposition_2_4_7_proved R S p hR J hJ hEtale hbounded

end SerrePositivity.CLMST.Inputs
