module

public import SerrePositivity.BhattScholze.PerfectoidizationInterface.IntegralExistence
public import Mathlib.RingTheory.Finiteness.Basic

/-! # 有限代数の perfectoid 化の存在の互換入口

Bhatt–Scholze Theorem 1.17(1) の整代数の存在入力を共通層で引用し、
有限代数の整性を確認して適用する。有限表示性は既存の署名との互換性のため保持する。
存在する環の選択と普遍性は従来と同じ述語・署名を使い、直接の sorry を置かない。
古典完備化との普遍性の移送も共通層で証明した。
原典の prismatic perfection とその離散性の構成自体は未実装である。
-/

public section

universe u

namespace SerrePositivity.Inputs

/-- Perfectoid 環上の有限かつ有限表示な代数は、環としての perfectoid 化を持つ。
Bhatt–Scholze の整代数の存在入力への適用。 -/
theorem exists_perfectoidization_of_finite
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Algebra.FinitePresentation R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) :
    ∃ (C : Type u) (_ : CommRing C) (f : S →+* C), IsPerfectoidization p f := by
  exact BhattScholze.exists_perfectoidization_of_finite R S p hR

end SerrePositivity.Inputs
