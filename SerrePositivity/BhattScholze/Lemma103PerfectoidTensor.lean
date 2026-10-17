module

public import SerrePositivity.BhattScholze.PerfectoidCompletedTensorDiscrete

/-!
# Lemma 10.3 の一般の perfectoid テンソル

## 概要
BS 著者版 Lemma 10.3 の証明中の主張（印刷 pp.78–79）を、実際の完備導来テンソルの
全非零次数のホモロジー消滅と、その実 H⁰ 環の perfectoid 性として公開する。

## 方針
既存の Fontaine 環・完全 prism・二段階完備化による証明を再利用する。
完全標数 p 環の Tor 独立性は証明済みであり、追加仮定にはしない。

## 規約
G2 の元の完備導来テンソルと `derivedH0CommRing` を使う。零環と p ねじれを許す。

## 使われ方
Lemma 10.3 の商環の自己テンソルと、B5 の依存監査の入口である。
-/

@[expose] public noncomputable section
universe u

namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard

/--
## 概要
perfectoid 環 R 上の perfectoid 代数 S,T の完備導来テンソルは全非零次数で
ホモロジーが零であり、同じ対象の実 H⁰ 環は perfectoid である
（BS 著者版 Lemma 10.3、印刷 pp.78–79）。

## 方針
既存の完全 prism による次数零集中と perfectoid 性を使い、標準 t 構造の
判定から非零次数の消滅を取り出す。

## 規約
有限性・平坦性・p 正則性・非零性を仮定しない。H⁰ の環構造を明示する。

## 使われ方
S=T=R/K に特殊化して Lemma 10.3 の商環の自己積に用いる。
-/
theorem lemma103_perfectoidTensor
    (p : ℕ) [Fact p.Prime] (R S T : Type u)
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (hR : IsIntegralPerfectoid R p) (hS : IsIntegralPerfectoid S p)
    (hT : IsIntegralPerfectoid T p) :
    let X := boundedAboveCompletedTensorAlgebra R (p : R) S T
    letI := derivedH0CommRing X
    (∀ i : ℤ, i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj X.X.obj)) ∧
      IsIntegralPerfectoid
        ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj X.X.obj) p := by
  obtain ⟨hpure, hperf⟩ := integralPerfectoid_completedTensor_pure_and_h0 p R S T hR hS hT
  refine ⟨?_, hperf⟩
  intro i hi
  rcases lt_or_gt_of_ne hi with hneg | hpos
  · exact (DerivedCategory.isGE_iff _ 0).mp hpure.1 i hneg
  · exact (DerivedCategory.isLE_iff _ 0).mp hpure.2 i hpos

end SerrePositivity.BhattScholze
