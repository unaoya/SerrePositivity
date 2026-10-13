module

public import SerrePositivity.CommutativeAlgebra.IntegralPerfectoid
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-! # 整代数の普遍 perfectoid 化（原典の文献入力）

Bhatt–Scholze, Prisms and prismatic cohomology, Theorem 1.17(1) は、
perfectoid 環 R 上の任意の整代数 S に、普遍 perfectoid 環が存在すると述べる。
Theorem 10.11 と Proposition 8.5 はその存在と普遍性の背景である。
ここでは冒頭の環としての普遍性の主張を引用し、
離散な prismatic perfection や導来完備化を定義したとは扱わない。
有限性・有限表示性・有界 p 冪ねじれは、この主張の仮定ではない。

出典：https://people.mpim-bonn.mpg.de/scholze/prisms.pdf （Theorem 1.17(1)）。
-/

public section
universe u
namespace SerrePositivity.BhattScholze.Inputs

/-- BS Theorem 1.17(1)：perfectoid 環上の整代数は普遍 perfectoid 環を持つ。
完成形の主張は環と一意因子分解であり、派生的な有限代数版への制限は含めない。 -/
theorem exists_perfectoidization_of_integral
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Algebra.IsIntegral R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) :
    ∃ (C : Type u) (_ : CommRing C) (f : S →+* C), IsPerfectoidization p f := by
  sorry

end SerrePositivity.BhattScholze.Inputs
