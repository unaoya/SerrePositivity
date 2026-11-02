module

public import SerrePositivity.Paper.Section4.RankQuotient
public import SerrePositivity.CommutativeAlgebra.GeometricFiber
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.Algebra.CharP.Defs

/-!
# 支持つきランク商の K₀ の降下（未証明入力）

## 主張と未証明の範囲

論文の補題4.6と一般係数版定理3.1の帰結を、一つの名前付き定理として置く。
既に構成した論文の支持圏、係数変更、自己同型による群作用について、
不変な K₀ 類の正の整数倍が A 側から来ることを主張する。
有理化後の全射性から分母とねじれを消去した形で、定理4.7に必要な入力である。

dg 商・connective な係数による表示とその両立条件、および定理3.1による降下は
この `sorry` の範囲に含める。補題4.6そのものを形式化・証明したとは主張しない。
正則局所環、剰余標数、幾何ファイバーの条件と正の基準ランクを明示し、
任意の圏や任意の群作用に対する降下を仮定しない。
長さ関数、C、§2の具体的な構成は用いない。
-/

@[expose] public section

universe u

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.Section4

open IsLocalRing Asymptotic

/-- 補題4.6と定理3.1から得られる、支持つきランク商の有理降下の整数版。

現在は未証明入力として引用する。後で dg 表示と一般係数版の降下を実装した際、
この証明だけを置き換えられる。定理4.7の数値比較はこの結論から別に証明する。 -/
theorem supportedRankK0_descent
    (A T : Type u) [CommRing A] [IsRegularLocalRing A]
    [CommRing T] [IsLocalRing T] [IsDomain T] [Algebra A T] [Module.Finite A T]
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField A) p]
    {e : ℕ} (z : Fin e → A) (_hz : Ideal.span (Set.range z) = maximalIdeal A)
    (s : ℕ → ℕ) (_hs : ∀ n, 0 < s n)
    (G : Type u) [Group G] [Finite G] [MulSemiringAction G T] [SMulCommClass G A T]
    (_hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap A T)))
    (_htrans : IsGeometricallyTransitive A T G)
    (y : TriangulatedK0 (paperSupportedRank (s := s) (algebraMap A T ∘ z)).FullSubcategory)
    (_hy : ∀ g : G, g • y = y) :
    ∃ (n : ℕ) (x : TriangulatedK0 (paperSupportedRank (s := s) z).FullSubcategory),
      0 < n ∧ n • y = TriangulatedK0.map (paperSupportedChangeRing (algebraMap A T) z) x := by
  sorry

end SerrePositivity.Section4
