module


public meta import SerrePositivity.Util.Citation
public import Mathlib.Algebra.DirectSum.Algebra

/-!
# 次数付き可換微分環

## 概要
自然数で次数付けた k 代数に、符号付き可換性と微分を持たせる。

## 方針
斉次積と次数 0 の環およびその加群作用は Mathlib の次数付き環から得る。

## 規約
奇数次の斉次元の平方零は別の条件として扱う。

## 使われ方
多項式 de Rham 複体からの写像の標的。
-/

@[expose] public section

universe u

open scoped DirectSum

namespace SerrePositivity.DeRham

/-- 概要：自然数で次数付けた次数付き可換微分 k 代数。
方針：斉次積の公理を次数付き環の型クラスから取り、微分の公理を加える。
規約：可換性と Leibniz 則の次数を添字の等式で合わせる。
使われ方：de Rham 複体の普遍性。 -/
structure GradedCommDGAlgebra (k : Type u) [CommRing k] where
  carrier : ℕ → Type u
  [addCommGroup : ∀ i, AddCommGroup (carrier i)]
  [module : ∀ i, Module k (carrier i)]
  [gradedRing : DirectSum.GRing carrier]
  [gradedAlgebra : DirectSum.GAlgebra k carrier]
  d : ∀ i, carrier i →ₗ[k] carrier (i + 1)
  d_sq (i : ℕ) (x : carrier i) : d (i + 1) (d i x) = 0
  mul_comm {i j : ℕ} (x : carrier i) (y : carrier j) :
    cast (congrArg carrier (Nat.add_comm i j)) (GradedMonoid.GMul.mul x y) =
      (-1 : ℤ) ^ (i * j) • GradedMonoid.GMul.mul y x
  leibniz {i j : ℕ} (x : carrier i) (y : carrier j) :
    d (i + j) (GradedMonoid.GMul.mul x y) =
      cast (congrArg carrier (by omega : (i + 1) + j = (i + j) + 1))
        (GradedMonoid.GMul.mul (d i x) y) +
      (-1 : ℤ) ^ i • GradedMonoid.GMul.mul x (d j y)

attribute [instance] GradedCommDGAlgebra.addCommGroup GradedCommDGAlgebra.module
  GradedCommDGAlgebra.gradedRing GradedCommDGAlgebra.gradedAlgebra

/-- 概要：標的の斉次元の積。
方針：次数付き環の積を用いる。
規約：積の次数は二つの次数の和。
使われ方：de Rham 複体からの写像の乗法性。 -/
def GradedCommDGAlgebra.mul {k : Type u} [CommRing k] (H : GradedCommDGAlgebra k)
    {i j : ℕ} (x : H.carrier i) (y : H.carrier j) : H.carrier (i + j) :=
  GradedMonoid.GMul.mul x y

end SerrePositivity.DeRham

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "7.1.4.8" (partial := special) "仮定：任意可換環 R と非負余鎖次数（Lean が強い：非負次数に限る）。結論：xy=(-1)^(ij)yx と微分の Leibniz 則を満たす可換 dg 代数を構造として定義する（この次数範囲の定義に一致）。全整数次数の dg 代数圏の充満部分圏としての束ね方は含まれない。"] _root_.SerrePositivity.DeRham.GradedCommDGAlgebra
