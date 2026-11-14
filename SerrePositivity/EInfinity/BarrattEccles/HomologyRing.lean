module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.EInfinity.BarrattEccles.HomologyAssociativity
public import SerrePositivity.EInfinity.BarrattEccles.HomologyUnit

/-!
# E 代数の実際の H⁰ の可換環構造

概要：BF §1・BM §1 の E 代数の H⁰ を、元のホモロジー加群上の可換環にする。
方針：証明済みの積・単位・結合・可換性と双線形性を束ねる。
規約：加法群構造を保持し、環構造は局所的に選ぶ。
使われ方：E2a-4 の H⁰、E2b の離散可換代数とコホモロジー。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

variable {A : Type u} [CommRing A]

/-- 概要：E 代数の実際の H⁰ は可換環（BF §1、BM §1）。
方針：既存の加法群を保ち、選んだ積と単位へ全ての環公理を付ける。
規約：任意の可換基礎環、環構造を大域 instance にしない。
使われ方：H⁰ の可換環と E2b の離散対象の比較。 -/
@[instance_reducible]
def homologyCommRing (X : (operad A).Algebra) : CommRing (X.carrier.homology 0) := by
  letI : Mul (X.carrier.homology 0) := ⟨fun x y => homologyProduct X x y⟩
  letI : One (X.carrier.homology 0) := ⟨homologyOne X⟩
  letI : CommMonoid (X.carrier.homology 0) := {
    mul_assoc := homologyProduct_assoc X
    one_mul := homologyProduct_one_left X
    mul_one := homologyProduct_one_right X
    mul_comm := homologyProduct_comm X }
  exact {
    (inferInstance : AddCommGroup (X.carrier.homology 0)),
    (inferInstance : CommMonoid (X.carrier.homology 0)) with
    left_distrib := fun x y z => map_add (homologyProduct X x) y z
    right_distrib := fun x y z => by
      change (homologyProduct X (x + y)) z = _
      rw [map_add]
      rfl
    zero_mul := fun x => by
      change (homologyProduct X 0) x = 0
      rw [map_zero]
      rfl
    mul_zero := fun x => map_zero (homologyProduct X x)
    natCast n := n • homologyOne X
    natCast_zero := zero_nsmul _
    natCast_succ n := succ_nsmul _ _
    intCast z := z • homologyOne X
    intCast_ofNat n := by
      change (n : ℤ) • homologyOne X = n • homologyOne X
      simp
    intCast_negSucc n := by
      change Int.negSucc n • homologyOne X = -((n + 1) • homologyOne X)
      simp }

/-- 概要：構成した H⁰ の環の積は元の双線形積（BF §1）。
方針：環構造の定義を評価する。
規約：環構造を局所的に選ぶ。
使われ方：環の記法と構成済みの作用の接続。 -/
lemma homologyCommRing_mul (X : (operad A).Algebra) (x y : X.carrier.homology 0) :
    let := homologyCommRing X
    x * y = homologyProduct X x y := rfl

/-- 概要：構成した H⁰ の環の一は実際の nullary 演算の類（BF §1）。
方針：環構造の単位を評価する。
規約：元の H⁰ の型を使う。
使われ方：離散可換代数との単位比較。 -/
lemma homologyCommRing_one (X : (operad A).Algebra) :
    let := homologyCommRing X
    (1 : X.carrier.homology 0) = homologyOne X := rfl

end SerrePositivity.EInfinity.BarrattEccles

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "7.1.1.6" (partial := component) "仮定：可換環 R 上の実 Barratt–Eccles 代数（Lean が強い：この dg 模型の零次の場合）。結論：既存の加法群を台とする H⁰ に可換環構造を構成する（π₀ の可換性の部分に一致）。全次数の符号付き可換積と一般の Eₖ 環スペクトルの π との比較は含まれない。"] _root_.SerrePositivity.EInfinity.BarrattEccles.homologyCommRing
attribute [cite HA "7.5.1.2" (partial := component) "仮定：通常可換環 R 上の実 BE dg 代数（Lean が強い：この E∞ の模型の次数 0 の場合）。結論：H₀ の積が可換となる（原典の π₀ の元の左右作用の一致のうち次数 0 の結論に一致）。全 πₙ の左右作用および全 k≥2 の模型比較は含まれない。"] _root_.SerrePositivity.EInfinity.BarrattEccles.homologyCommRing
