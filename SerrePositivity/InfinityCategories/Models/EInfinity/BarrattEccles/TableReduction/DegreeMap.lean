module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.DegreeZero
public import SerrePositivity.EInfinity.BarrattEccles.Basis

/-!
模型。文献の定義との比較は後で
# 正規化 Barratt–Eccles 基底上の table reduction

概要：Berger–Fresse §1.3.1 の有限和を実際の E(n) の各次数から線形に延長する。
方針：既存の正規化複体の基底で置換列を読み、その TR を像として指定する。
規約：鎖次数 d はコチェイン次数 −d。微分保存はここでは主張しない。
使われ方：一般の TR の鎖写像性と全射性の対象となる次数ごとの写像。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

variable (A : Type u) [CommRing A]

/-- 概要：実際の E(n) から χ(n) への次数ごとの線形写像（BF §1.3.1）。
方針：正規化複体の自由基底の各置換列に onSequence を適用する。
規約：次数 −d の成分で定義し、まだ chain map には束ねない。
使われ方：TR の全射性・微分保存・部分合成保存を証明する。 -/
def degreeMap (n d : ℕ) :
    (_root_.SerrePositivity.EInfinity.BarrattEccles.complex A n).X (-(d : ℤ)) →ₗ[A] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A n d :=
  (_root_.SerrePositivity.EInfinity.BarrattEccles.complexBasis A n d).constr A
    (fun x => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence A (_root_.SerrePositivity.EInfinity.BarrattEccles.simplexEquiv n d x.down.val))

/-- 概要：次数ごとの線形写像は基底上で table reduction の和（BF §1.3.1）。
方針：自由基底からの線形延長の評価公式を使う。
規約：非退化な置換列を基底の添字とする。
使われ方：鎖写像性と全射性を組合せ的な等式へ帰着する。 -/
@[simp] lemma degreeMap_basis (n d : ℕ)
    (x : ULift.{u} ((_root_.SerrePositivity.EInfinity.BarrattEccles.simplicial n).nonDegenerate d)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.degreeMap A n d (_root_.SerrePositivity.EInfinity.BarrattEccles.complexBasis A n d x) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence A (_root_.SerrePositivity.EInfinity.BarrattEccles.simplexEquiv n d x.down.val) :=
  (_root_.SerrePositivity.EInfinity.BarrattEccles.complexBasis A n d).constr_basis A _ x

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
