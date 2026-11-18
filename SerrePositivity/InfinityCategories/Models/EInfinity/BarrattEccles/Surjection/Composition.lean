module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSigns

/-!
模型。文献の定義との比較は後で
# 全射語の符号付き線形部分合成

概要：Berger–Fresse §1.2.4–5 の全ての重なる分割を足して部分合成を定義する。
方針：各基底語の対を符号付き正規化語の有限和へ写し、両変数で線形延長する。
規約：nullary も含む。微分・TR との両立とオペラッド公理は別に証明する。
使われ方：一般の TR の合成保存と χ のオペラッド構造の証明の対象となる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

variable (A : Type u) [CommRing A]

/-- 概要：基底語の対の符号付き部分合成（BF §1.2.4–5）。
方針：指定値の出現数に一致する全ての重なる分割の合成語を足す。
規約：無効な語は正規化で零へ送る。
使われ方：線形部分合成の基底上の値。 -/
def compositionOnWords {m n d e : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e)
    (k : Fin (m + 1)) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A (m + n) (d + e) :=
  ∑ r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e),
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionSign u v k r • _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeGenerator A u v k r

/-- 概要：χ の次数ごとの両線形部分合成（BF §1.2.4–5）。
方針：基底の像の有限和を自由加群の線形結合で両変数へ延長する。
規約：外側 arity m+1・次数 d、内側 arity n・次数 e。
使われ方：複体上の部分合成と TR の合成保存を構成するための次数写像。 -/
def partialComposition (m n d e : ℕ) (k : Fin (m + 1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A (m + 1) d →ₗ[A]
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A n e →ₗ[A] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A (m + n) (d + e) :=
  Finsupp.linearCombination A (fun u : ULift.{u} (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) =>
    Finsupp.linearCombination A (fun v : ULift.{u} (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) =>
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionOnWords A u.down v.down k))

/-- 概要：両線形部分合成は基底上で指定した有限和を与える（BF §1.2.4–5）。
方針：二つの台が一点の有限台関数の線形結合を評価する。
規約：整数符号は係数環上の加法群への作用。
使われ方：TR の合成保存を生成元ごとの有限和の対応へ帰着する。 -/
@[simp] lemma partialComposition_basis {m n d e : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) (k : Fin (m + 1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.partialComposition A m n d e k (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A (m + 1) d (ULift.up u))
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A n e (ULift.up v)) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionOnWords A u v k := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.partialComposition, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis_apply]
  erw [Finsupp.linearCombination_single]
  simp only [one_smul]
  erw [Finsupp.linearCombination_single]
  exact one_smul A _

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
