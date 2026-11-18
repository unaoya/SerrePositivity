module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSourceSum
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.NormalizedMap
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleLeibnizChains

/-!
模型。文献の定義との比較は後で
# 正の内側 arity の正規化 TR の部分合成保存

概要：Berger–Fresse §1.5.6–9 の全符号付き和の一致を実際の正規化鎖上の双線形合成へ移す。
方針：正規化生成元の shuffle 公式に一般の onSequence 合成保存を適用し、双線形外延性で延長する。
規約：任意の可換環・全次数・全外側 arity、内側 arity は正。
使われ方：全 arity の TR オペラッド射性と χ の微分・単位・結合則の転送。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection _root_.SerrePositivity.EInfinity.BarrattEccles
open scoped _root_.Simplicial

variable (A : Type u) [CommRing A]

/-- 概要：正規化生成元の全 shuffle 合成で TR は部分合成を保つ（BF §1.5.6–9）。
方針：shuffle の全生成元公式を TR の生成元値へ移し、全 onSequence 和の一般公式を使う。
規約：退化単体も含む任意の二つの単体に適用する。
使われ方：正規化鎖上の全双線形合成保存の生成元での検証。 -/
lemma normalizedMap_shuffle_generators_of_pos {m n d e : ℕ} (hn : 0 < n)
    (k : Fin (m + 1)) (x : (simplicial (m + 1)) _⦋d⦌) (y : (simplicial n) _⦋e⦌) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap A (m + n) (d + e)
      (shuffleBilinear A m n k d e (normalizedGenerator A (m + 1) d x)
        (normalizedGenerator A n e y)) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.partialComposition A m n d e k
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap A (m + 1) d (normalizedGenerator A (m + 1) d x))
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap A n e (normalizedGenerator A n e y)) := by
  simp only [shuffleBilinear_generators, shuffleValue, map_sum, map_zsmul,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap_generator]
  rw [← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence_partialComposition_of_pos A hn (simplexEquiv (m + 1) d x)
    (simplexEquiv n e y) k]
  apply Finset.sum_congr rfl
  intro s _
  congr 1

/-- 概要：正の内側 arity で実際の正規化 TR は全ての双線形 shuffle 合成を保つ（BF §1.5.6–9）。
方針：合成の両側を双線形写像として正規化生成元上で一致させる。
規約：任意の可換環・全自然数次数。始域の非退化性や元の成功を仮定しない。
使われ方：TR の一般のオペラッド射性の正の内側 arity の主定理。 -/
lemma normalizedMap_shuffleBilinear_of_pos {m n d e : ℕ} (hn : 0 < n)
    (k : Fin (m + 1)) (x : (_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedChains A (m + 1)).X d)
    (y : (_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedChains A n).X e) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap A (m + n) (d + e) (shuffleBilinear A m n k d e x y) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.partialComposition A m n d e k
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap A (m + 1) d x) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap A n e y) := by
  let L := (shuffleBilinear A m n k d e).compr₂ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap A (m + n) (d + e))
  let R := ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.partialComposition A m n d e k).compl₂
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap A n e)).comp (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap A (m + 1) d)
  have he : L = R := by
    apply normalizedGenerator_bilinear_ext A (m + 1) n d e
    intro sx sy
    change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap A (m + n) (d + e)
      (shuffleBilinear A m n k d e (normalizedGenerator A (m + 1) d sx)
        (normalizedGenerator A n e sy)) = _
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap_shuffle_generators_of_pos A hn k sx sy
  exact congrArg (fun f => f x y) he

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
