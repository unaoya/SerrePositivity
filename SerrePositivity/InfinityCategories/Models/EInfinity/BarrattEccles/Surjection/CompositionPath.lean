module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.ComponentPaths
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.SegmentDegrees
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OuterSegmentDegrees

/-!
模型。文献の定義との比較は後で
# 全射語の合成項から構成する実際の d×e 経路

概要：Berger–Fresse §1.5.4 の候補経路を成分行次数から構成する。
方針：外側最初の水平移動の後に内側・外側の成分移動を交互に連結する。
規約：水平次数は d、垂直次数は e であり、両方の総和の証明を使う。
使われ方：候補経路の table reduction が実際の合成語を返すことを次に照合する。
-/

@[expose] public section

noncomputable section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

open _root_.SerrePositivity.EInfinity.BarrattEccles

/-- 概要：各内側成分とその直後の外側成分の次数の列（BF §1.5.4）。
方針：出現順の有限添字で垂直次数と次の水平次数を対にする。
規約：最初の外側成分はこの列の前に別に置く。
使われ方：合成の候補経路の連結データ。 -/
def compositionDegreePairs {m n d e : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e)
    (k : Fin (m + 1)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e)) :
    List (ℕ × ℕ) :=
  List.ofFn (fun i => (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.segmentDegree v.val r i, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.outerSegmentDegree u.val k (i.val + 1)))

/-- 概要：成分移動の全垂直次数は内側の次数 e（BF §1.5.4）。
方針：分割成分次数の総和を列の第一成分の総和へ移す。
規約：内側の空語も含む。
使われ方：候補経路の垂直辺数の型を合わせる。 -/
lemma compositionDegreePairs_vertical {m n d e : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e)) :
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionDegreePairs u v k r).map Prod.fst).sum = e := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionDegreePairs, List.map_ofFn, Function.comp_apply, List.sum_ofFn]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.sum_segmentDegree v r (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount_pos u k)

/-- 概要：最初を含めた全水平次数は外側の次数 d（BF §1.5.4）。
方針：全外側成分の次数和から最初の成分を分離する。
規約：零次数の成分も保持する。
使われ方：候補経路の水平辺数の型を合わせる。 -/
lemma compositionDegreePairs_horizontal {m n d e : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.outerSegmentDegree u.val k 0 + ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionDegreePairs u v k r).map Prod.snd).sum = d := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionDegreePairs, List.map_ofFn, Function.comp_apply, List.sum_ofFn]
  have hs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.sum_outerSegmentDegree u k
  rw [Fin.sum_univ_succ] at hs
  exact hs

/-- 概要：全射語の一つの合成項が指定する実際の d×e 格子経路（BF §1.5.4）。
方針：最初の外側成分を水平に進み、続いて内側・外側の成分移動を連結する。
規約：成分次数の総和で d と e の辺数へ移送する。
使われ方：shuffle 合成と table reduction の許容表を比較する候補経路。 -/
def compositionPath {m n d e : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e)
    (k : Fin (m + 1)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e)) : ShufflePath d e :=
  shufflePathCastEquiv (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionDegreePairs_horizontal u v k r)
    (by rw [Nat.zero_add, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionDegreePairs_vertical])
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.append (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.horizontal (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.outerSegmentDegree u.val k 0))
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.blocks (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionDegreePairs u v k r)))

/-- 概要：候補経路の実際の shuffle 符号の成分交換による式（BF §1.5.6）。
方針：先頭水平成分は符号 1、残る成分連結の符号を使う。
規約：元の合成指数との有限和の同定は CompositionPathSign で行う。
使われ方：TR の合成保存で必要な二つの符号の一致を証明する。 -/
lemma compositionPath_sign_blocks {m n d e : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e)) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionPath u v k r).sign =
      (-1 : ℤˣ) ^ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.blockExponent (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionDegreePairs u v k r) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionPath, shufflePathCastEquiv_sign, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.append_sign,
    ShufflePath.sign_rightZero, zero_mul, pow_zero, one_mul, one_mul, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.blocks_sign]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
