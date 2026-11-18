module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.CutLineRanks
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.TwoPiecePartitions

/-!
模型。文献の定義との比較は後で
# 非零内側切断による分割部分語の行次数

概要：Berger–Fresse §1.2.5・§2.2.6 の一・二部分割の成分次数を計算する。
方針：非零切断点までに全区切りを通過することから前半次数は全次数、後半は零とする。
規約：成分次数は元の lineRank の端点差をそのまま使う。
使われ方：二段切断で選ぶ合成分割の Koszul 符号。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：唯一部分語の行次数は内側語の全次数（BF §1.2.5）。
方針：始点零と語の最終位置の行番号を評価する。
規約：内側空語も含む。
使われ方：一出現挿入の符号の成分次数。 -/
lemma segmentDegree_single {n e : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.segmentDegree v.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.single (n + e)) 0 = e := by
  change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank v.val (0 + (n + e) - 1) - _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank v.val 0 = e
  rw [Nat.zero_add, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank_last, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank_zero, Nat.sub_zero]

/-- 概要：非零内側切断の二部分割の前半行次数は全内側次数（BF §2.2.6）。
方針：前半の終点は切断点で、その時点で全区切りを通過済み。
規約：共有文字を前半に含める。
使われ方：最初の指定出現だけが内側次数を移動させること。 -/
lemma segmentDegree_two_zero {n e : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) (q : Fin (n + e))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate v.val q) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.segmentDegree v.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.two q) 0 = e := by
  change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank v.val (0 + (q.val + 1) - 1) - _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank v.val 0 = e
  have he : 0 + (q.val + 1) - 1 = q.val := by omega
  rw [he, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank_zero, Nat.sub_zero]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.lineRank_after_pivot_eq_degree v q h q.val le_rfl

/-- 概要：非零内側切断の二部分割の後半行次数は零（BF §2.2.6）。
方針：切断点以後に区切りがないので両端の行番号が一致する。
規約：共有文字を後半の先頭に含める。
使われ方：二番目の指定出現の合成指数の寄与を消去する。 -/
lemma segmentDegree_two_one {n e : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) (q : Fin (n + e))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate v.val q) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.segmentDegree v.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.two q) 1 = 0 := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.segmentDegree
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.two_start_one]
  change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank v.val (q.val + ((n + e) - q.val) - 1) - _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank v.val q.val = 0
  have he : q.val + ((n + e) - q.val) = n + e := by have := q.isLt; omega
  rw [he, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank_last, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.lineRank_after_pivot_eq_degree v q h q.val le_rfl, Nat.sub_self]

/-- 概要：分割数の移送は同じ部分語の行次数を保つ（BF §1.2.5）。
方針：分割数の等式を消去して有限添字を一致させる。
規約：語の全射性や切断の非零性は不要。
使われ方：二段切断の分割を標準二部分割へ移す。 -/
lemma segmentDegree_cast_count {t s l n : ℕ} (h : t = s) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition t l)
    (v : Fin l → Fin n) (i : Fin t) (j : Fin s) (hij : i.val = j.val) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.segmentDegree v (cast (congrArg (fun a => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition a l) h) r) j =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.segmentDegree v r i := by
  cases h
  have he : j = i := Fin.ext hij.symm
  subst j
  rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
