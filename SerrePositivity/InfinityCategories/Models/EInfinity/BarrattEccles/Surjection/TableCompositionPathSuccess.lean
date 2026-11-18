module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionGridWalk
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionPathSign

/-!
模型。文献の定義との比較は後で
# 実際の compositionPath の合成表と合成語抽出

概要：Berger–Fresse §1.5.7 の正方向で元の二表と分割から実際の経路上の成功表を構成する。
方針：一般の座標列一致で残っていた入力を閉じ、構成済みの実際の Schedule を使う。
規約：正の内側語長。逆構成と全項の和の対応は後続。
使われ方：TR の一般の合成保存で正方向の各合成項を供給する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction _root_.SerrePositivity.EInfinity.BarrattEccles

/-- 概要：実際の経路置換列と構成した Schedule は元の全融合表そのもの（BF §1.5.7）。
方針：実際の経路全座標を元の融合格子列と一般に一致させる。
規約：座標列や合成表の一致を入力に要求しない。
使われ方：実際の経路表に既存の全融合抽出成功を適用する。 -/
lemma rows_pathSequence {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows c.pathSequence c.fusedSchedule = c.fusedRows 0 :=
  c.rows_pathSequence_of_vertices c.compositionPath_vertices_eq_grid

/-- 概要：元の二つの成功と分割から実際の経路表の合成語抽出成功（BF §1.5.7）。
方針：一般の座標列一致で構成済みの経路表を全融合表へ戻す。
規約：元の成功以外の成功・経路一致・行長条件は仮定しない。
使われ方：一般の TR 合成保存の正方向の実際の一項。 -/
lemma pathSequence_success {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows c.pathSequence c.fusedSchedule) [] =
      some (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord c.outerWord c.innerWord c.slot c.cuts) := by
  rw [c.rows_pathSequence]
  exact c.fused_success_compositeWord

/-- 概要：構成した経路置換列は既存の実際の shuffle 合成単体の頂点列（BF §1.5.7）。
方針：既存の shuffleSimplex の各頂点公式で比較する。
規約：元の二つの単体は元の置換列から構成する。
使われ方：抽出成功を既存の Barratt–Eccles 合成の正規化項へ接続する。 -/
lemma pathSequence_eq_shuffleSimplex {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e) :
    c.pathSequence = simplexEquiv (m + n) (d + e)
      (shuffleSimplex m n c.slot (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionPath c.outerWord c.innerWord c.slot c.cuts)
        ((simplexEquiv (m + 1) d).symm c.outer) ((simplexEquiv n e).symm c.inner)) := by
  funext k
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData.pathSequence, simplexEquiv_shuffleSimplex, Equiv.apply_symm_apply]

/-- 概要：実際の経路表の正規化 TR 項は元の分割の合成項（BF §1.5.7）。
方針：一般の実際の抽出成功を既存の term に代入する。
規約：符号は既存の compositionPath_sign で別途合わせる。
使われ方：全分割と全実際の経路表の和の対応を構成する。 -/
lemma term_pathSequence (A : Type*) [CommRing A] {m n d e : ℕ}
    (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.term A c.pathSequence c.fusedSchedule =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeGenerator A c.outerWord c.innerWord c.slot c.cuts := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.term, c.pathSequence_success]
  rfl

/-- 概要：既存の実際の shuffle 単体上で選んだ TR 項は元の合成項（BF §1.5.7）。
方針：元の経路置換列を shuffleSimplex の頂点列へ置き換える。
規約：任意の可換環上。経路・Schedule は元の二表から実際に構成したもの。
使われ方：一般の合成保存の正方向を既存 BE の shuffle 公式に適用する。 -/
lemma term_shuffleSimplex (A : Type*) [CommRing A] {m n d e : ℕ}
    (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.term A (simplexEquiv (m + n) (d + e)
      (shuffleSimplex m n c.slot (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionPath c.outerWord c.innerWord c.slot c.cuts)
        ((simplexEquiv (m + 1) d).symm c.outer) ((simplexEquiv n e).symm c.inner)))
      c.fusedSchedule = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeGenerator A c.outerWord c.innerWord c.slot c.cuts := by
  rw [← c.pathSequence_eq_shuffleSimplex]
  exact c.term_pathSequence A

/-- 概要：既存の shuffle 符号付き実際の TR 項は元の符号付き合成項（BF §1.5.6–7）。
方針：実際の項の一致と既存の全経路符号の一致を合わせる。
規約：任意の可換環上。全項の和の全単射はまだ要求しない。
使われ方：一般の TR 合成保存で正方向の各項と符号を同時に合わせる。 -/
lemma signed_term_shuffleSimplex (A : Type*) [CommRing A] {m n d e : ℕ}
    (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e) :
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionPath c.outerWord c.innerWord c.slot c.cuts).sign : ℤ) •
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.term A (simplexEquiv (m + n) (d + e)
        (shuffleSimplex m n c.slot (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionPath c.outerWord c.innerWord c.slot c.cuts)
          ((simplexEquiv (m + 1) d).symm c.outer) ((simplexEquiv n e).symm c.inner)))
        c.fusedSchedule = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionSign c.outerWord c.innerWord c.slot c.cuts •
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeGenerator A c.outerWord c.innerWord c.slot c.cuts := by
  rw [c.term_shuffleSimplex A, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionPath_sign]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData
