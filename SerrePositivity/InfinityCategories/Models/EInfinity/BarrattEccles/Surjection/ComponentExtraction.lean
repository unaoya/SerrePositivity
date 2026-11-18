module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReductionInterval
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.ComponentRowRanges
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapCoverage

/-!
模型。文献の定義との比較は後で
# 重なる分割の各成分の実際の抽出

概要：Berger–Fresse §1.5.7 の内側分割成分を元の連続する置換行から抽出する。
方針：有限な始終点で元の成功抽出の区間証明書を構成する。
規約：正の語長の成分を扱い、隣接成分の共有端点を両方に含める。
使われ方：compositionPath の各垂直成分に実際の元の行と選択語を与える。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：内側分割の一成分の元の抽出証明書（BF §1.5.7）。
方針：同じ元の成功から成分の両端の区間を切り出す。
規約：語長が正なら一文字成分も含めて構成する。
使われ方：合成表の垂直成分を実際に進める入力。 -/
noncomputable def componentExtraction {n d t : ℕ}
    (w : Fin (d + 1) → Equiv.Perm (Fin n)) (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d)
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w s) [] = some (List.ofFn v.val))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition t (n + d)) (hl : 0 < n + d) (i : Fin t) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReductionInterval w s v.val h (r.startPosition hl i) (r.endPosition hl i) :=
  Classical.choice (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionInterval_nonempty w s v.val h _ _
    (r.startPosition_le_endPosition hl i))

/-- 概要：成分証明書の選択語は実際の重なる分割の部分語（BF §1.5.7）。
方針：閉区間の長さを指定された部分長へ戻す。
規約：共有端点は両成分の選択語に残る。
使われ方：合成語の既存 segment と元の抽出を同定する。 -/
lemma componentExtraction_word {n d t : ℕ}
    (w : Fin (d + 1) → Equiv.Perm (Fin n)) (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d)
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w s) [] = some (List.ofFn v.val))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition t (n + d)) (hl : 0 < n + d) (i : Fin t) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.componentExtraction w s v h r hl i).selected.flatten = r.segment v.val i := by
  have hw := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.componentExtraction w s v h r hl i).word
  change (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.componentExtraction w s v h r hl i).selected.flatten =
    ((List.ofFn v.val).drop (r.start i)).take
      (r.start i + (r.val i).val - 1 - r.start i + 1) at hw
  have he : r.start i + (r.val i).val - 1 - r.start i + 1 = (r.val i).val := by
    have := r.positive hl i; omega
  rw [he] at hw
  exact hw

/-- 概要：成分を抽出する元の行数は成分次数＋1（BF §1.5.7）。
方針：区間の元の行数を既存の成分次数の定義へ照合する。
規約：次数零の成分は一行。
使われ方：候補経路の垂直辺数と実際の元の行の進行を一致させる。 -/
lemma componentExtraction_length {n d t : ℕ}
    (w : Fin (d + 1) → Equiv.Perm (Fin n)) (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d)
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w s) [] = some (List.ofFn v.val))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition t (n + d)) (hl : 0 < n + d) (i : Fin t) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.componentExtraction w s v h r hl i).part.length = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.segmentDegree v.val r i + 1 :=
  (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.componentExtraction w s v h r hl i).length

/-- 概要：成分証明書は元の reduceRows で実際の部分語を返す（BF §1.5.7）。
方針：区間の実際の成功を選択語の同定へ移す。
規約：初期状態は元の成分開始位置の進行状態。
使われ方：合成表の構成で追加の成分成功仮定を要求しない。 -/
lemma componentExtraction_success {n d t : ℕ}
    (w : Fin (d + 1) → Equiv.Perm (Fin n)) (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d)
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w s) [] = some (List.ofFn v.val))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition t (n + d)) (hl : 0 < n + d) (i : Fin t) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.componentExtraction w s v h r hl i).part
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRemoved w s v.val h (r.startPosition hl i)) = some (r.segment v.val i) := by
  have hs := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.componentExtraction w s v h r hl i).trace.append [] [] rfl
  simpa only [List.append_nil, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.componentExtraction_word] using hs

/-- 概要：隣接成分の終了位置と開始位置は同じ有限位置（BF §1.5.7）。
方針：重なる分割の開始位置の更新式と正の部分長を使う。
規約：部分語の両端を共有する。
使われ方：元の抽出の成分終状態と次の成分始状態を一致させる。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.endPosition_eq_startPosition {t l : ℕ} (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition t l)
    (hl : 0 < l) (i j : Fin t) (hij : j.val = i.val + 1) :
    r.endPosition hl i = r.startPosition hl j := by
  apply Fin.ext
  change r.start i + (r.val i).val - 1 = r.start j
  rw [r.start_next i j hij]
  have := r.positive hl i
  omega

/-- 概要：隣接する重なる成分の元の抽出証跡を厳密な共有状態で連結（BF §1.5.7）。
方針：同じ有限共有端点の進行状態を一致させ、元の先行証跡を連結する。
規約：共有文字は両成分に現れるが、共有状態ではまだ除外しない。
使われ方：複数の内側成分の間で元の抽出状態を引き継ぐ。 -/
lemma componentExtraction_adjacent_prefix {n d t : ℕ}
    (w : Fin (d + 1) → Equiv.Perm (Fin n)) (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d)
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w s) [] = some (List.ofFn v.val))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition t (n + d)) (hl : 0 < n + d) (i j : Fin t)
    (hij : j.val = i.val + 1) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.componentExtraction w s v h r hl i).part ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.componentExtraction w s v h r hl j).part)
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRemoved w s v.val h (r.startPosition hl i))
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.componentExtraction w s v h r hl i).selected ++
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.componentExtraction w s v h r hl j).selected)
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRemoved w s v.val h (r.endPosition hl j)) := by
  have he := congrArg (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRemoved w s v.val h) (r.endPosition_eq_startPosition hl i j hij)
  have ht := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.componentExtraction w s v h r hl j).trace
  rw [← he] at ht
  exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.componentExtraction w s v h r hl i).trace.trans ht

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
