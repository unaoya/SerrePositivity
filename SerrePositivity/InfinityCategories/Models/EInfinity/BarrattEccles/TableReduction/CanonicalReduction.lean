module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.CanonicalSchedule
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.WordRows

/-!
模型。文献の定義との比較は後で
# 標準 Schedule による全行の抽出

概要：Berger–Fresse §1.4.3 の指定した行長の項が元の語になることを証明する。
方針：最後の行を基底として、抽出値と除外状態の更新を後方帰納法で反復する。
規約：正の arity で実際の Schedule を使う。
使われ方：TR の標準項の値と一般の全射性を証明する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：指定行以後の正しい抽出は元の語の対応する尾部（BF §1.4.3）。
方針：最後の行の抽出と一行の値・状態更新を後方帰納法で合成する。
規約：除外状態はその行の開始位置までの pastFinals。
使われ方：全行で元の語を得ることの帰納的な主張。 -/
lemma reduceRows_canonical_from {n d : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) (hn : 0 < n)
    (i : Fin (d + 1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.wordRows v (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalLengths v)).drop i.val)
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.pastFinals (List.ofFn v.val) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rowStart v i)) =
        some ((List.ofFn v.val).drop (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rowStart v i)) := by
  induction i using Fin.reverseInduction with
  | last =>
    simp only [Fin.val_last]
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.wordRows_drop_last v (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalLengths v), _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalLengths_last v]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_canonical_last v hn
  | cast i ih =>
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.wordRows_drop_cons v (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalLengths v) i.castSucc]
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows]
    rw [ite_eq_left ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalLengths_pos v hn i.castSucc,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalLengths_le_available v i.castSucc⟩]
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalLengths_castSucc]
    simp only [Nat.add_sub_cancel]
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRows_exclusion_update]
    change Option.map _
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.wordRows v (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalLengths v)).drop i.succ.val)
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.pastFinals (List.ofFn v.val) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rowStart v i.succ))) = _
    rw [ih]
    simp only [Option.map_some]
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRows_extract_original_segment]
    have hs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rowStart_le_caesuraAt v i
    have hd : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rowStart v i.succ = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rowStart v i.castSucc +
        ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraAt v i).val - _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rowStart v i.castSucc + 1) := by
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rowStart_succ_eq_caesuraAt]
      omega
    rw [hd, ← List.drop_drop]
    exact congrArg some (List.take_append_drop _ _)

/-- 概要：標準行長で全行を抽出すると元の全射語になる（BF §1.4.3）。
方針：後続行の抽出の式を最初の行に適用する。
規約：最初の除外状態は空。
使われ方：TR の和の標準項の値を計算する。 -/
lemma reduceRows_canonical {n d : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) (hn : 0 < n) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalVertices v) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalSchedule v hn)) [] =
      some (List.ofFn v.val) := by
  have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_canonical_from v hn 0
  simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows_canonical_eq_wordRows, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalSchedule, Fin.val_zero, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rowStart_zero,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.pastFinals, List.take_zero, List.dedup_nil, List.filter_nil, List.drop_zero] using h

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
