module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionTransfers

/-!
模型。文献の定義との比較は後で
# 元の全成分を交互に連結した合成表の実際の成功

概要：Berger–Fresse §1.5.7 の水平・垂直の全ブロックを後続から接続して成功を構成する。
方針：残り成分数で再帰し、最後の水平から垂直・水平の転送を戻していく。
規約：共有頂点の二行と共有文字の二コピーはまだ融合しない。
使われ方：次に共有行を融合して実際の compositionPath の表へ移す元の成功。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：第 i 成分以降の全ブロックを連結した実際の合成行列（BF §1.5.7）。
方針：水平・垂直・残りの列とし、最後は最終水平成分だけ。
規約：共有頂点はこの段階では隣接する二行として残す。
使われ方：全成分の成功を示してから経路の共有頂点へ融合する。 -/
noncomputable def rawRows {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e)
    (i : ℕ) : List (List (Fin (m + n)) × ℕ) :=
  if hi : i < c.count then
    c.horizontalRows i ++ c.verticalRows ⟨i, hi⟩ ++ c.rawRows (i + 1)
  else c.horizontalRows c.count
termination_by c.count - i
decreasing_by omega

/-- 概要：共有文字を両側に含めた全成分列の出力語（BF §1.5.7）。
方針：各ブロックの実際の出力を同じ再帰で連結する。
規約：共有文字一つの削除は後続の共有行融合で行う。
使われ方：全表の成功出力を合成語へ照合する前の語。 -/
def rawWord {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e) (i : ℕ) : List (Fin (m + n)) :=
  if hi : i < c.count then
    c.horizontalWord i ++ c.verticalWord ⟨i, hi⟩ ++ c.rawWord (i + 1)
  else c.horizontalWord c.count
termination_by c.count - i
decreasing_by omega

/-- 概要：全成分の交互連結の表は元の進行状態から実際に抽出成功（BF §1.5.7）。
方針：最終水平を閉じ、垂直と水平の任意の後続への転送で再帰的に戻す。
規約：共有頂点と共有文字の融合はまだ行わない。
使われ方：経路の表へ融合する全ての成分を含む元の成功。 -/
lemma raw_success {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e)
    (i : ℕ) (hi : i ≤ c.count) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (c.rawRows i) (c.state i) = some (c.rawWord i) := by
  by_cases hlt : i < c.count
  · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData.rawRows, dite_eq_left hlt, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData.rawWord, dite_eq_left hlt]
    have hnext := c.raw_success (i + 1) (by omega)
    have hv := c.vertical_transfer ⟨i, hlt⟩ (c.rawRows (i + 1)) (c.rawWord (i + 1)) hnext
    have hh := c.horizontal_transfer ⟨i, hlt⟩ (c.verticalRows ⟨i, hlt⟩ ++ c.rawRows (i + 1))
      (c.verticalWord ⟨i, hlt⟩ ++ c.rawWord (i + 1)) hv
    simpa only [List.append_assoc] using hh
  · have he : i = c.count := by omega
    subst i
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData.rawRows, dite_eq_right (Nat.lt_irrefl _), _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData.rawWord, dite_eq_right (Nat.lt_irrefl _)]
    have hf := c.final_transfer [] [] rfl
    simpa only [List.append_nil] using hf
termination_by c.count - i
decreasing_by omega

/-- 概要：全成分を含む実際の合成表が空の除外状態から抽出成功（BF §1.5.7）。
方針：第零成分からの全成功の初期進行状態を空へ同定する。
規約：共有頂点とその文字はまだ二重に残す。
使われ方：全表を共有行の融合で実際の合成経路へ移す出発点。 -/
lemma raw_success_zero {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (c.rawRows 0) [] = some (c.rawWord 0) := by
  simpa only [c.state_zero] using c.raw_success 0 (Nat.zero_le _)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData
