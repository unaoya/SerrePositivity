module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.PartitionPositions
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.ComponentHorizontalExtraction
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.ComponentVerticalExtraction
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.FinalHorizontalExtraction

/-!
模型。文献の定義との比較は後で
# 二つの元の成功表と一つの合成分割の入力

概要：Berger–Fresse §1.5.7 の全成分を接続するため、元の二つの成功と分割を同じ添字で保持する。
方針：元の表・Schedule・基底語・実際の成功だけを入力とし、合成の成功は後で構成する。
規約：内側語長は正。空語の合成は別途扱う。
使われ方：全水平・垂直成分の共通位置と進行状態を指定する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：元の二つの成功表と端点を重ねた合成分割（BF §1.5.7）。
方針：従来の各成分転送の入力をまとめる。
規約：合成表の成功・経路との一致は入力に含めない。
使われ方：合成表全体の構成と成功を同じ元の入力から証明する。 -/
structure TableCompositionData (m n d e : ℕ) where
  outer : Fin (d + 1) → Equiv.Perm (Fin (m + 1))
  outerSchedule : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule (m + 1) d
  outerWord : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d
  outer_success : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows outer outerSchedule) [] = some (List.ofFn outerWord.val)
  inner : Fin (e + 1) → Equiv.Perm (Fin n)
  innerSchedule : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n e
  innerWord : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e
  inner_success : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows inner innerSchedule) [] = some (List.ofFn innerWord.val)
  slot : Fin (m + 1)
  cuts : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount outerWord.val slot) (n + e)
  inner_positive : 0 < n + e

namespace TableCompositionData

/-- 概要：元の外側指定値の出現回数（BF §1.5.7）。
方針：既存の有限出現列の長さを使う。
規約：全射語なので正。
使われ方：全成分列の反復回数。 -/
abbrev count {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e) : ℕ :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount c.outerWord.val c.slot

/-- 概要：外側の各出現成分の有限境界位置（BF §1.5.7）。
方針：既存の出現境界を同じ元の外側語に適用する。
規約：外側 arity は m+1 なので語長は正。
使われ方：水平成分の前後の元の位置。 -/
def outerPosition {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e) (i : ℕ) : Fin (m + 1 + d) :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceBoundaryPosition c.outerWord.val c.slot (by omega) i

/-- 概要：内側の各分割成分の有限境界位置（BF §1.5.7）。
方針：同じ元の分割の境界位置を使う。
規約：隣接成分の共有位置を一つの添字で指定する。
使われ方：垂直成分の前後と水平成分の固定内側位置。 -/
def innerPosition {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e) (i : ℕ) : Fin (n + e) :=
  c.cuts.boundaryPosition c.inner_positive i

/-- 概要：第 i 水平成分の始状態（BF §1.5.7）。
方針：元の外側境界と内側境界の実際の進行状態を合成する。
規約：最後の水平成分も同じ式。
使われ方：全成分を接続する共通の状態列。 -/
noncomputable def state {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e) (i : ℕ) :
    List (Fin (m + n)) :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved c.slot
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRemoved c.outer c.outerSchedule c.outerWord.val c.outer_success (c.outerPosition i))
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRemoved c.inner c.innerSchedule c.innerWord.val c.inner_success (c.innerPosition i))

/-- 概要：第 i 水平成分の終状態であり垂直成分の始状態（BF §1.5.7）。
方針：外側だけを次の出現まで進め、内側は同じ境界に保つ。
規約：指定値はまだ除外しない。
使われ方：同じ指定出現で水平から垂直へ接続する。 -/
noncomputable def betweenState {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e) (i : ℕ) :
    List (Fin (m + n)) :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved c.slot
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRemoved c.outer c.outerSchedule c.outerWord.val c.outer_success
      (c.outerPosition (i + 1)))
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRemoved c.inner c.innerSchedule c.innerWord.val c.inner_success (c.innerPosition i))

end TableCompositionData

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
