module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.ResidualCutPartner

/-!
模型。文献の定義との比較は後で
# 切断点以外の障害を持つ削除項の固定点なし対合

概要：Berger–Fresse §2.2.7 の削除後だけ非零の項のうち非切断点障害を持つものを対にする。
方針：削除位置と一意な障害位置を交換し、同じ元切断点の新しい位置を戻す。
規約：有限な添字型に証明を保持し、相手の非零性も構成する。
使われ方：全削除和の余分な部分を固定点のない二項対で相殺する。
-/

@[expose] public section

noncomputable section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：削除後だけ非零で、障害が切断点でない切断項（BF §2.2.7）。
方針：元の削除位置・削除後の切断位置・障害位置を証明とともに保持する。
規約：元切断の退化性は障害の存在から導かれる。
使われ方：相殺対合の有限な定義域。 -/
@[ext] structure NonpivotResidualCut {n l : ℕ} (u : Fin (l + 1) → Fin n) where
  /-- 概要：元の削除文字の位置（BF §2.2.7）。
  方針：元の語の位置を保持する。
  規約：切断点は削除しない。
  使われ方：χ の削除項の添字。 -/
  deleted : Fin (l + 1)
  /-- 概要：削除後の非零切断の位置（BF §2.2.7）。
  方針：削除後の語の位置を保持する。
  規約：元の位置へは succAbove で戻す。
  使われ方：切断項の添字。 -/
  pivot : Fin l
  /-- 概要：元切断の同色重複の障害位置（BF §2.2.7）。
  方針：削除文字と同じ側の別の同色位置を保持する。
  規約：削除位置と異なる。
  使われ方：交換相手の削除位置。 -/
  defect : Fin (l + 1)
  /-- 概要：削除後の切断の非零性（BF §2.2.7）。
  方針：実際の非退化判定の証明を保持する。
  規約：元切断の非零性は要求しない。
  使われ方：余分な削除項の有効性。 -/
  nondegenerate : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u deleted) pivot
  /-- 概要：障害位置の同色・同側の条件（BF §2.2.7）。
  方針：障害述語の証明を保持する。
  規約：元切断の退化性を含意する。
  使われ方：交換とその一意性。 -/
  defect_spec : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.CutDeletionDefect u deleted pivot defect
  /-- 概要：障害位置が切断点と異なる条件（BF §2.2.7）。
  方針：同じ元切断点を相手の削除後にも残す。
  規約：切断点障害は別に扱う。
  使われ方：相手位置の存在。 -/
  defect_ne_pivot : defect ≠ deleted.succAbove pivot

variable {n l : ℕ} {u : Fin (l + 1) → Fin n}

/-- 概要：非切断点障害を持つ削除切断の添字は有限（BF §2.2.7）。
方針：三つの有限な位置の組へ単射で写す。
規約：証明フィールドは添字の個数を増やさない。
使われ方：余分な削除項の有限和。 -/
instance _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.instFiniteNonpivotResidualCut : Finite (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NonpivotResidualCut u) :=
  Finite.of_injective (fun c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NonpivotResidualCut u => (c.deleted, c.pivot, c.defect)) (by
    intro c d h
    apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NonpivotResidualCut.ext
    · exact congrArg Prod.fst h
    · exact congrArg (fun t => t.2.1) h
    · exact congrArg (fun t => t.2.2) h)

/-- 概要：有限な余分削除項の全体を有限和の添字として選ぶ（BF §2.2.7）。
方針：構成済みの有限性から Fintype を取る。
規約：非計算的な選択は添字列挙だけに使う。
使われ方：対合による有限和の相殺。 -/
instance _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.instFintypeNonpivotResidualCut : Fintype (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NonpivotResidualCut u) := Fintype.ofFinite _

namespace NonpivotResidualCut

/-- 概要：相手の削除後の切断位置（BF §2.2.7）。
方針：同じ元切断点へ戻る一意な相手位置を取る。
規約：相手の非零性は同じ存在証明に含まれる。
使われ方：削除項の交換対合。 -/
def partnerPosition (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NonpivotResidualCut u) : Fin l :=
  Classical.choose (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.residual_partner_existsUnique u c.deleted c.pivot c.nondegenerate
    c.defect c.defect_spec c.defect_ne_pivot)

/-- 概要：相手位置は同じ元切断点へ戻り、削除後の切断も非零（BF §2.2.7）。
方針：一意存在の証明から二つの性質を取り出す。
規約：元の語は固定する。
使われ方：交換後の切断項を型付けする。 -/
lemma partnerPosition_spec (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NonpivotResidualCut u) :
    c.defect.succAbove c.partnerPosition = c.deleted.succAbove c.pivot ∧
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u c.defect) c.partnerPosition :=
  (Classical.choose_spec (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.residual_partner_existsUnique u c.deleted c.pivot c.nondegenerate
    c.defect c.defect_spec c.defect_ne_pivot)).1

/-- 概要：削除位置と障害位置を交換する削除切断の対合（BF §2.2.7）。
方針：相手位置とその非零性を使い、障害条件を対称にする。
規約：同じ元切断点と同じ色を保持する。
使われ方：余分な削除項を二つずつ組にする。 -/
def swap (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NonpivotResidualCut u) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NonpivotResidualCut u where
  deleted := c.defect
  pivot := c.partnerPosition
  defect := c.deleted
  nondegenerate := c.partnerPosition_spec.2
  defect_spec := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.residual_partner_defect u c.deleted c.pivot c.defect c.defect_spec
    c.partnerPosition c.partnerPosition_spec.1
  defect_ne_pivot := by
    rw [c.partnerPosition_spec.1]
    exact Fin.ne_succAbove c.deleted c.pivot

/-- 概要：交換は元の切断点を保つ（BF §2.2.7）。
方針：相手位置の仕様を使う。
規約：削除前の位置で比較する。
使われ方：交換を二回行った位置を同定する。 -/
lemma swap_pivot (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NonpivotResidualCut u) :
    c.swap.deleted.succAbove c.swap.pivot = c.deleted.succAbove c.pivot :=
  c.partnerPosition_spec.1

/-- 概要：交換を二回行うと元の削除切断へ戻る（BF §2.2.7）。
方針：削除・障害位置は直接戻り、切断位置は順序単射の単射性で比較する。
規約：証明のフィールドは proof irrelevance で揃う。
使われ方：有限和の対合相殺に必要な反転則。 -/
@[simp] lemma swap_swap (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NonpivotResidualCut u) : c.swap.swap = c := by
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NonpivotResidualCut.ext
  · rfl
  · apply (Fin.succAbove_right_injective (p := c.deleted))
    exact c.swap.swap_pivot.trans c.swap_pivot
  · rfl

/-- 概要：余分な削除切断の交換は固定点を持たない（BF §2.2.7）。
方針：固定されれば異なる削除位置と障害位置が一致してしまう。
規約：切断点障害の項はこの定義域から除外している。
使われ方：二項対による相殺。 -/
lemma swap_ne (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NonpivotResidualCut u) : c.swap ≠ c := by
  intro h
  exact c.defect_spec.1 (congrArg (fun t : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NonpivotResidualCut u => t.deleted) h)

/-- 概要：余分な削除切断の交換は有限型の自己同値（BF §2.2.7）。
方針：同じ交換を順・逆の両方向に使う。
規約：全ての項と相手の非零性を保持する。
使われ方：添字替えによる有限和の相殺。 -/
def swapEquiv : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NonpivotResidualCut u ≃ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NonpivotResidualCut u where
  toFun := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NonpivotResidualCut.swap
  invFun := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NonpivotResidualCut.swap
  left_inv := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NonpivotResidualCut.swap_swap
  right_inv := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NonpivotResidualCut.swap_swap

end NonpivotResidualCut
end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
