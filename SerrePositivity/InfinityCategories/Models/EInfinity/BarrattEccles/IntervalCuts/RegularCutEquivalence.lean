module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.RepeatCutPairs

/-!
模型。文献の定義との比較は後で
# 元切断非零の削除項と反復色の左右二削除の有限同値

概要：Berger–Fresse §2.2.7 の元切断非零部分を反復位置対と削除側で添字付ける。
方針：全射削除の同色相手と、非零元切断の左右単射性を使う。
規約：削除後の切断位置は同じ元切断点への一意な逆像。
使われ方：全削除和の元切断非零部分を反復色因子境界へ変換する。
-/

@[expose] public section

noncomputable section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

variable {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n (d + 1))

/-- 概要：反復位置対と側番号から元切断非零削除項への写像（BF §2.2.7）。
方針：指定側の正規化削除切断を取る。
規約：側零は左、一は右。
使われ方：有限同値の順写像。 -/
def regularCutMap (z : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.RepeatCutPair u.val × Fin 2) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NormalizedDeletedCut.Regular u.val :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.RepeatCutPair.normalizedCut u z.1 z.2

/-- 概要：反復位置対と削除側は実際の元切断非零削除項から一意に戻る（BF §2.2.7）。
方針：削除位置と切断位置から元切断点を戻し、両側の単射性で反対同色位置を決める。
規約：左右の削除を混同すると切断点を跨ぐ順序に矛盾する。
使われ方：全削除和の添字替えの単射側。 -/
lemma regularCutMap_injective : Function.Injective (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.regularCutMap u) := by
  rintro ⟨c, s⟩ ⟨e, t⟩ he
  have hi := congrArg (fun z : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NormalizedDeletedCut.Regular u.val => z.val.deleted) he
  change c.deleted s = e.deleted t at hi
  have hpos := congrArg (fun z : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NormalizedDeletedCut.Regular u.val =>
    z.val.deleted.succAbove z.val.pivot) he
  have hp : c.pivot = e.pivot := (c.erasePosition_spec s).symm.trans
    (hpos.trans (e.erasePosition_spec t))
  have hst : s = t := by
    fin_cases s <;> fin_cases t
    · rfl
    · change c.left = e.right at hi
      have hc := c.straddles.1
      rw [hi, hp] at hc
      exact False.elim ((not_lt_of_ge e.straddles.2.le) hc)
    · change c.right = e.left at hi
      have hc := c.straddles.2
      rw [hi, hp] at hc
      exact False.elim ((not_lt_of_ge e.straddles.1.le) hc)
    · rfl
  cases hst
  apply congrArg (fun z : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.RepeatCutPair u.val => (z, s))
  fin_cases s
  · change c.left = e.left at hi
    have hr := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge_right_injective c.nondegenerate c.right e.right c.straddles.2.le
      (by rw [hp]; exact e.straddles.2.le)
      ((c.same_color.symm.trans (congrArg u.val hi)).trans e.same_color)
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.RepeatCutPair.ext hp hi hr
  · change c.right = e.right at hi
    have hl := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge_left_injective c.nondegenerate c.left e.left c.straddles.1.le
      (by rw [hp]; exact e.straddles.1.le)
      ((c.same_color.trans (congrArg u.val hi)).trans e.same_color.symm)
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.RepeatCutPair.ext hp hl hi

/-- 概要：全ての元切断非零削除項は反復位置対の左右どちらかの削除（BF §2.2.7）。
方針：削除後全射性から別の同色出現を取り、前後順で位置対を作る。
規約：削除後切断位置は順序単射の単射性で元のものへ一致する。
使われ方：全削除和の添字替えの全射側。 -/
lemma regularCutMap_surjective : Function.Surjective (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.regularCutMap u) := by
  intro c
  obtain ⟨j, hji, hu⟩ := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase_surjective_iff u.val u.surjective c.val.deleted).mp c.val.surjective
  rcases lt_or_gt_of_ne hji with hji | hij
  · let e : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.RepeatCutPair u.val :=
      ⟨c.val.deleted.succAbove c.val.pivot, j, c.val.deleted, c.property, hji, hu⟩
    refine ⟨(e, 1), ?_⟩
    apply Subtype.ext
    apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NormalizedDeletedCut.ext
    · rfl
    · apply (Fin.succAbove_right_injective (p := c.val.deleted))
      exact e.erasePosition_spec 1
  · let e : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.RepeatCutPair u.val :=
      ⟨c.val.deleted.succAbove c.val.pivot, c.val.deleted, j, c.property, hij, hu.symm⟩
    refine ⟨(e, 0), ?_⟩
    apply Subtype.ext
    apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NormalizedDeletedCut.ext
    · rfl
    · apply (Fin.succAbove_right_injective (p := c.val.deleted))
      exact e.erasePosition_spec 0

/-- 概要：元切断非零の正規化削除切断と反復位置対・左右側の有限同値（BF §2.2.7）。
方針：位置対から削除切断への写像の全単射性を使う。
規約：実際の削除位置・切断位置を保持する。
使われ方：各反復色の二項を一つの因子境界公式へまとめる。 -/
def regularCutEquiv : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.RepeatCutPair u.val × Fin 2) ≃ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NormalizedDeletedCut.Regular u.val :=
  Equiv.ofBijective (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.regularCutMap u) ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.regularCutMap_injective u, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.regularCutMap_surjective u⟩

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
