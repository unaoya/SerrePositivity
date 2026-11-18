module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NormalizedDeletedCuts
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.ResidualCutGeometry
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.PivotResidualIndices

/-!
模型。文献の定義との比較は後で
# 正規化削除切断の二つの障害部分と既存の相殺添字の同値

概要：Berger–Fresse §2.2.7 の正規化全削除和から既存の二種類の障害添字へ移す。
方針：全射性は同色相手から復元し、非切断点障害の位置は一意性で戻す。
規約：元の語は全射な非退化基底語。
使われ方：三部分分割後に既存の全和相殺・境界比較を適用する。
-/

@[expose] public section

noncomputable section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NormalizedDeletedCut

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

variable {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n (d + 1))

/-- 概要：非切断点障害添字を正規化削除切断の対応部分へ埋め込む（BF §2.2.7）。
方針：障害の同色相手から削除後全射性を得る。
規約：障害位置自身は像で保持しない。
使われ方：既存の固定点なし対合との有限同値。 -/
def fromNonpivot (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NonpivotResidualCut u.val) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NormalizedDeletedCut.Nonpivot u.val :=
  ⟨⟨c.deleted, c.pivot, (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase_surjective_iff u.val u.surjective c.deleted).mpr
      ⟨c.defect, c.defect_spec.1, c.defect_spec.2.1⟩, c.nondegenerate⟩,
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cutDeletionDefect_exists_iff u.val c.deleted c.pivot c.nondegenerate).mp
      ⟨c.defect, c.defect_spec⟩, Ne.symm c.pivot_color_ne⟩

/-- 概要：非切断点障害から正規化部分への写像は単射（BF §2.2.7）。
方針：削除・切断位置が一致すれば障害位置の一意性を使う。
規約：証明フィールドは proof irrelevance で一致する。
使われ方：有限同値の単射側。 -/
lemma fromNonpivot_injective : Function.Injective (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NormalizedDeletedCut.fromNonpivot u) := by
  intro c e he
  have hi := congrArg (fun z : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NormalizedDeletedCut.Nonpivot u.val => z.val.deleted) he
  have hp := congrArg (fun z : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NormalizedDeletedCut.Nonpivot u.val => z.val.pivot) he
  change c.deleted = e.deleted at hi
  change c.pivot = e.pivot at hp
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NonpivotResidualCut.ext hi hp
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cutDeletionDefect_unique u.val c.deleted c.pivot c.nondegenerate
    c.defect e.defect c.defect_spec
  simpa only [← hi, ← hp] using e.defect_spec

/-- 概要：正規化削除の非切断点部分から障害添字を復元できる（BF §2.2.7）。
方針：元切断の退化性から障害位置を取り、色の不一致で切断点障害を除く。
規約：障害位置は一意だが全射性には存在だけを使う。
使われ方：有限同値の全射側。 -/
lemma fromNonpivot_surjective : Function.Surjective (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NormalizedDeletedCut.fromNonpivot u) := by
  intro c
  obtain ⟨j, hj⟩ := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cutDeletionDefect_exists_iff u.val c.val.deleted c.val.pivot
    c.val.nondegenerate).mpr c.property.1
  have hjp : j ≠ c.val.deleted.succAbove c.val.pivot := by
    intro he
    exact c.property.2 (hj.2.1.symm.trans (congrArg u.val he))
  let e : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NonpivotResidualCut u.val :=
    ⟨c.val.deleted, c.val.pivot, j, c.val.nondegenerate, hj, hjp⟩
  refine ⟨e, ?_⟩
  apply Subtype.ext
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NormalizedDeletedCut.ext rfl rfl

/-- 概要：切断点障害添字を正規化削除切断の対応部分へ埋め込む（BF §2.2.7）。
方針：残る切断点が削除色を保持することから全射性を得る。
規約：障害の色の等式をそのまま保持する。
使われ方：既存の切断点障害全和との有限同値。 -/
def fromPivot (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.PivotResidualCut u.val) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NormalizedDeletedCut.Pivot u.val :=
  ⟨⟨c.deleted, c.pivot, (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase_surjective_iff u.val u.surjective c.deleted).mpr
      ⟨c.deleted.succAbove c.pivot, Fin.succAbove_ne _ _, c.same_color.symm⟩,
    c.nondegenerate⟩, c.same_color⟩

/-- 概要：切断点障害から正規化部分への写像は単射（BF §2.2.7）。
方針：保持した二位置の一致を取り出す。
規約：証明の選択は個数を増やさない。
使われ方：有限同値の単射側。 -/
lemma fromPivot_injective : Function.Injective (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NormalizedDeletedCut.fromPivot u) := by
  intro c e he
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.PivotResidualCut.ext
  · exact congrArg (fun z : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NormalizedDeletedCut.Pivot u.val => z.val.deleted) he
  · exact congrArg (fun z : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NormalizedDeletedCut.Pivot u.val => z.val.pivot) he

/-- 概要：正規化削除の切断点部分は既存障害添字から来る（BF §2.2.7）。
方針：二位置と同色・非零性を取り出す。
規約：削除後全射性は障害添字へ追加しない。
使われ方：有限同値の全射側。 -/
lemma fromPivot_surjective : Function.Surjective (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NormalizedDeletedCut.fromPivot u) := by
  intro c
  refine ⟨⟨c.val.deleted, c.val.pivot, c.val.nondegenerate, c.property⟩, ?_⟩
  apply Subtype.ext
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NormalizedDeletedCut.ext rfl rfl

/-- 概要：非切断点障害添字と正規化削除の非切断点部分の有限同値（BF §2.2.7）。
方針：障害を忘れる写像の全単射性を使う。
規約：実際の削除位置と切断位置を保持する。
使われ方：正規化全削除和から固定点なし対合の相殺へ移す。 -/
def nonpivotEquiv : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NonpivotResidualCut u.val ≃ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NormalizedDeletedCut.Nonpivot u.val :=
  Equiv.ofBijective (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NormalizedDeletedCut.fromNonpivot u) ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NormalizedDeletedCut.fromNonpivot_injective u, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NormalizedDeletedCut.fromNonpivot_surjective u⟩

/-- 概要：切断点障害添字と正規化削除の切断点部分の有限同値（BF §2.2.7）。
方針：全射性を付ける写像の全単射性を使う。
規約：実際の削除位置と切断位置を保持する。
使われ方：正規化全削除和から切断点色の全因子境界和へ移す。 -/
def pivotEquiv : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.PivotResidualCut u.val ≃ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NormalizedDeletedCut.Pivot u.val :=
  Equiv.ofBijective (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NormalizedDeletedCut.fromPivot u) ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NormalizedDeletedCut.fromPivot_injective u, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NormalizedDeletedCut.fromPivot_surjective u⟩

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NormalizedDeletedCut
