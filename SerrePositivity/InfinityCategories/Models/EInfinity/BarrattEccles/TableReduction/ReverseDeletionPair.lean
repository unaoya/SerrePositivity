module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReverseOccurrences
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.FinalDeletionPair

/-!
模型。文献の定義との比較は後で
# 行末削除から逆に構成した削除項の相殺

概要：Berger–Fresse §1.4.4 の逆 Schedule の二つの削除係数を比較する。
方針：短縮行末が直前出現であることを使い、最終出現の負符号を計算する。
規約：係数環は任意、削除後の次数は d−1、退化出力も保持する。
使われ方：行末側からも実際の成功出力と逆符号の二項を構成する。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

namespace ReverseTransferData

variable {n d : ℕ} {w : Fin (d + 1) → Equiv.Perm (Fin n)}
  {r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d} {out : List (Fin n)} {q : Fin out.length}

/-- 概要：逆 Schedule の挿入位置の削除係数は元の行番号の符号の負（BF §1.4.4）。
方針：直前出現を短縮行末と同定して最終出現の係数公式を適用する。
規約：変更後の出力の全射性・非退化性を要求しない。
使われ方：逆側の二項の相殺を追加の符号仮定なしに与える。 -/
lemma point_coefficient (b : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReverseTransferData w r out q) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient (fun j : Fin b.new.length => b.new[j.val]) b.point =
      -((-1 : ℤ) ^ b.early.val) := by
  obtain ⟨hp, he⟩ := b.point_previousOccurrence
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient_final _ _ b.point_not_caesura hp]
  congr 1
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionCoefficient_schedule_rowEnd w _ b.new b.success b.early
  have hend := b.shortened_end
  change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleEnd _ b.early = _
  omega

/-- 概要：逆構成した二項は正規化削除和でも相殺（BF §1.4.4）。
方針：元の行末の係数と挿入点の負符号、削除後の語の一致を用いる。
規約：削除後の次数は d−1。
使われ方：残余の行末削除を全体の有限和の相殺に組み込む。 -/
lemma pair_cancel (A : Type u) [CommRing A] (b : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReverseTransferData w r out q)
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] = some out) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.listDeletionTerm A (d := d - 1) out q +
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.listDeletionTerm A (d := d - 1) b.new b.point = 0 := by
  have hq : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient (fun j : Fin out.length => out[j.val]) q =
      (-1 : ℤ) ^ b.early.val :=
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionCoefficient_schedule_rowEnd w r out h b.early q b.row_end
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.listDeletionTerm, hq, b.point_coefficient, b.deleted_eq, neg_zsmul,
    add_neg_cancel]

end ReverseTransferData

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
