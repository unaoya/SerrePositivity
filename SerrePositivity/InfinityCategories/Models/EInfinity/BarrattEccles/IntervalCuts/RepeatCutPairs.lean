module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NormalizedDeletedCuts
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.DeletedActivePositions

/-!
模型。文献の定義との比較は後で
# 非零元切断を跨ぐ反復色の位置対と二つの削除

概要：Berger–Fresse §2.2.7 の非零元切断の各反復色を二出現の位置対として保持する。
方針：左・右出現の順序と同色を記録し、切断点を残した二つの削除切断を構成する。
規約：側番号零は左削除、一は右削除。
使われ方：正規化削除の元切断非零部分を二項の因子境界へまとめる。
-/

@[expose] public section

noncomputable section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：非零切断を跨ぐ反復色の二出現（BF §2.2.7）。
方針：元切断点・前後二出現・非零性・順序・同色を保持する。
規約：この二出現以外の同色位置は存在しない。
使われ方：二削除を一つの辺因子境界へまとめる有限添字。 -/
@[ext] structure RepeatCutPair {n l : ℕ} (u : Fin l → Fin n) where
  /-- 概要：元の非零切断点（BF §2.2.7）。
  方針：元の語の位置を保持する。
  規約：二出現の間にある。
  使われ方：元の出力テンソル。 -/
  pivot : Fin l
  /-- 概要：反復色の前の出現（BF §2.2.7）。
  方針：元の有限位置を保持する。
  規約：切断点より前。
  使われ方：終点境界に対応する左削除。 -/
  left : Fin l
  /-- 概要：反復色の後の出現（BF §2.2.7）。
  方針：元の有限位置を保持する。
  規約：切断点より後。
  使われ方：始点境界に対応する右削除。 -/
  right : Fin l
  /-- 概要：元の辺切断の非零性（BF §2.2.7）。
  方針：左右単射性の証明を保持する。
  規約：退化元切断は含まない。
  使われ方：二削除後の非零性。 -/
  nondegenerate : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u pivot
  /-- 概要：二出現の厳密順序（BF §2.2.7）。
  方針：前後を固定する。
  規約：左右出現は異なる。
  使われ方：削除係数の符号と境界端点の区別。 -/
  ordered : left < right
  /-- 概要：前後の出現色の一致（BF §2.2.7）。
  方針：同色の二位置として記録する。
  規約：左から右への等式。
  使われ方：削除後の全射性と出力辺の境界。 -/
  same_color : u left = u right

variable {n l : ℕ} {u : Fin l → Fin n}

/-- 概要：反復位置対の添字型は有限（BF §2.2.7）。
方針：三つの有限位置の組へ単射で写す。
規約：証明は個数を増やさない。
使われ方：反復色因子の有限和。 -/
instance _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.instFiniteRepeatCutPair : Finite (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.RepeatCutPair u) :=
  Finite.of_injective (fun c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.RepeatCutPair u => (c.pivot, c.left, c.right)) (by
    intro c e h
    apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.RepeatCutPair.ext
    · exact congrArg Prod.fst h
    · exact congrArg (fun t => t.2.1) h
    · exact congrArg (fun t => t.2.2) h)

/-- 概要：有限な反復位置対を全て列挙する（BF §2.2.7）。
方針：有限性から Fintype を選ぶ。
規約：非計算的選択は列挙だけ。
使われ方：全反復色因子境界の和。 -/
instance _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.instFintypeRepeatCutPair : Fintype (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.RepeatCutPair u) := Fintype.ofFinite _

namespace RepeatCutPair

/-- 概要：二出現は元切断点を厳密に跨ぐ（BF §2.2.7）。
方針：非零切断の同色対の一般公式を使う。
規約：両不等号は厳密。
使われ方：二削除とも切断点を残す。 -/
lemma straddles (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.RepeatCutPair u) : c.left < c.pivot ∧ c.pivot < c.right :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.repeated_straddles c.nondegenerate c.ordered c.same_color

/-- 概要：側番号で指定する削除位置（BF §2.2.7）。
方針：零なら前の出現、一なら後の出現を取る。
規約：側番号は Fin 2。
使われ方：位置対を二つの実際の削除項へ展開する。 -/
def deleted (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.RepeatCutPair u) (s : Fin 2) : Fin l := if s = 0 then c.left else c.right

/-- 概要：削除する側とは反対の同色位置（BF §2.2.7）。
方針：前後を反転して選ぶ。
規約：削除位置自身ではない。
使われ方：削除後の全射性。 -/
def partner (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.RepeatCutPair u) (s : Fin 2) : Fin l := if s = 0 then c.right else c.left

/-- 概要：二削除位置はいずれも元切断点と異なる（BF §2.2.7）。
方針：同色対が切断点を厳密に跨ぐことを使う。
規約：元切断点を削除しない。
使われ方：削除後切断位置の復元。 -/
lemma deleted_ne_pivot (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.RepeatCutPair u) (s : Fin 2) : c.deleted s ≠ c.pivot := by
  fin_cases s
  · exact ne_of_lt c.straddles.1
  · exact ne_of_gt c.straddles.2

/-- 概要：反対側は削除位置と異なる同色出現（BF §2.2.7）。
方針：二位置の順序と同色等式を両側へ適用する。
規約：どちらの側番号にも成立する。
使われ方：実際の削除語の全射性。 -/
lemma partner_spec (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.RepeatCutPair u) (s : Fin 2) :
    c.partner s ≠ c.deleted s ∧ u (c.partner s) = u (c.deleted s) := by
  fin_cases s
  · exact ⟨ne_of_gt c.ordered, c.same_color.symm⟩
  · exact ⟨ne_of_lt c.ordered, c.same_color⟩

/-- 概要：位置対の指定側を削除した後の元切断点の位置（BF §2.2.7）。
方針：削除の順序単射の像から元切断点を戻す。
規約：一意に定まる切断位置を非計算的に選ぶ。
使われ方：実際の削除切断の構成。 -/
def erasePosition {n l : ℕ} {u : Fin (l + 1) → Fin n} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.RepeatCutPair u) (s : Fin 2) :
    Fin l := Classical.choose (Fin.exists_succAbove_eq (c.deleted_ne_pivot s).symm)

/-- 概要：選んだ削除後位置は同じ元切断点へ戻る（BF §2.2.7）。
方針：順序単射の逆像の仕様を使う。
規約：削除側を変えても元切断点は共通。
使われ方：二削除の値を同じ因子境界へ比較する。 -/
lemma erasePosition_spec {n l : ℕ} {u : Fin (l + 1) → Fin n}
    (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.RepeatCutPair u) (s : Fin 2) : (c.deleted s).succAbove (c.erasePosition s) = c.pivot :=
  Classical.choose_spec (Fin.exists_succAbove_eq (c.deleted_ne_pivot s).symm)

/-- 概要：反復位置対の指定側から実際の元切断非零削除項を構成する（BF §2.2.7）。
方針：反対同色位置で全射性を保ち、元非零切断を削除語へ制限する。
規約：元切断点と全出力の色は保つ。
使われ方：正規化削除項との有限同値。 -/
def normalizedCut {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n (d + 1)) (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.RepeatCutPair u.val) (s : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NormalizedDeletedCut.Regular u.val :=
  ⟨⟨c.deleted s, c.erasePosition s,
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase_surjective_iff u.val u.surjective _).mpr ⟨c.partner s, c.partner_spec s⟩,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.erase_edgeNondegenerate u.val _ _ (by rw [c.erasePosition_spec s]; exact c.nondegenerate)⟩,
    by rw [c.erasePosition_spec s]; exact c.nondegenerate⟩

end RepeatCutPair
end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
