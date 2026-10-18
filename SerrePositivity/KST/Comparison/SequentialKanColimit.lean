module

public import SerrePositivity.KST.Comparison.HornRightColimit
public import SerrePositivity.HomotopicalAlgebra.Diagram.ColimitWeakEquivalence
public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit

/-!
# 順序余極限による Kan 射と引き戻しの保存

概要：自然数添字の余極限は各行の Kan fibration と厳密な引き戻しを保つ。
方針：horn の有限表示可能性と型の filtered colimit・有限極限の交換を使う。
規約：Segal 1974 Proposition 1.6 の無限骨格を実際の余極限で処理する補助。
使われ方：図式の関手的 Kan 分解の順序余極限への適用。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits

/--
概要：各段階で Kan fibration である自然変換の順序余極限は Kan fibration。
方針：arrow 圏の実際の余極限に horn の持ち上げ性の保存を適用する。
規約：対象の Kan 性や遷移の単射性は不要。
使われ方：無限骨格での別分解の射影の Kan 性。
-/
theorem sequentialColim_rlp {F G : ℕ ⥤ SSet.{u}} (α : F ⟶ G)
    (hα : ∀ n, SSet.modelCategoryQuillen.J.rlp (α.app n)) :
    SSet.modelCategoryQuillen.J.rlp (colim.map α) :=
  hornRight_sequentialColimit (SerrePositivity.DiagramModel.arrowColimitCoconeIsColimit α) hα

/--
概要：自然数添字の余極限は厳密な引き戻しを保つ。
方針：型の filtered colimit と有限極限の交換を各単体次数で使う。
規約：単体集合の図式圏から単体集合への実際の余極限関手。
使われ方：厳密なファイバーの図式の余極限の同定。
-/
instance sequentialColim_preservesPullbacks :
    PreservesLimitsOfShape WalkingCospan (colim : (ℕ ⥤ SSet.{u}) ⥤ SSet.{u}) := by
  infer_instance

end SerrePositivity.KST.Comparison
