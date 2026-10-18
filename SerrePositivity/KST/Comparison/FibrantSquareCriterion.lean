module

public import SerrePositivity.KST.Comparison.HomotopyPullbackSymmetry

/-!
# Kan な縦射を持つ四角形の厳密ファイバーによる判定

概要：右側の縦射が Kan fibration のとき、ホモトピー引き戻し性を厳密な引き戻しへの比較で判定する。
方針：脚を交換し、恒等射を前半とする別分解の判定を使う。
規約：Segal 1974 Lemma 1.7 のファイバー模型の厳密化への補助。
使われ方：中央の対象から二つの厳密ファイバーへの局所化同型を得る。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits
open SerrePositivity.SimplicialModel

/--
概要：左脚が Kan fibration の四角形のホモトピー引き戻し性は、厳密な引き戻しへの比較の可逆性と同値。
方針：脚の交換の不変性と、恒等射から始まる別分解の判定を適用する。
規約：四角形を横に描いたとき、Kan な脚は右の縦射 f となる。
使われ方：span の中央から端点の厳密ファイバーへの比較。
-/
theorem isHomotopyPullback_iff_strict_of_left_fibration {P X Y Z : SSet.{u}}
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (sq : CommSq a b f g) (hf : SSet.modelCategoryQuillen.J.rlp f) :
    IsHomotopyPullback sq ↔ IsIso (AnodyneHomotopy.anodyneQ.map
      (pullback.lift b a sq.w.symm : P ⟶ pullback g f)) := by
  calc
    _ ↔ IsHomotopyPullback sq.flip := (isHomotopyPullback_flip_iff sq).symm
    _ ↔ IsIso (AnodyneHomotopy.anodyneQ.map
        (alternativePullbackComparison sq.flip (𝟙 X) f (Category.id_comp _))) :=
      isHomotopyPullback_iff_alternative sq.flip (𝟙 X)
        (SSet.anodyneExtensions.of_isIso _) f hf (Category.id_comp _)
    _ ↔ _ := by simp only [alternativePullbackComparison, Category.comp_id]

end SerrePositivity.KST.Comparison
