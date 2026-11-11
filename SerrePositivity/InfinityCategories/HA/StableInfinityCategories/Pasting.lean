module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PastingLeftAttachment

/-! # 押し出し四角形の貼り合わせ

概要：左四角形が押し出しのとき、右四角形が押し出しであることと外側が押し出しであることは同値。
方針：長方形を終端角への余錐とみなし、五頂点図式と四頂点図式の coslice を比較する。
規約：HTT Lemma 4.4.2.1 の押し出し側。三角構造には別途引き戻し側と安定性の補題を使う。
使われ方：S4 の cofiber 列の貼り合わせと八面体。
-/
@[expose] public section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：左四角形が押し出しなら右四角形と外側四角形の押し出し性は同値。
方針：右・外側の span への余極限判定の間に、左余極限頂点を付加する coslice の同値を挟む。
規約：F の面番号二が左、零が右、一が外側。値域は quasicategory。
使われ方：HTT Lemma 4.4.2.1 と S4 の cofiber の貼り合わせ。 -/
lemma isPushoutSquare_pasting_iff {X : SSet.{u}} [Quasicategory X]
    (F : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hleft : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 2)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 0) ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 1) :=
  (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.pastingCocone_isColimitCone_iff_right F).symm.trans
    ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingCocone_isColimitCone_iff_outerCocone F hleft).trans
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterCocone_isColimitCone_iff_outer F))

/-- 概要：隣り合う二つの押し出し四角形の外側は押し出し。
方針：左四角形を固定した右と外側の判定の順方向を使う。
規約：二つの四角形を含む実際の長方形を指定する。
使われ方：cofiber 列の合成の普遍性。 -/
lemma isPushoutSquare_pasting {X : SSet.{u}} [Quasicategory X]
    (F : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hleft : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 2))
    (hright : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 0)) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 1) :=
  (isPushoutSquare_pasting_iff F hleft).mp hright

/-- 概要：左と外側が押し出しなら右四角形も押し出し。
方針：左四角形を固定した右と外側の判定の逆方向を使う。
規約：値域は quasicategory。使われ方：八面体に現れる cofiber の判定。 -/
lemma isPushoutSquare_pasting_cancel_left {X : SSet.{u}} [Quasicategory X]
    (F : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hleft : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 2))
    (houter : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 1)) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 0) :=
  (isPushoutSquare_pasting_iff F hleft).mpr houter

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
