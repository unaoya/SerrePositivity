module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FirstColumnBackwardForwardFunctor

/-!
# 元の backward・forward の切断関手の忠実性

概要：元の指定 Hom と残りの語を同じ反変係数の積へ回収する。
方針：元の接合点・全縦成分と貼り戻しの全往復を使う。
規約：元の切断関手自体を保持する。
使われ方：DK9.4・10.3の残る混合二方向の分解。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory Opposite Zigzag.FirstBoundary
variable {C : Type u} [Category.{u} C] (W : MorphismProperty C) [W.IsMultiplicative]
  (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (X Y : C)
lemma backwardForwardFunctor_map_injective {S T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardForwardSource W w X Y}
    (h k : S ⟶ T) (he : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardForwardFunctor W w X Y).map h =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardForwardFunctor W w X Y).map k) : h = k := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.hom_ext
  intro j
  by_cases hj0 : j.val = 0
  · have hj : j = 0 := Fin.ext hj0
    subst j
    exact h.first.trans k.first.symm
  · by_cases hj1 : j.val = 1
    · have hj : j = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .forward w)
          (Fin.last (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward).length) := by apply Fin.ext; exact hj1
      subst j
      exact congrArg (fun z : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardForwardObject W w X Y S ⟶
          _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardForwardObject W w X Y T =>
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.baseMap z).hom) he
    · let i : Fin (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .forward w).length := ⟨j.val - 2, by
        have hlt := j.isLt
        change j.val < 1 + (w.length + 1) + 1 at hlt
        change j.val - 2 < w.length + 1
        omega⟩
      have hj : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .forward w) i.succ = j := by
        apply Fin.ext
        change 1 + (j.val - 2 + 1) = j.val
        omega
      rw [← hj]
      exact congrArg (fun z : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardForwardObject W w X Y S ⟶
          _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardForwardObject W w X Y T =>
        (show S.vertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .forward w) i.succ) ⟶
            T.vertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .forward w) i.succ) from
          (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.leftMap z).2.app i.succ)) he

instance backwardForwardFunctor_faithful : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardForwardFunctor W w X Y).Faithful where
  map_injective := backwardForwardFunctor_map_injective W w X Y _ _
end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
