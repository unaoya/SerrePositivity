module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FirstColumnForwardForwardFunctor

/-!
# 元の前向きの切断関手の忠実性

概要：先頭の一列と残りの元の語を接合点で切り出す。
方針：底の指定射・残りの全縦射・先頭列の Hom を保持する。
規約：元の対象と全縦射を使う。圏同値と他の向きは後続。
使われ方：DK9.4・10.3の全語の分解。

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
lemma forwardForwardFunctor_map_injective {S T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardSource W w X Y}
    (h k : S ⟶ T) (he : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardFunctor W w X Y).map h =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardFunctor W w X Y).map k) : h = k := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.hom_ext
  intro j
  by_cases hj0 : j.val = 0
  · have hj : j = 0 := Fin.ext hj0
    subst j
    exact h.first.trans k.first.symm
  · by_cases hj1 : j.val = 1
    · have hj : j = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .forward w)
          (Fin.last (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward).length) := by apply Fin.ext; exact hj1
      subst j
      exact congrArg (fun z : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardObject W w X Y S ⟶
          _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardObject W w X Y T =>
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.baseMap z).hom) he
    · let i : Fin (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .forward w).length := ⟨j.val - 2, by
        have hlt := j.isLt
        change j.val < 1 + (w.length + 1) + 1 at hlt
        change j.val - 2 < w.length + 1
        omega⟩
      have hj : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .forward w) i.succ = j := by
        apply Fin.ext
        change 1 + (j.val - 2 + 1) = j.val
        omega
      rw [← hj]
      exact congrArg (fun z : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardObject W w X Y S ⟶
          _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardObject W w X Y T =>
        (show S.vertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .forward w) i.succ) ⟶
            T.vertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .forward w) i.succ) from
          (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.leftMap z).app i.succ)) he

instance forwardForwardFunctor_faithful : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardFunctor W w X Y).Faithful where
  map_injective := forwardForwardFunctor_map_injective W w X Y _ _
end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
