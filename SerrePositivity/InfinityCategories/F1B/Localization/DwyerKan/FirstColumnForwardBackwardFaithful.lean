module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.FirstColumnForwardBackwardFunctor

/-!
# 元の混合二方向の切断関手の忠実性

概要：元の接合点の指定射と両側の全縦成分を保持して切断する。
方針：通常 Hom と残りの語の共変係数の積を使う。
規約：元の指定部分圏と実際の全射を使う。
使われ方：DK9.4・10.3の混合二方向の分解。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Hammock.FirstColumn
open CategoryTheory Opposite Zigzag.FirstBoundary
variable {C : Type u} [Category.{u} C] (W : MorphismProperty C) [W.IsMultiplicative]
  (w : Word) (X Y : C)
lemma forwardBackwardFunctor_map_injective {S T : forwardBackwardSource W w X Y}
    (h k : S ⟶ T) (he : (forwardBackwardFunctor W w X Y).map h =
      (forwardBackwardFunctor W w X Y).map k) : h = k := by
  apply Zigzag.hom_ext
  intro j
  by_cases hj0 : j.val = 0
  · have hj : j = 0 := Fin.ext hj0
    subst j
    exact h.first.trans k.first.symm
  · by_cases hj1 : j.val = 1
    · have hj : j = Word.leftVertex (Word.single .forward) (Word.cons .backward w)
          (Fin.last (Word.single .forward).length) := by apply Fin.ext; exact hj1
      subst j
      exact congrArg (fun z : forwardBackwardObject W w X Y S ⟶
          forwardBackwardObject W w X Y T =>
        (TwoSidedGrothendieck.baseMap z).hom) he
    · let i : Fin (Word.cons .backward w).length := ⟨j.val - 2, by
        have hlt := j.isLt
        change j.val < 1 + (w.length + 1) + 1 at hlt
        change j.val - 2 < w.length + 1
        omega⟩
      have hj : Word.rightVertex (Word.single .forward) (Word.cons .backward w) i.succ = j := by
        apply Fin.ext
        change 1 + (j.val - 2 + 1) = j.val
        omega
      rw [← hj]
      exact congrArg (fun z : forwardBackwardObject W w X Y S ⟶
          forwardBackwardObject W w X Y T =>
        (show S.vertex (Word.rightVertex (Word.single .forward) (Word.cons .backward w) i.succ) ⟶
            T.vertex (Word.rightVertex (Word.single .forward) (Word.cons .backward w) i.succ) from
          (TwoSidedGrothendieck.rightMap z).2.app i.succ)) he

instance forwardBackwardFunctor_faithful : (forwardBackwardFunctor W w X Y).Faithful where
  map_injective := forwardBackwardFunctor_map_injective W w X Y _ _
end SerrePositivity.EInfinity.Hammock.FirstColumn
