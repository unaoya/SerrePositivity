module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.FirstColumnForwardForwardFunctor

/-!
# 元の前向きの切断関手の忠実性

概要：先頭の一列と残りの元の語を接合点で切り出す。
方針：底の指定射・残りの全縦射・先頭列の Hom を保持する。
規約：元の対象と全縦射を使う。圏同値と他の向きは後続。
使われ方：DK9.4・10.3の全語の分解。
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
lemma forwardForwardFunctor_map_injective {S T : forwardForwardSource W w X Y}
    (h k : S ⟶ T) (he : (forwardForwardFunctor W w X Y).map h =
      (forwardForwardFunctor W w X Y).map k) : h = k := by
  apply Zigzag.hom_ext
  intro j
  by_cases hj0 : j.val = 0
  · have hj : j = 0 := Fin.ext hj0
    subst j
    exact h.first.trans k.first.symm
  · by_cases hj1 : j.val = 1
    · have hj : j = Word.leftVertex (Word.single .forward) (Word.cons .forward w)
          (Fin.last (Word.single .forward).length) := by apply Fin.ext; exact hj1
      subst j
      exact congrArg (fun z : forwardForwardObject W w X Y S ⟶
          forwardForwardObject W w X Y T =>
        (TwoSidedGrothendieck.baseMap z).hom) he
    · let i : Fin (Word.cons .forward w).length := ⟨j.val - 2, by
        have hlt := j.isLt
        change j.val < 1 + (w.length + 1) + 1 at hlt
        change j.val - 2 < w.length + 1
        omega⟩
      have hj : Word.rightVertex (Word.single .forward) (Word.cons .forward w) i.succ = j := by
        apply Fin.ext
        change 1 + (j.val - 2 + 1) = j.val
        omega
      rw [← hj]
      exact congrArg (fun z : forwardForwardObject W w X Y S ⟶
          forwardForwardObject W w X Y T =>
        (show S.vertex (Word.rightVertex (Word.single .forward) (Word.cons .forward w) i.succ) ⟶
            T.vertex (Word.rightVertex (Word.single .forward) (Word.cons .forward w) i.succ) from
          (TwoSidedGrothendieck.leftMap z).app i.succ)) he

instance forwardForwardFunctor_faithful : (forwardForwardFunctor W w X Y).Faithful where
  map_injective := forwardForwardFunctor_map_injective W w X Y _ _
end SerrePositivity.EInfinity.Hammock.FirstColumn
