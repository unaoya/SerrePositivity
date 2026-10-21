module

public import SerrePositivity.EInfinity.Hammock.FirstColumnBackwardBackwardFunctor

/-!
# 元の後向き二列の切断関手の忠実性

概要：元の接合点の指定射と両側の全縦成分を保持して切断する。
方針：指定 Hom の反変係数と残りの語の共変係数を使う。
規約：元の指定部分圏と実際の全射を使う。
使われ方：DK9.4・10.3の後向き二列の分解。
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
lemma backwardBackwardFunctor_map_injective {S T : backwardBackwardSource W w X Y}
    (h k : S ⟶ T) (he : (backwardBackwardFunctor W w X Y).map h =
      (backwardBackwardFunctor W w X Y).map k) : h = k := by
  apply Zigzag.hom_ext
  intro j
  by_cases hj0 : j.val = 0
  · have hj : j = 0 := Fin.ext hj0
    subst j
    exact h.first.trans k.first.symm
  · by_cases hj1 : j.val = 1
    · have hj : j = Word.leftVertex (Word.single .backward) (Word.cons .backward w)
          (Fin.last (Word.single .backward).length) := by apply Fin.ext; exact hj1
      subst j
      exact congrArg (fun z : backwardBackwardObject W w X Y S ⟶
          backwardBackwardObject W w X Y T =>
        (TwoSidedGrothendieck.baseMap z).hom) he
    · let i : Fin (Word.cons .backward w).length := ⟨j.val - 2, by
        have hlt := j.isLt
        change j.val < 1 + (w.length + 1) + 1 at hlt
        change j.val - 2 < w.length + 1
        omega⟩
      have hj : Word.rightVertex (Word.single .backward) (Word.cons .backward w) i.succ = j := by
        apply Fin.ext
        change 1 + (j.val - 2 + 1) = j.val
        omega
      rw [← hj]
      exact congrArg (fun z : backwardBackwardObject W w X Y S ⟶
          backwardBackwardObject W w X Y T =>
        (show S.vertex (Word.rightVertex (Word.single .backward) (Word.cons .backward w) i.succ) ⟶
            T.vertex (Word.rightVertex (Word.single .backward) (Word.cons .backward w) i.succ) from
          (TwoSidedGrothendieck.rightMap z).app i.succ)) he

instance backwardBackwardFunctor_faithful : (backwardBackwardFunctor W w X Y).Faithful where
  map_injective := backwardBackwardFunctor_map_injective W w X Y _ _
end SerrePositivity.EInfinity.Hammock.FirstColumn
