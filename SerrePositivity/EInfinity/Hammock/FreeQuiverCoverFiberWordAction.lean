module

public import SerrePositivity.EInfinity.Hammock.FreeQuiverCoverZigzagEquivalence
public import SerrePositivity.EInfinity.Hammock.ZigzagWordValue

/-!
# 元の全語の作用の値の fiber への制限

概要：元の全語の作用を元の値の等式で定まる全部分圏へ制限する。
方針：既存の値の不変性と元の遷移関手を使う。
規約：被覆を経由する別の語の作用で置き換えない。
使われ方：全語の値の fiber の厳密な圏値図式。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.FreeQuiverCover
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (A : Q) (Y : Paths Q)
  (β : (Quiver.FreeGroupoid.of Q).obj A ⟶ positiveEvaluation.obj Y)

def zigzagFiberWordAction {a b : Word} (f : a ⟶ b) :
    ZigzagValueFiber A a Y β ⥤ ZigzagValueFiber A b Y β where
  obj S := ⟨WordAction.obj f S.obj,
    (Zigzag.Value.wordAction_value positiveEvaluation positiveEvaluation_inverts_top f S.obj).trans
      S.property⟩
  map g := ObjectProperty.homMk ((WordAction.functor f).map g.hom)
  map_id S := ObjectProperty.hom_ext (zigzagValueProperty A _ Y β)
    ((WordAction.functor f).map_id S.obj)
  map_comp g h := ObjectProperty.hom_ext (zigzagValueProperty A _ Y β)
    ((WordAction.functor f).map_comp g.hom h.hom)

lemma zigzagFiberWordAction_inclusion {a b : Word} (f : a ⟶ b) :
    zigzagFiberWordAction A Y β f ⋙ (zigzagValueProperty A b Y β).ι =
      (zigzagValueProperty A a Y β).ι ⋙ WordAction.functor f := by
  apply CategoryTheory.Functor.hext
    (F := zigzagFiberWordAction A Y β f ⋙ (zigzagValueProperty A b Y β).ι)
    (G := (zigzagValueProperty A a Y β).ι ⋙ WordAction.functor f)
  · intro S
    rfl
  · intro S T g
    rfl

end SerrePositivity.EInfinity.Hammock.FreeQuiverCover
