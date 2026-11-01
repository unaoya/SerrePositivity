module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagAppendObjects

/-!
# 連結した元の列への射の性質の移送

概要：任意の射の性質は、元の列と連結語の同じ列で同値である。
方針：元の等式だけによる両端の移送を消す。
規約：射の性質に合成閉性やモデル圏の仮定を要求しない。
使われ方：中央の実際の backward 列の自明 cofibration 性を検証する。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.ZigzagAppend
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} {a b : Word} {X Y Z : C}

lemma arrow_left_property (P : MorphismProperty C) (S : Zigzag W a X Y)
    (T : Zigzag W b Y Z) (i : Fin a.length) :
    P ((obj S T).arrow (i.castAdd b.length)) ↔ P (S.arrow i) := by
  dsimp only [obj]
  rw [Fin.addCases_left]
  exact Direction.transport_mem (source_left_eq S T i) (target_left_eq S T i).symm (S.arrow i)

lemma arrow_right_property (P : MorphismProperty C) (S : Zigzag W a X Y)
    (T : Zigzag W b Y Z) (i : Fin b.length) :
    P ((obj S T).arrow (i.natAdd a.length)) ↔ P (T.arrow i) := by
  dsimp only [obj]
  rw [Fin.addCases_right]
  exact Direction.transport_mem (source_right_eq S T i) (target_right_eq S T i).symm (T.arrow i)

end SerrePositivity.EInfinity.Hammock.ZigzagAppend
