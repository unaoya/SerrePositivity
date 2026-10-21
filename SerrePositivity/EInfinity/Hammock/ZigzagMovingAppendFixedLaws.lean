module

public import SerrePositivity.EInfinity.Hammock.ZigzagMovingAppendLaws

/-!
# 固定端点へ戻した貼り合わせの恒等則

概要：元の恒等縦射を貼ると、実際の固定端点 zigzag の恒等射になる。
方針：動く縦比較の恒等則を全成分で回収する。
規約：接合点の整合性と両端の固定条件の証明の選択には依存しない。
使われ方：ブロック図式の関手性。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.ZigzagAppend.Moving
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} [W.IsMultiplicative]
  {a b : Word} {X Y Z : C}

lemma fixedMap_id (S : Zigzag W a X Y) (T : Zigzag W b Y Z)
    (hj : HEq ((Zigzag.MovingHom.id S).app (Fin.last a.length))
      ((Zigzag.MovingHom.id T).app 0))
    (hf : (Zigzag.MovingHom.id S).app 0 = eqToHom (S.first.trans S.first.symm))
    (hl : (Zigzag.MovingHom.id T).app (Fin.last b.length) =
      eqToHom (T.last.trans T.last.symm)) :
    fixedMap (Zigzag.MovingHom.id S) (Zigzag.MovingHom.id T) hj hf hl = 𝟙 (obj S T) := by
  apply Zigzag.hom_ext
  intro j
  exact congrArg (fun f => f.app j) (map_id S T hj)

end SerrePositivity.EInfinity.Hammock.ZigzagAppend.Moving
