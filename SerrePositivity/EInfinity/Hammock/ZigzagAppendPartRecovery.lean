module

public import SerrePositivity.EInfinity.Hammock.ZigzagAppendParts
public import SerrePositivity.EInfinity.Hammock.ZigzagExt

/-!
# 元の前後の部分から全体を回収する

概要：切り出した左右の部分を連結すると、元の全頂点と全列に戻る。
方針：接合点の左右で頂点を照合し、各列の二重の等式移送を消去する。
規約：元の任意の向きの語と空語を含む。
使われ方：局所置換の比較の値域を元の全体の恒等図式へ接続する。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.ZigzagAppend.Part
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} {a b : Word} {X Y : C}
  (S : Zigzag W (Word.append a b) X Y)

lemma rebuilt_vertex (j : Fin ((Word.append a b).length + 1)) :
    (obj (leftObj S) (rightObj S)).vertex j = S.vertex j := by
  change vertex (leftObj S) (rightObj S) j = _
  by_cases hj : j.val ≤ a.length
  · rw [vertex_le _ _ _ hj]
    apply congrArg S.vertex
    apply Fin.ext
    rfl
  · rw [vertex_gt _ _ _ hj]
    apply congrArg S.vertex
    apply Fin.ext
    change a.length + (j.val - a.length) = j.val
    omega

lemma rebuilt_arrow (j : Fin (Word.append a b).length) :
    HEq ((obj (leftObj S) (rightObj S)).arrow j) (S.arrow j) := by
  cases j using Fin.addCases with
  | left i =>
    apply HEq.trans (arrow_left_heq _ _ i)
    dsimp only [leftObj]
    simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
    rfl
  | right i =>
    apply HEq.trans (arrow_right_heq _ _ i)
    dsimp only [rightObj]
    simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
    rfl

lemma rebuilt_eq : obj (leftObj S) (rightObj S) = S :=
  Zigzag.object_ext _ _ (rebuilt_vertex S) (rebuilt_arrow S)

end SerrePositivity.EInfinity.Hammock.ZigzagAppend.Part
