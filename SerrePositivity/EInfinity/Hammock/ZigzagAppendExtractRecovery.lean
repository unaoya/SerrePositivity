module

public import SerrePositivity.EInfinity.Hammock.ZigzagAppendPartRecovery
public import SerrePositivity.EInfinity.Hammock.ZigzagEndpointChange
public import SerrePositivity.EInfinity.Hammock.ZigzagAppendNaturalityArrows

/-!
# 元の連結後の左右の切り出しと端点移送による回収

概要：連結して切り出した元の左右の部分は同じ端点表示に戻すと元の対象になる。
方針：全頂点と全列の異種等式を使う。
規約：空語と全ての向きを含み、指定性の仮定を追加しない。
使われ方：DK9.4・10.3の分解の逆向きの回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Hammock.ZigzagAppend.Part
open CategoryTheory
variable {C : Type u} [Category.{u} C] {W : MorphismProperty C}
  {a b : Word} {X Y Z : C} (S : Zigzag W a X Y) (T : Zigzag W b Y Z)
lemma joint_eq : (leftObj (obj S T)).vertex (Fin.last a.length) = Y :=
  (vertex_left S T (Fin.last a.length)).trans S.last

lemma leftObj_obj : Zigzag.EndpointChange.obj rfl (joint_eq S T) (leftObj (obj S T)) = S := by
  apply Zigzag.object_ext
  · intro j
    exact vertex_left S T j
  · intro i
    change HEq (eqToHom _ ≫ (obj S T).arrow (i.castAdd b.length) ≫ eqToHom _) (S.arrow i)
    simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
    exact arrow_left_heq S T i

lemma rightObj_obj : Zigzag.EndpointChange.obj (joint_eq S T) rfl (rightObj (obj S T)) = T := by
  apply Zigzag.object_ext
  · intro j
    exact vertex_right S T j
  · intro i
    change HEq (eqToHom _ ≫ (obj S T).arrow (i.natAdd a.length) ≫ eqToHom _) (T.arrow i)
    simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
    exact arrow_right_heq S T i
end SerrePositivity.EInfinity.Hammock.ZigzagAppend.Part
