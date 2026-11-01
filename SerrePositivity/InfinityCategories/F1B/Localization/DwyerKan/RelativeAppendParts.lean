module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.RelativeAppendObjects
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.RelativeFixedZigzagFunctor
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagAppendParts

/-!
# 元の相対関手による前後の部分の回収

概要：元の相対関手と全ての端点表示を保って切断の各成分を送る。
方針：元の指定部分圏の関手と全係数の元の自然変換を使う。
規約：始点・終点の表示を等式で移し、元の射を保持する。
使われ方：DK9.4・10.3の分解の全相対作用素への自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Hammock.ZigzagAppend.Part
open CategoryTheory
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  {W : MorphismProperty C} [W.IsMultiplicative] {V : MorphismProperty D} [V.IsMultiplicative]
  {a b : Word} {X Y : C} {X' Y' : D} (F : LocalizerMorphism W V)
  (hX : F.functor.obj X = X') (hY : F.functor.obj Y = Y')
lemma left_relative_obj (S : Zigzag W (Word.append a b) X Y) :
    leftObj ((Zigzag.Relative.fixedFunctor F hX hY).obj S) =
      (Zigzag.Relative.fixedFunctor F hX rfl).obj (leftObj S) := by
  apply Zigzag.object_ext
  · intro j; rfl
  · intro i
    change HEq (eqToHom _ ≫ F.functor.map (S.arrow (i.castAdd b.length)) ≫ eqToHom _)
      (F.functor.map (eqToHom _ ≫ S.arrow (i.castAdd b.length) ≫ eqToHom _))
    simp only [Functor.map_comp, eqToHom_map, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff,
      heq_eqToHom_comp_iff, heq_comp_eqToHom_iff]
    rfl
lemma right_relative_obj (S : Zigzag W (Word.append a b) X Y) :
    rightObj ((Zigzag.Relative.fixedFunctor F hX hY).obj S) =
      (Zigzag.Relative.fixedFunctor F rfl hY).obj (rightObj S) := by
  apply Zigzag.object_ext
  · intro j; rfl
  · intro i
    change HEq (eqToHom _ ≫ F.functor.map (S.arrow (i.natAdd a.length)) ≫ eqToHom _)
      (F.functor.map (eqToHom _ ≫ S.arrow (i.natAdd a.length) ≫ eqToHom _))
    simp only [Functor.map_comp, eqToHom_map, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff,
      heq_eqToHom_comp_iff, heq_comp_eqToHom_iff]
    rfl
end SerrePositivity.EInfinity.Hammock.ZigzagAppend.Part
