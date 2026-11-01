module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.FirstColumnForwardForwardData

/-!
# 元の先頭 Hom の離散係数の恒等と合成

概要：元の相対関手を先頭 Hom の離散圏へ移す作用は恒等と合成に両立する。
方針：元の射の像と始点表示の移送を同じ Hom へ回収する。
規約：相対関手と固定対象の元の表示を保持する。
使われ方：DK10.3の元の二方向単体図式の右係数。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Hammock.FirstColumn
open CategoryTheory Opposite SimplicialLocalization
variable {C D E : RelativeCategory.{u}} (w : Word)
lemma forwardForwardRightMap_id_heq (F : C ⟶ C) (h : F = 𝟙 C)
    (X Y : C.category) (hX : F.functor.obj X = X) (Z : WideSubcategory C.weakEquivalences) :
    HEq ((forwardForwardRightMap (Y := Y) (Y' := Y) w F hX).app Z)
      (𝟙 (Cat.of (Discrete (X ⟶ Z.obj)))) := by
  cases h
  apply heq_of_eq
  apply Cat.Hom.ext
  refine CategoryTheory.Functor.ext (fun e => Discrete.ext ?_) ?_
  · change (𝟙 X) ≫ e.as = e.as
    exact Category.id_comp _
  · intro e e' f
    exact @Discrete.hom_eq (X ⟶ Z.obj) _ _ _ _

lemma forwardForwardRightMap_comp_heq (F : C ⟶ D) (G : D ⟶ E) (H : C ⟶ E)
    (h : H = F ≫ G) (X Y : C.category) (X' Y' : D.category) (X'' Y'' : E.category)
    (hX : F.functor.obj X = X') (hX' : G.functor.obj X' = X'') (hXH : H.functor.obj X = X'')
    (Z : WideSubcategory C.weakEquivalences) :
    HEq ((forwardForwardRightMap (Y := Y) (Y' := Y'') w H hXH).app Z)
      (((forwardForwardRightMap (Y := Y) (Y' := Y') w F hX).app Z) ≫
        ((forwardForwardRightMap (Y := Y') (Y' := Y'') w G hX').app
          ((markedCategoryMap F).obj Z))) := by
  cases h
  apply heq_of_eq
  apply Cat.Hom.ext
  refine CategoryTheory.Functor.ext (fun e => Discrete.ext ?_) ?_
  · change eqToHom hXH.symm ≫ G.functor.map (F.functor.map e.as) =
      eqToHom hX'.symm ≫ G.functor.map (eqToHom hX.symm ≫ F.functor.map e.as)
    simp only [Functor.map_comp, eqToHom_map, eqToHom_trans_assoc]
  · intro e e' f
    exact @Discrete.hom_eq (X'' ⟶ G.functor.obj (F.functor.obj Z.obj)) _ _ _ _
end SerrePositivity.EInfinity.Hammock.FirstColumn
