module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.TwoSidedGrothendieckDuality
public import SerrePositivity.EInfinity.Hammock.TwoSidedGrothendieckRightWeak

/-!
# 元の左係数比較と左右交換の可換式

概要：元の左係数比較を左右交換後の元の右係数比較と照合する。
方針：同じ二段の Grothendieck の map・pre の全成分を評価する。
規約：元の係数自然変換の自然性と全射の移送を保持する。
使われ方：DK §9.6の左係数の弱同値性。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.TwoSidedGrothendieck
open CategoryTheory Opposite

variable {W : Type u} [Category.{u} W] {F F' : Wᵒᵖ ⥤ Cat.{u, u}}
  (G : W ⥤ Cat.{u, u})

def leftCoefficientMap (α : F ⟶ F') : total F G ⥤ total F' G :=
  Grothendieck.pre (contravariantProjection F' ⋙ G) (contravariantMap α)

lemma leftCoefficientMap_projection (α : F ⟶ F') :
    leftCoefficientMap G α ⋙ projection = projection := rfl

lemma coefficientMap_factorization {G' : W ⥤ Cat.{u, u}} (α : F ⟶ F') (β : G ⟶ G') :
    coefficientMap α β = rightCoefficientMap F β ⋙ leftCoefficientMap G' α := rfl

lemma leftCoefficientMap_dualFunctor (α : F ⟶ F') :
    leftCoefficientMap G α ⋙ dualFunctor F' G =
      dualFunctor F G ⋙
        (rightCoefficientMap (dualLeft G) (Functor.whiskerRight α Cat.opFunctor)).op := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  apply Quiver.Hom.unop_inj
  refine Grothendieck.ext _ _ ?_ ?_
  · apply Quiver.Hom.unop_inj
    refine Grothendieck.ext _ _ ?_ ?_
    · rfl
    · simp [leftCoefficientMap, rightCoefficientMap, dualFunctor, dualMap, homMk,
        contravariantMap, leftMap, rightMap, baseMap]
      rfl
  · simp [leftCoefficientMap, rightCoefficientMap, dualFunctor, dualMap, homMk,
      contravariantMap, leftMap, rightMap, baseMap]
    rfl

end SerrePositivity.EInfinity.Hammock.TwoSidedGrothendieck
