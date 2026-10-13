module

public import SerrePositivity.Spectra.SymmetricSequence.SumCoherence

/-!
# 全単射の有限集合圏の直和による対称モノイダル構造

直和の二変数関手と構造同型を型クラスへ登録する。
既存の convolution に使った直和関手と、登録したテンソル関手は同じ。
-/

@[expose] public section

namespace SerrePositivity.FiniteBijection

open CategoryTheory CategoryTheory.MonoidalCategory

instance sumMonoidalCategoryStruct : MonoidalCategoryStruct FiniteBijection where
  tensorObj := sumObj
  tensorHom := sumMap
  whiskerLeft X _ _ f := sumMap (𝟙 X) f
  whiskerRight f Y := sumMap f (𝟙 Y)
  tensorUnit := of 0
  associator := sumAssociator
  leftUnitor := sumLeftUnitor
  rightUnitor := sumRightUnitor

instance sumMonoidalCategory : MonoidalCategory FiniteBijection :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := sumMap_id)
    (id_tensorHom := by intros; rfl)
    (tensorHom_id := by intros; rfl)
    (tensorHom_comp_tensorHom := fun f g f' g' ↦ sumMap_comp f g f' g')
    (associator_naturality := fun f g h ↦ sumAssociator_naturality f g h)
    (leftUnitor_naturality := fun f ↦ sumLeftUnitor_naturality f)
    (rightUnitor_naturality := fun f ↦ sumRightUnitor_naturality f)
    (pentagon := sumAssociator_pentagon)
    (triangle := sumAssociator_triangle)

instance sumSymmetricCategory : SymmetricCategory FiniteBijection where
  braiding := sumSymmetry
  braiding_naturality_right := by
    intro X Y Z f
    exact sumSymmetry_naturality (𝟙 X) f
  braiding_naturality_left := by
    intro X Y f Z
    exact sumSymmetry_naturality f (𝟙 Z)
  hexagon_forward := sumAssociator_hexagon_forward
  hexagon_reverse := sumAssociator_hexagon_reverse
  symmetry := sumSymmetry_comp

/-- 登録したテンソル関手は既存の直和関手と定義上同じ。 -/
lemma tensor_eq_sumFunctor : tensor FiniteBijection = sumFunctor := rfl

/-- 添字圏のテンソル積は直和の対象。 -/
lemma tensorObj_eq_sumObj (A B : FiniteBijection) : A ⊗ B = sumObj A B := rfl

lemma whiskerRight_eq_sumMap {A A' : FiniteBijection} (f : A ⟶ A') (B : FiniteBijection) :
    f ▷ B = sumMap f (𝟙 B) := rfl
lemma whiskerLeft_eq_sumMap (B : FiniteBijection) {A A' : FiniteBijection} (f : A ⟶ A') :
    B ◁ f = sumMap (𝟙 B) f := rfl

end SerrePositivity.FiniteBijection
