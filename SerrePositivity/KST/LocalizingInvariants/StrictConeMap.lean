module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictCones

/-!
概要：図式が異なる二つの通常の錐の比較を、始対象を加えた全関手の自然変換にする。
方針：始点では頂点射、元の図式上では指定自然変換を使い、混合射で錐の可換式を使う。
規約：同じ底図式には制限しない。使われ方：BF fiber 比較の実 cube の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits

namespace SerrePositivity.KST.LocalizingInvariants.StrictConeMap

variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C]
  {F G : I ⥤ C} (η : F ⟶ G) (c : Cone F) (d : Cone G) (m : c.pt ⟶ d.pt)
  (hm : ∀ i, c.π.app i ≫ η.app i = m ≫ d.π.app i)

def transformation : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictConeFunctor c ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictConeFunctor d where
  app x := match x with
    | WithInitial.of i => η.app (AsSmall.down.obj i)
    | WithInitial.star => m
  naturality i j g := by
    cases i with
    | of i =>
      cases j with
      | of j => exact η.naturality (AsSmall.down.map (WithInitial.down g))
      | star => exact (WithInitial.false_of_to_star g).elim
    | star =>
      cases j with
      | of j => exact hm (AsSmall.down.obj j)
      | star => exact (Category.id_comp m).trans (Category.comp_id m).symm

lemma transformation_star : (transformation η c d m hm).app WithInitial.star = m := rfl

lemma transformation_of (i : AsSmall.{v} I) :
    (transformation η c d m hm).app (WithInitial.of i) = η.app (AsSmall.down.obj i) := rfl

end SerrePositivity.KST.LocalizingInvariants.StrictConeMap
