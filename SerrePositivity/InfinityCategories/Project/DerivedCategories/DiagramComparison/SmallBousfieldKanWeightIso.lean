module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.SmallOverLift
public import Mathlib.CategoryTheory.Types.Basic
/-!
概要：元のsmallBousfieldKanWeightDown自身の逆を持ち上げで与える。
方針：同じover列を元のupで持ち上げ、全次数で両合成を確認する。
規約：IS-W2 A12のAsSmall・ULift照合の証明分割。順射は変更しない。
使われ方：HA 1.2.4、反転BK比較を係数環の宇宙へ移す指定同型。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (J : Type) [SmallCategory J]
/-- 元の指定されたBK持ち下げは全成分で可逆。 -/
instance smallBousfieldKanWeightDown_isIso : IsIso (smallBousfieldKanWeightDown.{u} J) := by
  haveI (j : AsSmall.{u} J) : IsIso ((smallBousfieldKanWeightDown.{u} J).app j) := by
    haveI (n : SimplexCategoryᵒᵖ) : IsIso (((smallBousfieldKanWeightDown.{u} J).app j).app n) := by
      let e : ((bousfieldKanWeight (AsSmall.{u} J)).obj j).obj n ≃
          (((AsSmall.down : AsSmall.{u} J ⥤ J) ⋙ bousfieldKanWeight J ⋙
            SSet.uliftFunctor.{u,0}).obj j).obj n := {
        toFun s := ULift.up (s ⋙ Over.post (AsSmall.down : AsSmall.{u} J ⥤ J))
        invFun s := s.down ⋙ smallOverLift j
        left_inv s := by
          change (s ⋙ Over.post (AsSmall.down : AsSmall.{u} J ⥤ J)) ⋙ smallOverLift j = s
          erw [Functor.assoc, smallOverDown_lift, Functor.comp_id]
        right_inv s := by
          apply ULift.ext
          change (s.down ⋙ smallOverLift j) ⋙ Over.post (AsSmall.down : AsSmall.{u} J ⥤ J) = s.down
          erw [Functor.assoc, smallOverLift_down, Functor.comp_id] }
      apply (isIso_iff_bijective _).mpr
      exact e.bijective
    exact NatIso.isIso_of_isIso_app _
  exact NatIso.isIso_of_isIso_app _
/-- 既存の指定持ち下げを順射とする同じBK重みの同型。 -/
def smallBousfieldKanWeightIso :
    bousfieldKanWeight (AsSmall.{u} J) ≅
      (AsSmall.down : AsSmall.{u} J ⥤ J) ⋙ bousfieldKanWeight J ⋙ SSet.uliftFunctor.{u,0} :=
  asIso (smallBousfieldKanWeightDown J)
/-- 同型の順射は既存の持ち下げそのもの。 -/
theorem smallBousfieldKanWeightIso_hom :
    (smallBousfieldKanWeightIso.{u} J).hom = smallBousfieldKanWeightDown J := rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
