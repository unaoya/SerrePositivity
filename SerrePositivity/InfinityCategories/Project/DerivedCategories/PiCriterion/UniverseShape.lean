module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.FilteredUniverse
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitReindex

/-!
概要：小さい底と大きい空間値を、底の ULift により同じ宇宙の公開 API へ移す。
方針：二重 ULift と一重 ULift の厳密な同型で図式を引き戻す。
規約：元の余錐の余極限性を保存・反映する。既存全空間構成の複製は不要。
使われ方：w = max (u+1) v における coherent π 判定。
-/

@[expose] public section
noncomputable section
universe u v
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion

/-- 底を値の宇宙へ上げた後の二重持ち上げを、元の一重持ち上げへ戻す。 -/
def liftedBaseShapeIso (B : SSet.{u}) :
    (SSet.uliftFunctor.{max u v + 1, max u v}).obj
      ((SSet.uliftFunctor.{v, u}).obj B) ≅
        (SSet.uliftFunctor.{max u v + 1, u}).obj B where
  hom :=
    { app _ := ↾fun x ↦ ULift.up x.down.down
      naturality {_ _} _ := rfl }
  inv :=
    { app _ := ↾fun x ↦ ULift.up (ULift.up x.down)
      naturality {_ _} _ := rfl }
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- 小さい底の大きい空間値図式を、持ち上げた底の同宇宙図式として読む。 -/
def liftedBaseDiagram {B : SSet.{u}}
    (F : (SSet.uliftFunctor.{max u v + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{max u v}) :
    (SSet.uliftFunctor.{max u v + 1, max u v}).obj
      ((SSet.uliftFunctor.{v, u}).obj B) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{max u v} :=
  (liftedBaseShapeIso.{u, v} B).hom ≫ F

/-- 底の宇宙を上げても、同じ元の余錐の余極限性を判定できる。 -/
lemma isColimitCone_iff_liftedBase_restrict {B : SSet.{u}}
    {F : (SSet.uliftFunctor.{max u v + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{max u v}}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (c.restrict (liftedBaseShapeIso.{u, v} B).hom) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_iff_restrict_of_isIso c _

end SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion
