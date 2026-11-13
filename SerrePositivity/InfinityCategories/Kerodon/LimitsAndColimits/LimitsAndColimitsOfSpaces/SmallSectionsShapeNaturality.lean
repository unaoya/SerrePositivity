module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.SmallSectionsComparisonEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.SmallUnstraighteningSectionsRestriction
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.UnstraighteningSectionsRestriction

/-!
概要：元の大小の切断比較は、実際の形状制限と厳密に自然。
方針：引き戻しの二射影で比較し、全空間の縮小同型の既存の自然性を使う。
規約：指定極限の選択は用いず、元の切断制限だけを比較する。
使われ方：元の錐の値の切断写像と小さい切断制限の接続。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces

/-- 小さい実切断制限の評価は、小さい全空間の元の底変換射と可換。 -/
lemma smallUnstraighteningSectionsRestriction_map_evaluation {B K : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) (i : K ⟶ B) :
    (K ◁ smallUnstraighteningSectionsRestriction F i) ≫
      simplicialSectionsEvaluation (smallLeftUnstraighteningProjection
        ((SSet.uliftFunctor.{u + 1, u}).map i ≫ F)) ≫
      smallLeftUnstraighteningMap ((SSet.uliftFunctor.{u + 1, u}).map i ≫ F) F i rfl =
      (i ▷ simplicialSections (smallLeftUnstraighteningProjection F)) ≫
        simplicialSectionsEvaluation (smallLeftUnstraighteningProjection F) := by
  have he : (smallLeftUnstraighteningBaseChangeIso F i).hom ≫
      pullback.fst (smallLeftUnstraighteningProjection F) i =
      smallLeftUnstraighteningMap ((SSet.uliftFunctor.{u + 1, u}).map i ≫ F) F i rfl :=
    IsPullback.isoPullback_hom_fst _
  rw [← he]
  exact smallUnstraighteningSectionsRestriction_evaluation F i

/-- 元の大小の切断同型は、同じ形状の実切断制限と厳密に可換。 -/
lemma smallUnstraighteningSectionsIso_shape {B K : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) (i : K ⟶ B) :
    (SSet.uliftFunctor.{u + 1, u}).map (smallUnstraighteningSectionsRestriction F i) ≫
      (smallUnstraighteningSectionsIso ((SSet.uliftFunctor.{u + 1, u}).map i ≫ F)).hom =
    (smallUnstraighteningSectionsIso F).hom ≫
      unstraighteningSectionsRestriction F ((SSet.uliftFunctor.{u + 1, u}).map i) := by
  let U := SSet.uliftFunctor.{u + 1, u}
  let G := U.map i ≫ F
  let A := simplicialSections (smallLeftUnstraighteningProjection F)
  apply simplicialSections_hom_ext
  apply (cancel_mono (leftUnstraighteningBaseChangeIso F (U.map i)).hom).mp
  apply pullback.hom_ext
  · simp only [Category.assoc, leftUnstraighteningBaseChangeIso_hom_fst,
      whiskerLeft_comp]
    erw [← Category.assoc (U.obj K ◁ (smallUnstraighteningSectionsIso G).hom)]
    erw [smallUnstraighteningSectionsIso_evaluation G]
    erw [unstraighteningSectionsRestriction_evaluation F (U.map i)]
    erw [← Category.assoc (U.obj K ◁ (smallUnstraighteningSectionsIso F).hom),
      whisker_exchange]
    simp only [Category.assoc]
    erw [smallUnstraighteningSectionsIso_evaluation F]
    erw [← smallLeftUnstraighteningMap_naturality G F i rfl]
    simp only [← Category.assoc]
    erw [uliftTensorIso_inv_whiskerLeft]
    simp only [Category.assoc, ← CategoryTheory.Functor.map_comp]
    erw [smallUnstraighteningSectionsRestriction_map_evaluation]
    have hi : (U.map i ▷ U.obj A) ≫ (uliftTensorIso B A).inv =
        (uliftTensorIso K A).inv ≫ U.map (i ▷ A) := rfl
    simp only [Category.assoc, CategoryTheory.Functor.map_comp]
    erw [← Category.assoc (U.map i ▷ U.obj A), hi]
    simp only [Category.assoc]
    rfl
  · simp only [Category.assoc, leftUnstraighteningBaseChangeIso_hom_snd]
    erw [simplicialSectionsEvaluation_projection]
    erw [whiskerLeft_fst] <;> rfl

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
