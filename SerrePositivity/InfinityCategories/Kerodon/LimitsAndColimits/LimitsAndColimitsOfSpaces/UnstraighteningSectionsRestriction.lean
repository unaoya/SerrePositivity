module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftUnstraighteningBaseChange
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.CartesianSectionsRestriction

/-!
概要：元の大きい unstraightening の切断を、指定形状へ実際に制限する。
方針：既存の引き戻し同型と、切断の評価による制限を合成する。
規約：選んだ極限の普遍射で代用せず、元の射影と切断を使う。
使われ方：小さい切断表示との比較、および元の錐の全 fiber の自然性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces

/-- 元の図式の全切断を、指定形状の引き戻しに制限する実際の射。 -/
def unstraighteningSectionsRestriction {B K : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) (i : K ⟶ B) :
    simplicialSections (leftUnstraighteningProjection F) ⟶
      simplicialSections (leftUnstraighteningProjection (i ≫ F)) :=
  sectionsRestrictionOfIso (leftUnstraighteningProjection F)
    (leftUnstraighteningProjection (i ≫ F)) i (leftUnstraighteningBaseChangeIso F i)
    (leftUnstraighteningBaseChangeIso_hom_snd F i)

/-- 制限した切断の評価は、元の全評価を形状に沿って引き戻したもの。 -/
lemma unstraighteningSectionsRestriction_evaluation {B K : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) (i : K ⟶ B) :
    (K ◁ unstraighteningSectionsRestriction F i) ≫
      simplicialSectionsEvaluation (leftUnstraighteningProjection (i ≫ F)) ≫
      leftUnstraighteningMap (i ≫ F) F i rfl =
    (i ▷ simplicialSections (leftUnstraighteningProjection F)) ≫
      simplicialSectionsEvaluation (leftUnstraighteningProjection F) := by
  rw [← leftUnstraighteningBaseChangeIso_hom_fst]
  exact sectionsRestrictionOfIso_evaluation (leftUnstraighteningProjection F)
    (leftUnstraighteningProjection (i ≫ F)) i (leftUnstraighteningBaseChangeIso F i)
    (leftUnstraighteningBaseChangeIso_hom_snd F i)

/-- 制限後の切断を元の相対関手空間へ送る、同じ引き戻し表示の同型。 -/
def unstraighteningSectionsRestrictionTargetIso {B K : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) (i : K ⟶ B) :
    simplicialSections (leftUnstraighteningProjection (i ≫ F)) ≅
      SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace
        (leftUnstraighteningProjection F) i :=
  sectionsRestrictionTargetIso (leftUnstraighteningProjection F)
    (leftUnstraighteningProjection (i ≫ F)) i (leftUnstraighteningBaseChangeIso F i)
    (leftUnstraighteningBaseChangeIso_hom_snd F i)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
