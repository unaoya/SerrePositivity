module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LocalUnstraighteningStrictification
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.CartesianSectionsRestriction
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallLeftUnstraighteningBaseChange
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.SpaceSectionsObject

/-!
概要：小さい unstraightening の実切断を、同じ形状写像に沿って制限する。
方針：元の切断の評価を引き戻しへ持ち上げ、同じ基底変更同型で戻す。
規約：生の切断空間と持ち上げた切断空間を混同しない。
使われ方：G8 の指定極限と切断制限の全族比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces

/-- 概要：同じ小さい分類図式の切断を、指定形状写像に沿って実際に制限する。
方針：評価を引き戻した後、既存の小さい基底変更同型の逆へ続ける。
規約：任意の小さい形状。使われ方：G8 の切断制限の比較。 -/
def smallUnstraighteningSectionsRestriction {B K : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) (i : K ⟶ B) :
    simplicialSections (smallLeftUnstraighteningProjection F) ⟶
      simplicialSections (smallLeftUnstraighteningProjection
        ((SSet.uliftFunctor.{u + 1, u}).map i ≫ F)) :=
  sectionsRestrictionOfIso (smallLeftUnstraighteningProjection F)
    (smallLeftUnstraighteningProjection ((SSet.uliftFunctor.{u + 1, u}).map i ≫ F)) i
    (smallLeftUnstraighteningBaseChangeIso F i)
    (smallLeftUnstraighteningBaseChangeIso_hom_snd F i)

/-- 概要：元の評価を同じ基底変更の射影へ送ると、実際の切断制限の評価になる。
方針：切断の普遍性、同じ基底変更同型の相殺、引き戻しの第一射影を順に使う。
規約：全パラメータの厳密な等式。使われ方：G8 の正本の切断制限との照合。 -/
lemma smallUnstraighteningSectionsRestriction_evaluation {B K : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) (i : K ⟶ B) :
    (K ◁ smallUnstraighteningSectionsRestriction F i) ≫
      simplicialSectionsEvaluation (smallLeftUnstraighteningProjection
        ((SSet.uliftFunctor.{u + 1, u}).map i ≫ F)) ≫
      (smallLeftUnstraighteningBaseChangeIso F i).hom ≫
      pullback.fst (smallLeftUnstraighteningProjection F) i =
    (i ▷ simplicialSections (smallLeftUnstraighteningProjection F)) ≫
      simplicialSectionsEvaluation (smallLeftUnstraighteningProjection F) :=
  sectionsRestrictionOfIso_evaluation (smallLeftUnstraighteningProjection F)
    (smallLeftUnstraighteningProjection ((SSet.uliftFunctor.{u + 1, u}).map i ≫ F)) i
    (smallLeftUnstraighteningBaseChangeIso F i)
    (smallLeftUnstraighteningBaseChangeIso_hom_snd F i)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
