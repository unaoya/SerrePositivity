module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.SectionsFunctor
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.PullbackSections
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

/-- 概要：指定された実際の引き戻し表示に沿って、元の切断空間の全族を制限する。
方針：元の評価を引き戻しへ持ち上げ、指定された同型の逆で戻す。
規約：fibration 性は不要。使われ方：G8 の大きい切断と小さい切断の共通の制限。 -/
def sectionsRestrictionOfIso {E E' B K : SSet.{u}}
    (p : E ⟶ B) (q : E' ⟶ K) (i : K ⟶ B)
    (e : E' ≅ pullback p i) (he : e.hom ≫ pullback.snd p i = q) :
    simplicialSections p ⟶ simplicialSections q := by
  let A := simplicialSections p
  let l := (i ▷ A) ≫ simplicialSectionsEvaluation p
  have hl : l ≫ p = fst K A ≫ i := by
    dsimp only [l]
    rw [Category.assoc, simplicialSectionsEvaluation_projection, whiskerRight_fst]
  let r := pullback.lift l (fst K A) hl
  have hr : (r ≫ e.inv) ≫ q = fst K A := by
    rw [← he, Category.assoc, Iso.inv_hom_id_assoc]
    exact pullback.lift_snd _ _ _
  exact simplicialSectionsLift (r ≫ e.inv) hr

/-- 概要：引き戻し表示を用いた切断制限を評価すると、元の評価の制限を回収する。
方針：切断の持ち上げを評価し、同型の逆と順射を相殺する。
規約：任意の全パラメータの厳密な等式。使われ方：G8 の切断制限の比較。 -/
lemma sectionsRestrictionOfIso_evaluation {E E' B K : SSet.{u}}
    (p : E ⟶ B) (q : E' ⟶ K) (i : K ⟶ B)
    (e : E' ≅ pullback p i) (he : e.hom ≫ pullback.snd p i = q) :
    (K ◁ sectionsRestrictionOfIso p q i e he) ≫ simplicialSectionsEvaluation q ≫
      e.hom ≫ pullback.fst p i =
      (i ▷ simplicialSections p) ≫ simplicialSectionsEvaluation p := by
  dsimp only [sectionsRestrictionOfIso]
  rw [← Category.assoc, ← Category.assoc, simplicialSectionsLift_evaluation]
  simp only [Category.assoc]
  rw [Iso.inv_hom_id_assoc, pullback.lift_fst]

/-- 概要：同じ引き戻し表示による切断空間は、元の射の相対関手空間と同型。
方針：底上の同型で切断を移し、既存の引き戻し切断の同型を使う。
規約：指定された表示を保持。使われ方：全族の制限の同型の反映。 -/
def sectionsRestrictionTargetIso {E E' B K : SSet.{u}}
    (p : E ⟶ B) (q : E' ⟶ K) (i : K ⟶ B)
    (e : E' ≅ pullback p i) (he : e.hom ≫ pullback.snd p i = q) :
    simplicialSections q ≅
      SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p i :=
  (simplicialSectionsFunctor K).mapIso (Over.isoMk (f := Over.mk q) (g := Over.mk (pullback.snd p i)) e he) ≪≫ pullbackSectionsRelativeIso p i

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
