module

public import SerrePositivity.InfinityCategories.F1.EdgewisePointedUnstraighteningSpan
public import SerrePositivity.InfinityCategories.F1.EdgewiseOrdinaryKanImage

/-!
概要：元の strict Kan 図式と元の反転図式の unstraightening を、一つの共通全空間で比較する。
方針：定値な通常の Hom の標準持ち上げに同じ二脚を制限し、図式の厳密な等式で戻す。
規約：元の図式の射を変更せず、各脚の底上の性質と同値性を保持する。
使われ方：元の oppositeKanUnstraighteningComparison と共通 Hom 解像の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
open HomotopyLimits

variable {I : Type u} [SmallCategory I] (F : I ⥤ KanObject.{u})

/-- 元の strict Kan 図式を、同じ通常の射を定値にした共通 Hom 解像へ入れる。 -/
def strictKanCommonDiagram : I ⥤ EdgewiseEnrichedObject KanObject.{u} :=
  F ⋙ edgewiseOrdinaryLift KanObject.{u}

/-- 標準持ち上げの右側は元の strict Kan 図式そのもの。 -/
lemma strictKanCommonDiagram_right :
    strictKanCommonDiagram F ⋙ coherentEnrichedUnderlyingFunctor
      (edgewiseEnrichedRight KanObject.{u}) = F := by
  rw [strictKanCommonDiagram, Functor.assoc, edgewiseOrdinaryLift_right, Functor.comp_id]

/-- 標準持ち上げの左側は元の strict Kan 図式の値の反転そのもの。 -/
lemma strictKanCommonDiagram_opposite :
    strictKanCommonDiagram F ⋙ coherentEnrichedUnderlyingFunctor edgewiseOppositeKanEnriched =
      F ⋙ kanObjectOpFunctor := by
  rw [strictKanCommonDiagram, Functor.assoc, edgewiseOrdinaryLift_opposite]

private lemma unstraightening_eqToHom_projection {B : SSet.{u + 1}}
    {G H : B ⟶ SpaceInfinity.{u}} (h : G = H) :
    eqToHom (congrArg leftUnstraightening h) ≫ leftUnstraighteningProjection H =
      leftUnstraighteningProjection G := by
  subst H
  rw [eqToHom_refl, Category.id_comp]

/-- 共通全空間から、元の strict 図式の実際の unstraightening への右脚。 -/
def strictKanCommonUnstraighteningRight :
    coherentConeTotal (strictCoherentDiagram (strictKanCommonDiagram F))
      (coherentNerveVertex edgewisePointKanObject) ⟶
    leftUnstraightening (kanDiagramCoherentNerve F) :=
  edgewisePointedUnstraighteningRight (strictKanCommonDiagram F) ≫
    eqToHom (congrArg leftUnstraightening
      (congrArg kanDiagramCoherentNerve (strictKanCommonDiagram_right F)))

/-- 同じ共通全空間から、元の strict 図式の反転の実際の unstraightening への左脚。 -/
def strictKanCommonUnstraighteningOpposite :
    coherentConeTotal (strictCoherentDiagram (strictKanCommonDiagram F))
      (coherentNerveVertex edgewisePointKanObject) ⟶
    leftUnstraightening (kanDiagramCoherentNerve (F ⋙ kanObjectOpFunctor)) :=
  edgewisePointedUnstraighteningOpposite (strictKanCommonDiagram F) ≫
    eqToHom (congrArg leftUnstraightening
      (congrArg kanDiagramCoherentNerve (strictKanCommonDiagram_opposite F)))

/-- 元の図式への右脚は、同じ持ち上げた nerve の底を厳密に保つ。 -/
lemma strictKanCommonUnstraighteningRight_projection :
    strictKanCommonUnstraighteningRight F ≫
      leftUnstraighteningProjection (kanDiagramCoherentNerve F) =
    coherentConeProjection (strictCoherentDiagram (strictKanCommonDiagram F))
      (coherentNerveVertex edgewisePointKanObject) := by
  rw [strictKanCommonUnstraighteningRight, Category.assoc,
    unstraightening_eqToHom_projection
      (congrArg kanDiagramCoherentNerve (strictKanCommonDiagram_right F))]
  exact edgewisePointedUnstraighteningRight_projection (strictKanCommonDiagram F)

/-- 元の反転図式への左脚も、同じ持ち上げた nerve の底を厳密に保つ。 -/
lemma strictKanCommonUnstraighteningOpposite_projection :
    strictKanCommonUnstraighteningOpposite F ≫
      leftUnstraighteningProjection (kanDiagramCoherentNerve (F ⋙ kanObjectOpFunctor)) =
    coherentConeProjection (strictCoherentDiagram (strictKanCommonDiagram F))
      (coherentNerveVertex edgewisePointKanObject) := by
  rw [strictKanCommonUnstraighteningOpposite, Category.assoc,
    unstraightening_eqToHom_projection
      (congrArg kanDiagramCoherentNerve (strictKanCommonDiagram_opposite F))]
  exact edgewisePointedUnstraighteningOpposite_projection (strictKanCommonDiagram F)

/-- 元の strict 図式の unstraightening への実際の右脚は前合成同値。 -/
lemma strictKanCommonUnstraighteningRight_isPrecompositionEquivalence :
    IsPrecompositionEquivalence (strictKanCommonUnstraighteningRight F) :=
  (edgewisePointedUnstraighteningRight_isPrecompositionEquivalence (strictKanCommonDiagram F)).comp
    (isPrecompositionEquivalence_of_iso (eqToIso (congrArg leftUnstraightening
      (congrArg kanDiagramCoherentNerve (strictKanCommonDiagram_right F)))))

/-- 元の strict 反転図式の unstraightening への実際の左脚も前合成同値。 -/
lemma strictKanCommonUnstraighteningOpposite_isPrecompositionEquivalence :
    IsPrecompositionEquivalence (strictKanCommonUnstraighteningOpposite F) :=
  IsPrecompositionEquivalence.comp
    (edgewisePointedUnstraighteningOpposite_isPrecompositionEquivalence (strictKanCommonDiagram F))
    (isPrecompositionEquivalence_of_iso (eqToIso (congrArg leftUnstraightening
      (congrArg kanDiagramCoherentNerve (strictKanCommonDiagram_opposite F)))))

end SerrePositivity.InfinityCategories
