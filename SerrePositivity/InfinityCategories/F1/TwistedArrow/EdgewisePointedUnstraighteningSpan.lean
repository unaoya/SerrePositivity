module

public import SerrePositivity.InfinityCategories.F1.TwistedArrow.EdgewiseWeightedConeSpan
public import SerrePositivity.InfinityCategories.F1.Transport.PointKanOpposite

/-!
概要：共通 Hom 解像の一点 cone から、直値と反転値の実際の unstraightening へ比較する。
方針：同じ全空間の二脚を標準 unstraightening に移し、反転した一点だけを厳密に正規化する。
規約：両脚は元の cone の後合成であり、底への射影を厳密に保つ。
使われ方：weighted nerve の自然な復元と反転 unstraightening の接続。
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

/-- Hom の共通解像の標準一点対象。 -/
def edgewisePointKanObject : EdgewiseEnrichedObject KanObject.{u} := ⟨pointKanObject, trivial⟩

variable {I : Type u} [SmallCategory I] (F : I ⥤ EdgewiseEnrichedObject KanObject.{u})

/-- 反転した一点を標準一点へ正規化し、同じ cone 全空間を標準 unstraightening にする。 -/
def edgewiseOppositePointConeUnstraighteningIso :
    coherentConeTotal
      (strictCoherentDiagram (F ⋙ coherentEnrichedUnderlyingFunctor edgewiseOppositeKanEnriched))
      (coherentNerveVertex (edgewiseOppositeKanEnriched.obj edgewisePointKanObject)) ≅
    leftUnstraightening
      (kanDiagramCoherentNerve
        (F ⋙ coherentEnrichedUnderlyingFunctor edgewiseOppositeKanEnriched)) :=
  eqToIso (congrArg (fun x => coherentConeTotal
    (strictCoherentDiagram (F ⋙ coherentEnrichedUnderlyingFunctor edgewiseOppositeKanEnriched))
      (coherentNerveVertex x)) kanObjectOpFunctor_point) ≪≫
    strictKanUnstraighteningIso (F ⋙ coherentEnrichedUnderlyingFunctor edgewiseOppositeKanEnriched)

/-- 一点の正規化を含む同型も、元の同じ底への射影を厳密に保つ。 -/
lemma edgewiseOppositePointConeUnstraighteningIso_projection :
    (edgewiseOppositePointConeUnstraighteningIso F).hom ≫
      leftUnstraighteningProjection
        (kanDiagramCoherentNerve
          (F ⋙ coherentEnrichedUnderlyingFunctor edgewiseOppositeKanEnriched)) =
    coherentConeProjection
      (strictCoherentDiagram (F ⋙ coherentEnrichedUnderlyingFunctor edgewiseOppositeKanEnriched))
      (coherentNerveVertex (edgewiseOppositeKanEnriched.obj edgewisePointKanObject)) := by
  rw [edgewiseOppositePointConeUnstraighteningIso, Iso.trans_hom, Category.assoc,
    strictKanUnstraighteningIso_projection]
  exact coherentConeTotal_transport_projection rfl
    (congrArg coherentNerveVertex kanObjectOpFunctor_point)
    (congrArg (fun x => coherentConeTotal
      (strictCoherentDiagram (F ⋙ coherentEnrichedUnderlyingFunctor edgewiseOppositeKanEnriched))
        (coherentNerveVertex x)) kanObjectOpFunctor_point)

/-- 同じ共通一点 cone の全空間から、直値側の実際の unstraightening への右脚。 -/
def edgewisePointedUnstraighteningRight :
    coherentConeTotal (strictCoherentDiagram F) (coherentNerveVertex edgewisePointKanObject) ⟶
    leftUnstraightening
      (kanDiagramCoherentNerve (F ⋙ coherentEnrichedUnderlyingFunctor
        (edgewiseEnrichedRight KanObject.{u}))) :=
  coherentConeTotalFunctorImage F (edgewiseEnrichedRight KanObject.{u}) edgewisePointKanObject ≫
    (strictKanUnstraighteningIso
      (F ⋙ coherentEnrichedUnderlyingFunctor (edgewiseEnrichedRight KanObject.{u}))).hom

/-- 同じ共通一点 cone の全空間から、反転値側の実際の unstraightening への左脚。 -/
def edgewisePointedUnstraighteningOpposite :
    coherentConeTotal (strictCoherentDiagram F) (coherentNerveVertex edgewisePointKanObject) ⟶
    leftUnstraightening
      (kanDiagramCoherentNerve
        (F ⋙ coherentEnrichedUnderlyingFunctor edgewiseOppositeKanEnriched)) :=
  coherentConeTotalFunctorImage F edgewiseOppositeKanEnriched edgewisePointKanObject ≫
    (edgewiseOppositePointConeUnstraighteningIso F).hom

/-- 直値側の右脚は同じ底の上の射。 -/
lemma edgewisePointedUnstraighteningRight_projection :
    edgewisePointedUnstraighteningRight F ≫ leftUnstraighteningProjection
      (kanDiagramCoherentNerve (F ⋙ coherentEnrichedUnderlyingFunctor
        (edgewiseEnrichedRight KanObject.{u}))) =
    coherentConeProjection (strictCoherentDiagram F)
      (coherentNerveVertex edgewisePointKanObject) := by
  rw [edgewisePointedUnstraighteningRight, Category.assoc,
    strictKanUnstraighteningIso_projection]
  exact coherentConeTotalFunctorImage_projection F (edgewiseEnrichedRight KanObject.{u})
    edgewisePointKanObject

/-- 反転値側の左脚も、同じ底の上の射。 -/
lemma edgewisePointedUnstraighteningOpposite_projection :
    edgewisePointedUnstraighteningOpposite F ≫ leftUnstraighteningProjection
      (kanDiagramCoherentNerve
        (F ⋙ coherentEnrichedUnderlyingFunctor edgewiseOppositeKanEnriched)) =
    coherentConeProjection (strictCoherentDiagram F)
      (coherentNerveVertex edgewisePointKanObject) := by
  rw [edgewisePointedUnstraighteningOpposite, Category.assoc,
    edgewiseOppositePointConeUnstraighteningIso_projection,
    coherentConeTotalFunctorImage_projection]

/-- 直値側への実際の右脚は、全空間の前合成同値。 -/
lemma edgewisePointedUnstraighteningRight_isPrecompositionEquivalence :
    IsPrecompositionEquivalence (edgewisePointedUnstraighteningRight F) :=
  (edgewiseCoherentConeRight_isPrecompositionEquivalence F edgewisePointKanObject).comp
    (isPrecompositionEquivalence_of_iso (strictKanUnstraighteningIso
      (F ⋙ coherentEnrichedUnderlyingFunctor (edgewiseEnrichedRight KanObject.{u}))))

/-- 反転値側への実際の左脚も、全空間の前合成同値。 -/
lemma edgewisePointedUnstraighteningOpposite_isPrecompositionEquivalence :
    IsPrecompositionEquivalence (edgewisePointedUnstraighteningOpposite F) :=
  (edgewiseCoherentConeOpposite_isPrecompositionEquivalence F edgewisePointKanObject).comp
    (isPrecompositionEquivalence_of_iso (edgewiseOppositePointConeUnstraighteningIso F))

end SerrePositivity.InfinityCategories
