module
public import SerrePositivity.InfinityCategories.F1.KanModels.KanEnrichedJointPointHom
public import SerrePositivity.InfinityCategories.F1.Transport.FunctorIsoValueCurry
public import SerrePositivity.InfinityCategories.F1.KanModels.KanEnrichedDiagramOppositeComparison

/-! # 同じ共同比較の curry による実現同型を、元の対象へ制限する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
  {J : Type u} [Category.{u} J]

/-- 元の共同評価を curry すると、同じ実現写像を回収する。 -/
theorem kanEnrichedJointEvaluation_curry (D : KanEnrichedDiagram C J) :
    curry D.jointEvaluation = D.realization := by
  change curry (_ ◁ coherentNerveMap D.toEnrichedFunctor ≫ kanDiagramJointEvaluation J) = _
  rw [curry_natural_left]
  rfl

/-- 指定した元の対象への共同評価の制限は、その対象の図式全体を回収する。 -/
theorem kanEnrichedJointEvaluation_restrict (D : KanEnrichedDiagram C J) (X : C) :
    lift (𝟙 ((SSet.uliftFunctor.{u + 1, u}).obj (nerve J)))
        (SSet.const (coherentNerveVertex X)) ≫ D.jointEvaluation =
      kanDiagramCoherentNerve (D.evaluate X) := by
  apply functorVertex_injective
  rw [← curry_vertex_functorVertex, kanEnrichedJointEvaluation_curry]
  exact D.realization_vertex X

variable {D E : KanEnrichedDiagram C J} (η : KanEnrichedDiagramComparison D E)
  (hη : ∀ j (X : C), IsQCatEquivalence
    (X := ((D.obj j).obj X).obj) (Y := ((E.obj j).obj X).obj) ((η.component j).val X))

/-- 既存の実現同型は、同じ元の共同比較の curry の端点表示だけを変えたもの。 -/
theorem kanEnrichedRealizationIso_heq_curry :
    HEq (η.realizationIso hη) (η.jointComparisonIso hη).curry := by
  unfold KanEnrichedDiagramComparison.realizationIso
  dsimp only [_root_.id]
  have hcast {α β : Sort (u + 2)} (h : α = β) (x : α) : HEq (Eq.mp h x) x := by
    cases h
    rfl
  exact (hcast _ _).trans (hcast _ _)

/-- 元の対象で実現同型を評価し、同じ通常の二つの Kan 図式へ端点を揃える。 -/
def kanEnrichedRealizationValueIso (X : C) :
    FunctorIso (kanDiagramCoherentNerve (D.evaluate X))
      (kanDiagramCoherentNerve (E.evaluate X)) :=
  (eqToIso (congrArg HomotopyCategory.mk (D.realization_vertex X))).symm ≪≫
    functorIsoValue (η.realizationIso hη) (coherentNerveVertex X) ≪≫
      eqToIso (congrArg HomotopyCategory.mk (E.realization_vertex X))

/-- 同じ実現値同型は、元の共同比較を同じ対象に制限したものと HEq。 -/
theorem kanEnrichedRealizationValueIso_heq_precomp (X : C) :
    HEq (kanEnrichedRealizationValueIso η hη X)
      ((η.jointComparisonIso hη).precomp
        (lift (𝟙 ((SSet.uliftFunctor.{u + 1, u}).obj (nerve J)))
          (SSet.const (coherentNerveVertex X)))) := by
  have h₁ := F2.iso_endpoints_heq
    (functorIsoValue (η.realizationIso hη) (coherentNerveVertex X))
    (congrArg HomotopyCategory.mk (D.realization_vertex X))
    (congrArg HomotopyCategory.mk (E.realization_vertex X))
  have h₂ := functorIsoValue_heq_of_heq (η.realizationIso hη)
    (η.jointComparisonIso hη).curry (kanEnrichedJointEvaluation_curry D).symm
    (kanEnrichedJointEvaluation_curry E).symm (kanEnrichedRealizationIso_heq_curry η hη)
    (coherentNerveVertex X)
  exact h₁.trans (h₂.trans
    (functorIsoValue_curry_heq_precomp (η.jointComparisonIso hη) (coherentNerveVertex X)))

end SerrePositivity.KST.Fibration
