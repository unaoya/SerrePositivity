module
public import SerrePositivity.KST.Fibration.FunctorIsoDoubleEvaluation
public import SerrePositivity.KST.Fibration.KanEnrichedRealizationPointHom

/-! # 豊穣実現の同じ指定成分を、一つの二重評価写像による像に戻す -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
  {J : Type u} [Category.{u} J]

/-- 同じ対象と添字による、全実現関手空間上の固定した二重評価写像。 -/
def kanEnrichedDoubleEvaluation (X : C) (j : J) :
    (ihom (SimplicialNerve C)).obj
      (SpaceInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve J))) ⟶
        SpaceInfinity.{u} :=
  doubleFunctorEvaluation (K := SimplicialNerve C)
    (A := (SSet.uliftFunctor.{u + 1, u}).obj (nerve J)) (Y := SpaceInfinity.{u})
    (coherentNerveVertex X) (ULift.up (nerveVertex j))

/-- 同じ二重評価は元の対象・添字での Kan 値を回収する。 -/
theorem kanEnrichedDoubleEvaluation_vertex (D : KanEnrichedDiagram C J) (X : C) (j : J) :
    (kanEnrichedDoubleEvaluation X j).app (Opposite.op ⦋0⦌) (functorVertex D.realization) =
      spaceInfinityVertex ((D.obj j).obj X) := by
  let a : ((SSet.uliftFunctor.{u + 1, u}).obj (nerve J)) _⦋0⦌ := ULift.up (nerveVertex j)
  have h := doubleFunctorEvaluation_vertex (A := (SSet.uliftFunctor.{u + 1, u}).obj (nerve J))
    (Y := SpaceInfinity.{u}) D.realization (coherentNerveVertex X) a
  have hv : (evaluateFunctorAt (Y := SpaceInfinity.{u}) a).app (Opposite.op ⦋0⦌)
      (D.realization.app (Opposite.op ⦋0⦌) (coherentNerveVertex X)) =
        spaceInfinityVertex ((D.obj j).obj X) := by
    rw [D.realization_vertex, evaluateFunctorAt_functorVertex, kanDiagramCoherentNerve_vertex]
    rfl
  exact h.trans hv

/-- 同じ二重評価を前合成した実現に適用すると、元の像の対象の Kan 値を回収する。 -/
theorem kanEnrichedDoubleEvaluation_precomp_vertex
    {L : Type (u + 1)} [Category.{u} L] [SimplicialCategory L]
    (D : KanEnrichedDiagram C J) (H : EnrichedFunctor SSet.{u} L C) (X : L) (j : J) :
    (kanEnrichedDoubleEvaluation X j).app (Opposite.op ⦋0⦌)
      (functorVertex (coherentNerveMap H ≫ D.realization)) =
        spaceInfinityVertex ((D.obj j).obj (H.obj X)) := by
  let a : ((SSet.uliftFunctor.{u + 1, u}).obj (nerve J)) _⦋0⦌ := ULift.up (nerveVertex j)
  have h := doubleFunctorEvaluation_vertex (A := (SSet.uliftFunctor.{u + 1, u}).obj (nerve J))
    (Y := SpaceInfinity.{u}) (coherentNerveMap H ≫ D.realization) (coherentNerveVertex X) a
  have hv : (evaluateFunctorAt (Y := SpaceInfinity.{u}) a).app (Opposite.op ⦋0⦌)
      ((coherentNerveMap H ≫ D.realization).app (Opposite.op ⦋0⦌) (coherentNerveVertex X)) =
        spaceInfinityVertex ((D.obj j).obj (H.obj X)) := by
    change (evaluateFunctorAt (Y := SpaceInfinity.{u}) a).app (Opposite.op ⦋0⦌)
      (D.realization.app (Opposite.op ⦋0⦌)
        ((coherentNerveMap H).app (Opposite.op ⦋0⦌) (coherentNerveVertex X))) = _
    rw [coherentNerveMap_vertex, D.realization_vertex, evaluateFunctorAt_functorVertex,
      kanDiagramCoherentNerve_vertex]
    rfl
  exact h.trans hv

variable {D E : KanEnrichedDiagram C J} (η : KanEnrichedDiagramComparison D E)
  (hη : ∀ j (X : C), IsQCatEquivalence
    (X := ((D.obj j).obj X).obj) (Y := ((E.obj j).obj X).obj) ((η.component j).val X))

/-- 同じ実現の指定成分は、同じ二重評価による元の指定実現同型の像と HEq。 -/
theorem kanEnrichedRealizationComponentIso_heq_doubleMap (X : C) (j : J) :
    HEq (kanEnrichedRealizationComponentIso η hη X j)
      (VertexIso.map (η.realizationIso hη) (kanEnrichedDoubleEvaluation X j)) := by
  let R := kanEnrichedRealizationValueIso η hη X
  let e := η.realizationIso hη
  let a := ULift.up.{u + 1} (nerveVertex j)
  let x := coherentNerveVertex X
  have h₁ : HEq (kanEnrichedRealizationComponentIso η hη X j) (functorIsoValue R a) :=
    F2.iso_endpoints_heq _
      (congrArg HomotopyCategory.mk (kanDiagramCoherentNerve_vertex (D.evaluate X) j))
      (congrArg HomotopyCategory.mk (kanDiagramCoherentNerve_vertex (E.evaluate X) j))
  have hr : HEq R (functorIsoValue e x) := F2.iso_endpoints_heq _
    (congrArg HomotopyCategory.mk (D.realization_vertex X))
    (congrArg HomotopyCategory.mk (E.realization_vertex X))
  have h₂ := F2.vertexIso_map_heq_of_heq R (functorIsoValue e x)
    (D.realization_vertex X).symm (E.realization_vertex X).symm hr (evaluateFunctorAt a)
  exact h₁.trans ((functorIsoValue_heq_map R a).trans
    (h₂.trans (functorIsoDoubleValue_heq_map e x a)))

end SerrePositivity.KST.Fibration
