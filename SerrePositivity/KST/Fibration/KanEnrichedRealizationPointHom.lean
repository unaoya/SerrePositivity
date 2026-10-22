module
public import SerrePositivity.KST.Fibration.KanEnrichedRealizationValue

/-! # 同じ豊穣実現同型の指定成分は、元の共同比較の係数点の作用を保持する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
  {J : Type u} [Category.{u} J] {D E : KanEnrichedDiagram C J}
  (η : KanEnrichedDiagramComparison D E)
  (hη : ∀ j (X : C), IsQCatEquivalence
    (X := ((D.obj j).obj X).obj) (Y := ((E.obj j).obj X).obj) ((η.component j).val X))

/-- 同じ実現値同型の指定添字での成分を、元の Kan 値で表示する。 -/
def kanEnrichedRealizationComponentIso (X : C) (j : J) :
    VertexIso (spaceInfinityVertex ((D.obj j).obj X))
      (spaceInfinityVertex ((E.obj j).obj X)) :=
  (eqToIso (congrArg HomotopyCategory.mk
    (kanDiagramCoherentNerve_vertex (D.evaluate X) j))).symm ≪≫
      functorIsoValue (kanEnrichedRealizationValueIso η hη X) (ULift.up (nerveVertex j)) ≪≫
        eqToIso (congrArg HomotopyCategory.mk (kanDiagramCoherentNerve_vertex (E.evaluate X) j))

/-- 同じ実現同型の二段階評価は、元の共同比較の同じ指定成分と厳密に一致。 -/
theorem kanEnrichedRealizationComponentIso_eq_joint (X : C) (j : J) :
    kanEnrichedRealizationComponentIso η hη X j =
      kanEnrichedJointComponentIso η hη X j := by
  let q : (SSet.uliftFunctor.{u + 1, u}).obj (nerve J) ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj (nerve J) ⊗ SimplicialNerve C :=
    lift (𝟙 _) (SSet.const (coherentNerveVertex X))
  let z := ULift.up.{u + 1} (nerveVertex j)
  let R := kanEnrichedRealizationValueIso η hη X
  let P := (η.jointComparisonIso hη).precomp q
  have h₁ : HEq (kanEnrichedRealizationComponentIso η hη X j) (functorIsoValue R z) :=
    F2.iso_endpoints_heq _
      (congrArg HomotopyCategory.mk (kanDiagramCoherentNerve_vertex (D.evaluate X) j))
      (congrArg HomotopyCategory.mk (kanDiagramCoherentNerve_vertex (E.evaluate X) j))
  have h₂ := functorIsoValue_heq_of_heq R P
    (kanEnrichedJointEvaluation_restrict D X).symm
    (kanEnrichedJointEvaluation_restrict E X).symm
    (kanEnrichedRealizationValueIso_heq_precomp η hη X) z
  have h₃ := functorIsoValue_precomp (η.jointComparisonIso hη) q z
  have hz : q.app (Opposite.op ⦋0⦌) z = (z, coherentNerveVertex X) := by
    change (z, PinchedHom.constant (coherentNerveVertex X) 0) = (z, coherentNerveVertex X)
    rw [pinchedConstant_zero]
  have h₄ := functorIsoValue_point_heq (η.jointComparisonIso hη) hz
  have h₅ : HEq (kanEnrichedJointComponentIso η hη X j)
      (functorIsoValue (η.jointComparisonIso hη) (z, coherentNerveVertex X)) :=
    F2.iso_endpoints_heq _
      (congrArg HomotopyCategory.mk (kanEnrichedJointEvaluation_vertex D X j))
      (congrArg HomotopyCategory.mk (kanEnrichedJointEvaluation_vertex E X j))
  exact eq_of_heq (h₁.trans (h₂.trans ((heq_of_eq h₃).trans (h₄.trans h₅.symm))))

/-- 同じ実現同型の元の指定成分は、元の係数点をその元の像へ送る。 -/
theorem kanEnrichedRealizationComponentIso_pointHom (X : C) (j : J)
    (v : ((D.obj j).obj X).obj _⦋0⦌) :
    cosliceFiberPointHom ((pointedSpaceFiberVertexEquiv ((D.obj j).obj X)).symm v) ≫
      (kanEnrichedRealizationComponentIso η hη X j).hom =
    cosliceFiberPointHom ((pointedSpaceFiberVertexEquiv ((E.obj j).obj X)).symm
      (((η.component j).val X).app (Opposite.op ⦋0⦌) v)) := by
  rw [kanEnrichedRealizationComponentIso_eq_joint]
  exact kanEnrichedJointComponentIso_pointHom η hη X j v

end SerrePositivity.KST.Fibration
