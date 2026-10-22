module
public import SerrePositivity.KST.Fibration.KanDiagramComponentPointHom
public import SerrePositivity.KST.Fibration.FunctorIsoValue
public import SerrePositivity.InfinityCategories.F1.KanEnrichedDiagramJointComparison

/-! # 豊穣図式の同じ共同比較の指定成分で、元の係数点を追跡する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
  {J : Type u} [Category.{u} J]

/-- 共同評価は元の指定対象と添字における同じ Kan 値を回収する。 -/
theorem kanEnrichedJointEvaluation_vertex (D : KanEnrichedDiagram C J) (X : C) (j : J) :
    (D.jointEvaluation).app (Opposite.op ⦋0⦌)
      (ULift.up (nerveVertex j), coherentNerveVertex X) =
        spaceInfinityVertex (((D.obj j).obj X)) := by
  change (kanDiagramJointEvaluation J).app (Opposite.op ⦋0⦌)
    (ULift.up (nerveVertex j), (coherentNerveMap D.toEnrichedFunctor).app
      (Opposite.op ⦋0⦌) (coherentNerveVertex X)) = _
  rw [coherentNerveMap_vertex]
  let F := D.toEnrichedFunctor.obj X
  have he := congrArg (fun m => m.app (Opposite.op ⦋0⦌) (coherentNerveVertex F))
    (curry_evaluateFunctorAt_vertex (kanDiagramJointEvaluation J) (ULift.up (nerveVertex j)))
  change (evaluateFunctorAt (ULift.up (nerveVertex j))).app (Opposite.op ⦋0⦌)
    ((kanDiagramRealization J).app (Opposite.op ⦋0⦌) (coherentNerveVertex F)) =
      (kanDiagramJointEvaluation J).app (Opposite.op ⦋0⦌)
        (ULift.up (nerveVertex j), coherentNerveVertex F) at he
  rw [kanDiagramRealization_vertex, evaluateFunctorAt_functorVertex] at he
  exact he.symm.trans (kanDiagramCoherentNerve_vertex F.val j)

variable {D E : KanEnrichedDiagram C J} (η : KanEnrichedDiagramComparison D E)
  (hη : ∀ j (X : C), IsQCatEquivalence
    (X := ((D.obj j).obj X).obj) (Y := ((E.obj j).obj X).obj) ((η.component j).val X))

/-- 同じ共同比較を元の二つの Kan 値の標準頂点で表示する指定成分。 -/
def kanEnrichedJointComponentIso (X : C) (j : J) :
    VertexIso (spaceInfinityVertex ((D.obj j).obj X))
      (spaceInfinityVertex ((E.obj j).obj X)) :=
  (eqToIso (congrArg HomotopyCategory.mk (kanEnrichedJointEvaluation_vertex D X j))).symm ≪≫
    functorIsoValue (η.jointComparisonIso hη) (ULift.up (nerveVertex j), coherentNerveVertex X) ≪≫
      eqToIso (congrArg HomotopyCategory.mk (kanEnrichedJointEvaluation_vertex E X j))

/-- 同じ共同比較の指定成分の順方向射は、元の係数射の coherent な辺の類。 -/
theorem kanEnrichedJointComponentIso_hom (X : C) (j : J) :
    (kanEnrichedJointComponentIso η hη X j).hom =
    Truncated.HomotopyCategory.homMk
      (((coherentNerveEdge ((η.component j).val X)).ofEq
        (spaceInfinityVertex_eq_coherent ((D.obj j).obj X)).symm
        (spaceInfinityVertex_eq_coherent ((E.obj j).obj X)).symm).toTruncated) := by
  simp only [kanEnrichedJointComponentIso, Iso.trans_hom, Iso.symm_hom, eqToIso.inv,
    eqToIso.hom, functorIsoValue_hom]
  rw [show (η.jointComparisonIso hη).hom = Truncated.HomotopyCategory.homMk
    (η.jointComparisonEdge).toTruncated from rfl, functorHomEvaluate_edge_hom]
  exact homMk_transport (kanEnrichedJointEvaluation_vertex D X j)
    (kanEnrichedJointEvaluation_vertex E X j) _ _ (η.jointComparisonEdge_at j X)

/-- 元の係数点は、同じ共同比較の指定成分で元の像の点へ移る。 -/
theorem kanEnrichedJointComponentIso_pointHom (X : C) (j : J)
    (v : ((D.obj j).obj X).obj _⦋0⦌) :
    cosliceFiberPointHom ((pointedSpaceFiberVertexEquiv ((D.obj j).obj X)).symm v) ≫
      (kanEnrichedJointComponentIso η hη X j).hom =
    cosliceFiberPointHom ((pointedSpaceFiberVertexEquiv ((E.obj j).obj X)).symm
      (((η.component j).val X).app (Opposite.op ⦋0⦌) v)) := by
  rw [kanEnrichedJointComponentIso_hom]
  exact kanPointHom_comp_of_edge ((η.component j).val X) _ rfl v

end SerrePositivity.KST.Fibration
