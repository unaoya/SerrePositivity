module
public import SerrePositivity.KST.Fibration.FractionClassificationSimplexRestriction

/-! # 指定分類成分を元の strict Kan 値で読むと、同じ section 比較の実成分を回収する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {X Q : SSet.{u}} [Quasicategory X] [Quasicategory Q]
  (F : X ⟶ Q) (x : X _⦋0⦌) (c : TransportSimplexCategory X)

/-- 指定した native Kan 値から実分類図式の同じ初頂点値への元の同型。 -/
def fractionKanSimplexClassificationValueIso :
    VertexIso (spaceInfinityVertex ((fractionSimplexKanMappingDiagram F x).obj c))
      ((leftStraighteningInfinityDiagram
        (sliceUnderProjection (yonedaEquiv.symm (F.app (Opposite.op ⦋0⦌) x)))).app
          (Opposite.op ⦋0⦌) (ULift.up (F.app (Opposite.op ⦋0⦌)
            ((transportSimplexFirstVertexMap X).app (Opposite.op ⦋0⦌) (nerveVertex c))))) :=
  (eqToIso (congrArg HomotopyCategory.mk
    (kanDiagramCoherentNerve_vertex (fractionSimplexKanMappingDiagram F x) c))).symm ≪≫
      (fractionKanSimplexClassificationIso F x).app (ULift.up (nerveVertex c))

/-- 底上の同じ分類成分を、元の指定値同型で戻すと同じ native 分類成分になる。 -/
theorem fractionKanSpaceDiagram_classificationIso_native_component :
    (fractionKanSpaceDiagram_initialVertexIso F x c).inv ≫
      functorHomEvaluate (fractionKanSpaceDiagram_classificationIso F x).hom
        (ULift.up ((transportSimplexFirstVertexMap X).app (Opposite.op ⦋0⦌) (nerveVertex c))) =
      (fractionKanSimplexClassificationValueIso F x c).hom := by
  let k := (SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap X)
  let S := fractionKanSpaceDiagram F x
  let T := kanDiagramCoherentNerve (fractionSimplexKanMappingDiagram F x)
  let G := (SSet.uliftFunctor.{u + 1, u}).map F ≫ leftStraighteningInfinityDiagram
    (sliceUnderProjection (yonedaEquiv.symm (F.app (Opposite.op ⦋0⦌) x)))
  let z := ULift.up.{u + 1} (nerveVertex c)
  have he := fractionKanSpaceDiagram_classificationIso_component F x c
  change functorHomEvaluate (fractionKanSpaceDiagram_classificationIso F x).hom
      (ULift.up ((transportSimplexFirstVertexMap X).app (Opposite.op ⦋0⦌) (nerveVertex c))) =
    functorHomEvaluate ((fractionKanSpaceDiagram_restrictionIso F x).hom ≫
      (fractionKanSimplexClassificationIso F x).hom) z at he
  rw [functorHomEvaluate_comp (U := k ≫ S) (V := T) (W := k ≫ G)] at he
  simp only [← functorIso_app_hom_evaluate] at he
  have hc := congrArg (fun m => (fractionKanSpaceDiagram_initialVertexIso F x c).inv ≫ m) he
  dsimp only [z] at hc
  simp only [fractionKanSpaceDiagram_initialVertexIso, Iso.trans_inv,
    Category.assoc, Iso.inv_hom_id_assoc] at hc
  simpa only [fractionKanSimplexClassificationValueIso, fractionKanSpaceDiagram_initialVertexIso,
    Iso.trans_inv, Category.assoc, Iso.trans_hom, Iso.symm_hom,
    functorIso_app_hom_evaluate] using hc

end SerrePositivity.KST.Fibration
