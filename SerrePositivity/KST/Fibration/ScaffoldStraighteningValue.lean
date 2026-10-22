module
public import SerrePositivity.KST.Fibration.ScaffoldRestrictionChart

/-! # 指定 scaffold 比較を降下した後も、元の同じ初頂点成分を回収する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [LeftFibration p]
  (R : LeftTransportRepresentation ((SSet.uliftFunctor.{u + 1, u}).map p))

/-- 降下した指定同型の元の初頂点成分は、同じ指定制限比較の成分。 -/
theorem scaffoldStraighteningRepresentationIso_value (c : TransportSimplexCategory B) :
    functorHomEvaluate (scaffoldStraighteningRepresentationIso p R).hom
      (ULift.up ((transportSimplexFirstVertexMap B).app (Opposite.op ⦋0⦌)
        (nerveVertex c))) =
      functorHomEvaluate (scaffoldStraighteningRestrictionIso p R).hom
        (ULift.up (nerveVertex c)) := by
  let l := (SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap B)
  let F := leftStraighteningInfinityDiagram p
  let G := R.diagram
  let a := ULift.up.{u + 1} (nerveVertex c)
  have h := congrArg (fun m : FunctorHom (l ≫ F) (l ≫ G) => functorHomEvaluate m a)
    (scaffoldStraighteningRepresentationIso_pre p R)
  exact (functorHomEvaluate_precomp
    (scaffoldStraighteningRepresentationIso p R).hom l a).symm.trans h

/-- 同じ指定同型の成分同型そのものを回収する。 -/
theorem scaffoldStraighteningRepresentationIso_valueIso (c : TransportSimplexCategory B) :
    functorIsoValue (scaffoldStraighteningRepresentationIso p R)
      (ULift.up ((transportSimplexFirstVertexMap B).app (Opposite.op ⦋0⦌)
        (nerveVertex c))) =
      functorIsoValue (scaffoldStraighteningRestrictionIso p R)
        (ULift.up (nerveVertex c)) := by
  apply Iso.ext
  exact scaffoldStraighteningRepresentationIso_value p R c

/-- 元の降下同型の同じ成分を、元の共同分類値で表示する。 -/
def scaffoldStraighteningGlobalChart (c : TransportSimplexCategory B) :=
  F2.isoNormalizeEndpoints
    (functorIsoValue (scaffoldStraighteningRepresentationIso p R)
      (ULift.up ((transportSimplexFirstVertexMap B).app (Opposite.op ⦋0⦌) (nerveVertex c))))
    (congrArg HomotopyCategory.mk (firstVertexDiagram_source_vertex p c)) rfl

/-- 降下後の元の指定成分は、元の全制限成分と厳密に一致する。 -/
theorem scaffoldStraighteningGlobalChart_eq (c : TransportSimplexCategory B) :
    scaffoldStraighteningGlobalChart p R c = scaffoldStraighteningRestrictionChart p R c := by
  have hr : HEq (scaffoldStraighteningRestrictionChart p R c)
      (functorIsoValue (scaffoldStraighteningRestrictionIso p R)
        (ULift.up (nerveVertex c))) := by
    unfold scaffoldStraighteningRestrictionChart F2.isoNormalizeEndpoints
    exact F2.iso_endpoints_heq _ _ _
  exact F2.isoNormalizeEndpoints_eq_of_heq _ _ _ _
    ((heq_of_eq (scaffoldStraighteningRepresentationIso_valueIso p R c)).trans hr.symm)

/-- 元の降下比較の同じ指定成分でも、元の厳密切断の同じ pointedMap 像を回収する。 -/
theorem scaffoldStraighteningGlobalChart_pointHom (c : TransportSimplexCategory B)
    (v : (((relativeSectionEnrichedDiagram (transportSimplexDomainFunctor B)).obj c).obj
      (leftFibrationObjectOf p)).obj _⦋0⦌) :
    cosliceFiberPointHom ((pointedSpaceFiberVertexEquiv
      (((relativeSectionEnrichedDiagram (transportSimplexDomainFunctor B)).obj c).obj
        (leftFibrationObjectOf p))).symm v) ≫
      (straighteningFirstVertexSectionChart (leftFibrationObjectOf p) c).inv ≫
        (scaffoldStraighteningGlobalChart p R c).hom =
    cosliceFiberPointHom ((transportRepresentationPointedFiberMap
      (R.nativeRestrict (transportSimplexFirstVertexMap B)) (ULift.up (nerveVertex c))).app
      (Opposite.op ⦋0⦌) ((uliftVertexFiberIso
        (pullback.snd p (transportSimplexFirstVertexMap B)) (nerveVertex c)).hom.app
          (Opposite.op ⦋0⦌) (ULift.up ((leftStrictTransportEvaluate
            (pullback.snd p (transportSimplexFirstVertexMap B)) c).app (Opposite.op ⦋0⦌)
              ((firstVertexStrictSectionMap p c).app (Opposite.op ⦋0⦌) v))))) := by
  rw [scaffoldStraighteningGlobalChart_eq]
  exact scaffoldStraighteningRestrictionChart_pointHom p R c v

end SerrePositivity.KST.Fibration
