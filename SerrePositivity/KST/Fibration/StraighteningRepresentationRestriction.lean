module
public import SerrePositivity.InfinityCategories.Stable.Straightening.StraighteningRepresentationRestriction
public import SerrePositivity.KST.Fibration.StraighteningGlobalBaseChangeValue
public import SerrePositivity.InfinityCategories.F1.Transport.PointedClassificationReconstruction
public import SerrePositivity.InfinityCategories.F1.Transport.FunctorIsoValueInverse
public import SerrePositivity.KST.LocalizingInvariants.LocalizationUniqueness

/-! # 元の分類・表現比較を初頂点へ戻し、同じ指定比較を回収する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable {E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
  (R : LeftTransportRepresentation ((SSet.uliftFunctor.{u + 1, u}).map p))

/-- 元の表現比較の定義が指定した、同じ初頂点上の比較。 -/
def straighteningRepresentationRestrictionIso :=
  leftStraighteningInfinityDiagram_firstVertexTransportIso p ≪≫
    nerveCoherentTransportRepresentationIso
      (pullback.snd p (transportSimplexFirstVertexMap B))
      (R.nativeRestrict (transportSimplexFirstVertexMap B))

variable [Quasicategory B]

/-- Sp の前合成充満忠実性で、元の分類比較を同じ指定制限比較として回収する。 -/
theorem leftStraighteningRepresentationIso_pre :
    (hoFunctor.map ((pre ((SSet.uliftFunctor.{u + 1, u}).map
      (transportSimplexFirstVertexMap B))).app SpaceInfinity.{u})).toFunctor.map
        (leftStraighteningInfinityDiagram_representationIso p R).hom =
      (straighteningRepresentationRestrictionIso p R).hom := by
  exact (localizationPre_fullyFaithful (Y := SpaceInfinity.{u}) _ _
    (transportSimplexFirstVertexMap_ulift_isLocalization.{u, u + 1} B)
    ).toHoFullyFaithful.map_preimage _

/-- 元の分類比較の同じ初頂点成分を、指定した制限比較の成分として回収する。 -/
theorem leftStraighteningRepresentationIso_value (c : TransportSimplexCategory B) :
    functorHomEvaluate (leftStraighteningInfinityDiagram_representationIso p R).hom
      (ULift.up ((transportSimplexFirstVertexMap B).app (Opposite.op ⦋0⦌)
        (nerveVertex c))) =
      functorHomEvaluate (straighteningRepresentationRestrictionIso p R).hom
        (ULift.up (nerveVertex c)) := by
  let l := (SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap B)
  let F := leftStraighteningInfinityDiagram p
  let G := R.diagram
  let a := ULift.up.{u + 1} (nerveVertex c)
  have h := congrArg (fun m : FunctorHom (l ≫ F) (l ≫ G) => functorHomEvaluate m a)
    (leftStraighteningRepresentationIso_pre p R)
  exact (functorHomEvaluate_precomp
    (leftStraighteningInfinityDiagram_representationIso p R).hom l a).symm.trans h

/-- 順方向成分だけでなく、同じ指定した成分同型そのものを回収する。 -/
theorem leftStraighteningRepresentationIso_valueIso (c : TransportSimplexCategory B) :
    functorIsoValue (leftStraighteningInfinityDiagram_representationIso p R)
      (ULift.up ((transportSimplexFirstVertexMap B).app (Opposite.op ⦋0⦌)
        (nerveVertex c))) =
      functorIsoValue (straighteningRepresentationRestrictionIso p R)
        (ULift.up (nerveVertex c)) := by
  apply Iso.ext
  exact leftStraighteningRepresentationIso_value p R c

/-- 元の同じ分類比較の逆成分も、指定した制限比較の逆成分として回収する。 -/
theorem leftStraighteningRepresentationIso_inv_value (c : TransportSimplexCategory B) :
    functorHomEvaluate (leftStraighteningInfinityDiagram_representationIso p R).inv
      (ULift.up ((transportSimplexFirstVertexMap B).app (Opposite.op ⦋0⦌)
        (nerveVertex c))) =
      functorHomEvaluate (straighteningRepresentationRestrictionIso p R).inv
        (ULift.up (nerveVertex c)) := by
  have h := congrArg (fun e => e.inv) (leftStraighteningRepresentationIso_valueIso p R c)
  rw [_root_.SerrePositivity.InfinityCategories.F1.Transport.functorIsoValue_inv, _root_.SerrePositivity.InfinityCategories.F1.Transport.functorIsoValue_inv] at h
  exact h

end SerrePositivity.KST.Fibration
