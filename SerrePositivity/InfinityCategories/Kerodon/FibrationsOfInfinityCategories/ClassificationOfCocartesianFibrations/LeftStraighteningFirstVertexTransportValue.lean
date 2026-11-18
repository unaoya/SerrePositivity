module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.NormalizedFunctorIsoComponentRestriction
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.FunctorIsoValueComposition
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.FunctorIsoValueCurry
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FunctorIsoWhiskerAlgebra
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningSimplexPastingInputs
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningRepresentation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.FunctorIsoValue
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseOrdinaryLift
/-!
概要：指定初頂点transport比較の成分を、同じunderの係数比較の成分へ戻す。
方針：元の大域比較を先に分解し、同じ成分の端点移送と中間同型を相殺する。
規約：HTT §3.3.2・Kerodon §5.6、Corollary 5.6.0.6（Tag 028T）の構成の法則。
  この相対切断模型に特殊化した照合で、任意の同型の存在へ置き換えない。
使われ方：5∞-1のP3-C1PNV、指定νの反転区間の類への接続。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

private def underOppositeComparison (B : SSet.{u}) :=
  let C := TransportSimplexCategory B
  let j := edgewiseEnrichedInfinityMap (LeftFibrationObject B)
  let b := leftFibrationEdgewiseFirstVertexBaseChange B
  let h : j ≫ (leftFibrationInfinityBaseChange (transportSimplexFirstVertexMap B) ≫
      leftStraighteningCoherentMap C) =
      b ≫ (edgewiseEnrichedInfinityMap (LeftFibrationObject (nerve C)) ≫
        leftStraighteningCoherentMap C) := by
    rw [← Category.assoc, ← leftFibrationEdgewiseFirstVertexBaseChange_projection,
      Category.assoc]
  (transportSimplexUnderRealizationIso B).precomp j ≪≫
    ((transportSimplexUnderBaseChangeRealizationIso B).precomp j).symm ≪≫
    eqToIso (congrArg (fun f => HomotopyCategory.mk (functorVertex f)) h) ≪≫
    (leftStraighteningCoherentMap_oppositeIso C).precomp b

private lemma firstVertexOpposite_factor (B : SSet.{u}) :
    leftStraighteningInfinityMap_firstVertexOppositeIso B =
      (leftStraighteningSimplexRestrictionIso B).precomp
        (edgewiseEnrichedInfinityMap (LeftFibrationObject B)) ≪≫ underOppositeComparison B := by
  unfold leftStraighteningInfinityMap_firstVertexOppositeIso
    leftStraighteningInfinityMap_firstVertexRestrictionIso
    leftStraighteningInfinityMap_underRealizationIso leftStraighteningSimplexRestrictionIso
    underOppositeComparison
  dsimp only
  simp only [functorIso_precomp_trans, functorIso_precomp_symm]
  apply Iso.ext
  simp only [Iso.trans_hom, Category.assoc]

private lemma normalized_cancel {L : Type*} [Category* L] {a b c a' b' c' : L}
    (e : a ≅ b) (f : b ≅ c) (ha : a = a') (hb : b = b') (hc : c = c') :
    HEq (((eqToIso ha).symm ≪≫ e ≪≫ eqToIso hb).symm ≪≫
      ((eqToIso ha).symm ≪≫ (e ≪≫ f) ≪≫ eqToIso hc)) f := by
  subst a' b' c'
  simp only [eqToIso_refl, Iso.refl_symm, Iso.refl_trans, Iso.trans_refl]
  have h : e.symm ≪≫ (e ≪≫ f) = f := by
    apply Iso.ext
    simp only [Iso.trans_hom, Iso.symm_hom, ← Category.assoc, Iso.inv_hom_id,
      Category.id_comp]
  exact heq_of_eq h

private lemma normalize_of_heq {L : Type*} [Category* L] {a b a' b' : L}
    (e : a ≅ b) (f : a' ≅ b') (ha : a = a') (hb : b = b') (h : HEq e f) :
    (eqToIso ha).symm ≪≫ e ≪≫ eqToIso hb = f := by
  subst a' b'
  cases eq_of_heq h
  simp only [eqToIso_refl, Iso.refl_symm, Iso.refl_trans, Iso.trans_refl]

/-- 指定transport比較の成分は、同じunder・底変換・反転比較の指定成分。
HTT §3.3.2・Kerodon Tag 028Tの相対切断模型における構成の照合法則。 -/
@[cite HTT "3.3.2" (partial := special) "指定初頂点transport比較と同じunder係数比較の成分の照合。"]
lemma leftStraightening_firstVertexTransport_underValue : ∀ {E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [LeftFibration p],
  let C := TransportSimplexCategory B
  let j := edgewiseEnrichedInfinityMap (LeftFibrationObject B)
  let b := leftFibrationEdgewiseFirstVertexBaseChange B
  let h : j ≫ (leftFibrationInfinityBaseChange (transportSimplexFirstVertexMap B) ≫
      leftStraighteningCoherentMap C) =
      b ≫ (edgewiseEnrichedInfinityMap (LeftFibrationObject (nerve C)) ≫
        leftStraighteningCoherentMap C) := by
    rw [← Category.assoc, ← leftFibrationEdgewiseFirstVertexBaseChange_projection,
      Category.assoc]
  let γ := (transportSimplexUnderRealizationIso B).precomp j ≪≫
    ((transportSimplexUnderBaseChangeRealizationIso B).precomp j).symm ≪≫
    eqToIso (congrArg (fun f => HomotopyCategory.mk (functorVertex f)) h) ≪≫
    (leftStraighteningCoherentMap_oppositeIso C).precomp b
  let X := edgewiseOrdinaryObject (leftFibrationObjectOf p)
  HEq ((leftClassificationSimplexIso p).symm ≪≫
      leftStraighteningInfinityDiagram_firstVertexTransportIso p)
    (functorIsoValue γ (coherentNerveVertex X)) := by
  intro E B hB p hp
  let X := edgewiseOrdinaryObject (leftFibrationObjectOf p)
  let x := coherentNerveVertex X
  let j := edgewiseEnrichedInfinityMap (LeftFibrationObject B)
  let b := leftFibrationEdgewiseFirstVertexBaseChange B
  let A := leftStraighteningSimplexRestrictionIso B
  let D := relativeSectionEnrichedDiagram (transportSimplexDomainFunctor B)
  let F := leftStraighteningInfinityMap B ≫
    (pre ((SSet.uliftFunctor.{u+1,u}).map (transportSimplexFirstVertexMap B))).app
      SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}
  let a := leftClassificationSimplexIso p
  let t := leftStraighteningInfinityDiagram_firstVertexTransportIso p
  let e := functorIsoValue (A.precomp j) x
  let g := functorIsoValue (underOppositeComparison B) x
  change HEq (a.symm ≪≫ t) g
  have hj : j.app _ x = leftFibrationInfinityVertex p := by
    change (coherentNerveMap (edgewiseEnrichedRight (LeftFibrationObject B))).app _
      (coherentNerveVertex X) = _
    rw [coherentNerveMap_vertex]
    rfl
  have hva : (j ≫ F).app _ x = functorVertex
      ((SSet.uliftFunctor.{u+1,u}).map (transportSimplexFirstVertexMap B) ≫
        leftStraighteningInfinityDiagram p) := by
    change F.app _ (j.app _ x) = _
    rw [hj]
    exact (leftClassificationSimplex_sourceEq p).symm
  have hvb : (j ≫ D.realization).app _ x =
      functorVertex (kanDiagramCoherentNerve (D.evaluate (leftFibrationObjectOf p))) := by
    change D.realization.app _ (j.app _ x) = _
    rw [hj]
    exact D.realization_vertex (leftFibrationObjectOf p)
  have hvc : (b ≫ leftStraighteningOppositeCoherentMap (TransportSimplexCategory B)).app _ x =
      functorVertex (leftCoherentTransport (pullback.snd p (transportSimplexFirstVertexMap B))) := by
    exact (congrArg ((leftStraighteningOppositeCoherentMap (TransportSimplexCategory B)).app _)
      (leftFibrationEdgewiseFirstVertexBaseChange_vertex B (leftFibrationObjectOf p))).trans
        (leftStraighteningOppositeCoherentMap_vertex
          (pullback.snd p (transportSimplexFirstVertexMap B)))
  have he : HEq e (A.app (leftFibrationInfinityVertex p)) :=
    (heq_of_eq (functorIsoValue_precomp A j x)).trans
      ((functorIsoValue_point_heq A hj).trans
        (heq_of_eq (functorIsoValue_eq_app A (leftFibrationInfinityVertex p))))
  have ha : HEq a e :=
    (normalizedFunctorIsoComponent_heq_app A (leftFibrationInfinityVertex p)
      (leftClassificationSimplex_sourceEq p) (leftClassificationSimplex_targetEq p)).trans he.symm
  have ht : HEq t
      (functorIsoValue (leftStraighteningInfinityMap_firstVertexOppositeIso B) x) := by
    dsimp only [t]
    unfold leftStraighteningInfinityDiagram_firstVertexTransportIso
    change HEq ((eqToIso _).symm ≪≫
      (leftStraighteningInfinityMap_firstVertexOppositeIso B).app x ≪≫ eqToIso _) _
    exact (iso_endpoints_heq _ _ _).trans
      (heq_of_eq (functorIsoValue_eq_app _ _)).symm
  have hprod : functorIsoValue (leftStraighteningInfinityMap_firstVertexOppositeIso B) x =
      e ≪≫ g := by
    rw [firstVertexOpposite_factor, functorIsoValue_trans]
  have hna := normalize_of_heq e a (congrArg (fun v => HomotopyCategory.mk v) hva)
    (congrArg (fun v => HomotopyCategory.mk v) hvb) ha.symm
  have hnt := normalize_of_heq (e ≪≫ g) t (congrArg (fun v => HomotopyCategory.mk v) hva)
    (congrArg (fun v => HomotopyCategory.mk v) hvc) (ht.trans (heq_of_eq hprod)).symm
  rw [← hna, ← hnt]
  exact normalized_cancel e g _ _ _

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
