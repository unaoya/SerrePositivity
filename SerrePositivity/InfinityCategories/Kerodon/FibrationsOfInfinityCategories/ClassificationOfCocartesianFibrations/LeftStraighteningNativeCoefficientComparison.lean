module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningNativeCoefficients

/-!
概要：元のσと、同じunder・底変換・反転の三成分の合成を照合する。
方針：指定大域比較の同じ値を取り、端点の正規化を三成分の合成に移す。
規約：HTT §3.3.2、Kerodon §5.6（Tag 028T）の構成の特殊な照合。
使われ方：P3-C1PNG、指定νを元のstrict変換の実現の類へ戻す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

local instance comparison_left {E B D : SSet.{u}} (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) :
    LeftFibration (pullback.snd p k) := ⟨leftFibrations.pullback_snd p k (LeftFibration.mem (p := p))⟩

private lemma value_eqIso {A Y : SSet.{u}} {F G : A ⟶ Y} (h : F = G) (x : A _⦋0⦌) :
    functorIsoValue (eqToIso (congrArg (fun f => HomotopyCategory.mk (functorVertex f)) h)) x =
      eqToIso (congrArg (fun v => HomotopyCategory.mk v) (congrArg (fun f => f.app _ x) h)) := by
  cases h
  simp only [eqToIso_refl]
  apply Iso.ext
  rw [functorIsoValue_hom]
  exact functorHomEvaluate_id _ _

private lemma normalize_chain {L : Type*} [Category* L] {a b c d e a' b' c' e' : L}
    (r : a ≅ b) (s : c ≅ b) (t : d ≅ e)
    (ha : a = a') (hb : b = b') (hc : c = c') (hd : d = c') (he : e = e') (h : c = d) :
    ((eqToIso ha).symm ≪≫ r ≪≫ eqToIso hb) ≪≫
      ((eqToIso hc).symm ≪≫ s ≪≫ eqToIso hb).symm ≪≫
      ((eqToIso hd).symm ≪≫ t ≪≫ eqToIso he) =
      (eqToIso ha).symm ≪≫ (r ≪≫ s.symm ≪≫ eqToIso h ≪≫ t) ≪≫ eqToIso he := by
  subst a' b' c' e'
  subst d
  simp only [eqToIso_refl, Iso.refl_symm, Iso.refl_trans, Iso.trans_refl]

/-- 元のσは同じ三つの指定成分の合成に一致する。 -/
@[cite HTT "3.3.2" (partial := special) "初頂点の指定transport比較と同じ三つの係数成分の照合。"]
lemma leftStraightening_firstVertexTransport_nativeCoefficients :
    ∀ {E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [LeftFibration p],
    (leftClassificationSimplexIso p).symm ≪≫
      leftStraighteningInfinityDiagram_firstVertexTransportIso p = firstVertexNativeCoefficientIso p := by
  intro E B hB p hp
  let C := TransportSimplexCategory B
  let p₀ := pullback.snd p (transportSimplexFirstVertexMap B)
  let X := edgewiseOrdinaryObject (leftFibrationObjectOf p)
  let x := coherentNerveVertex X
  let Z := edgewiseOrdinaryObject (leftFibrationObjectOf p₀)
  let j := edgewiseEnrichedInfinityMap (LeftFibrationObject B)
  let j₀ := edgewiseEnrichedInfinityMap (LeftFibrationObject (nerve C))
  let b := leftFibrationEdgewiseFirstVertexBaseChange B
  let U := transportSimplexUnderRealizationIso B
  let V := transportSimplexUnderBaseChangeRealizationIso B
  let W := leftStraighteningCoherentMap_oppositeIso C
  have hfun : j ≫ (leftFibrationInfinityBaseChange (transportSimplexFirstVertexMap B) ≫
      leftStraighteningCoherentMap C) = b ≫ (j₀ ≫ leftStraighteningCoherentMap C) := by
    rw [← Category.assoc, ← leftFibrationEdgewiseFirstVertexBaseChange_projection, Category.assoc]
  let h := congrArg (fun v => HomotopyCategory.mk v) (congrArg (fun f => f.app _ x) hfun)
  let γ := U.precomp j ≪≫ (V.precomp j).symm ≪≫
    eqToIso (congrArg (fun f => HomotopyCategory.mk (functorVertex f)) hfun) ≪≫ W.precomp b
  let r := functorIsoValue (U.precomp j) x
  let s := functorIsoValue (V.precomp j) x
  let t := functorIsoValue (W.precomp b) x
  have hj : j.app _ x = leftFibrationInfinityVertex p := by
    change (coherentNerveMap (edgewiseEnrichedRight (LeftFibrationObject B))).app _ x = _
    rw [coherentNerveMap_vertex]
    rfl
  have hbz : b.app _ x = coherentNerveVertex Z :=
    leftFibrationEdgewiseFirstVertexBaseChange_vertex B (leftFibrationObjectOf p)
  have ha : (j ≫ (relativeSectionEnrichedDiagram (transportSimplexDomainFunctor B)).realization).app _ x =
      functorVertex (simplexSectionValue p) := by
    change (relativeSectionEnrichedDiagram (transportSimplexDomainFunctor B)).realization.app _ (j.app _ x) = _
    rw [hj]
    exact (relativeSectionEnrichedDiagram (transportSimplexDomainFunctor B)).realization_vertex _
  have hb : (j ≫ (relativeSectionEnrichedDiagram (transportSimplexUnderDomains B)).realization).app _ x =
      functorVertex (kanDiagramCoherentNerve ((relativeSectionEnrichedDiagram
        (transportSimplexUnderDomains B)).evaluate (leftFibrationObjectOf p))) := by
    change (relativeSectionEnrichedDiagram (transportSimplexUnderDomains B)).realization.app _ (j.app _ x) = _
    rw [hj]
    exact (relativeSectionEnrichedDiagram (transportSimplexUnderDomains B)).realization_vertex _
  have hc : (j ≫ (leftFibrationInfinityBaseChange (transportSimplexFirstVertexMap B) ≫
      leftStraighteningCoherentMap C)).app _ x = functorVertex (leftStraighteningCandidate p₀) := by
    change (leftStraighteningCoherentMap C).app _
      ((leftFibrationInfinityBaseChange (transportSimplexFirstVertexMap B)).app _ (j.app _ x)) = _
    rw [hj]
    change (leftStraighteningCoherentMap C).app _
      ((leftFibrationInfinityBaseChange (transportSimplexFirstVertexMap B)).app _
        (coherentNerveVertex (leftFibrationObjectOf p))) = _
    rw [leftFibrationInfinityBaseChange_vertex]
    exact leftStraighteningCoherentMap_vertex p₀
  have hd : (b ≫ (j₀ ≫ leftStraighteningCoherentMap C)).app _ x =
      functorVertex (leftStraighteningCandidate p₀) := by
    change (leftStraighteningCoherentMap C).app _ (j₀.app _ (b.app _ x)) = _
    rw [hbz]
    change (leftStraighteningCoherentMap C).app _
      ((coherentNerveMap (edgewiseEnrichedRight (LeftFibrationObject (nerve C)))).app _
        (coherentNerveVertex Z)) = _
    rw [coherentNerveMap_vertex]
    exact leftStraighteningCoherentMap_vertex p₀
  have he : (b ≫ leftStraighteningOppositeCoherentMap C).app _ x =
      functorVertex (leftCoherentTransport p₀) := by
    exact (congrArg ((leftStraighteningOppositeCoherentMap C).app _) hbz).trans
      (leftStraighteningOppositeCoherentMap_vertex p₀)
  have hr : HEq (nativeUnderCoefficientIso p) r :=
    (nativeUnderCoefficientIso_heq p).trans
      (((heq_of_eq (functorIsoValue_precomp U j x)).trans (functorIsoValue_point_heq U hj)).symm)
  have hs : HEq (nativeBaseChangeCoefficientIso p) s :=
    (nativeBaseChangeCoefficientIso_heq p).trans
      (((heq_of_eq (functorIsoValue_precomp V j x)).trans (functorIsoValue_point_heq V hj)).symm)
  have ht : HEq (nativeOppositeCoefficientIso p₀) t :=
    (nativeOppositeCoefficientIso_heq p₀).trans
      (((heq_of_eq (functorIsoValue_precomp W b x)).trans (functorIsoValue_point_heq W hbz)).symm)
  have hNr : (eqToIso (congrArg (fun v => HomotopyCategory.mk v) ha)).symm ≪≫ r ≪≫
      eqToIso (congrArg (fun v => HomotopyCategory.mk v) hb) = nativeUnderCoefficientIso p :=
    eq_of_heq ((iso_endpoints_heq r _ _).trans hr.symm)
  have hNs : (eqToIso (congrArg (fun v => HomotopyCategory.mk v) hc)).symm ≪≫ s ≪≫
      eqToIso (congrArg (fun v => HomotopyCategory.mk v) hb) = nativeBaseChangeCoefficientIso p :=
    eq_of_heq ((iso_endpoints_heq s _ _).trans hs.symm)
  have hNt : (eqToIso (congrArg (fun v => HomotopyCategory.mk v) hd)).symm ≪≫ t ≪≫
      eqToIso (congrArg (fun v => HomotopyCategory.mk v) he) = nativeOppositeCoefficientIso p₀ :=
    eq_of_heq ((iso_endpoints_heq t _ _).trans ht.symm)
  have hvs : functorIsoValue (V.precomp j).symm x = s.symm := by
    apply Iso.ext
    simp only [functorIsoValue_hom, Iso.symm_hom]
    exact (functorIsoValue_inv (V.precomp j) x).symm
  have hγ : functorIsoValue γ x = r ≪≫ s.symm ≪≫ eqToIso h ≪≫ t := by
    simp only [γ, functorIsoValue_trans]
    rw [hvs, value_eqIso hfun x]
  have hN : firstVertexNativeCoefficientIso p =
      (eqToIso (congrArg (fun v => HomotopyCategory.mk v) ha)).symm ≪≫
        (r ≪≫ s.symm ≪≫ eqToIso h ≪≫ t) ≪≫
      eqToIso (congrArg (fun v => HomotopyCategory.mk v) he) := by
    change nativeUnderCoefficientIso p ≪≫ (nativeBaseChangeCoefficientIso p).symm ≪≫
      nativeOppositeCoefficientIso p₀ = _
    rw [← hNr, ← hNs, ← hNt]
    exact normalize_chain r s t _ _ _ _ _ h
  have hσ : HEq ((leftClassificationSimplexIso p).symm ≪≫
      leftStraighteningInfinityDiagram_firstVertexTransportIso p) (functorIsoValue γ x) :=
    leftStraightening_firstVertexTransport_underValue p
  exact eq_of_heq (hσ.trans ((heq_of_eq hγ).trans
    ((iso_endpoints_heq _ _ _).symm.trans (heq_of_eq hN.symm))))

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
