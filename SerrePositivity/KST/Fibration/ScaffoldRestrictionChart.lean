module
public import SerrePositivity.InfinityCategories.Stable.Transport.ScaffoldRestrictionChart
import SerrePositivity.InfinityCategories.Stable.Transport.ScaffoldRestrictionChart
public import SerrePositivity.KST.Fibration.FirstVertexDiagramVertices
public import SerrePositivity.KST.Fibration.ScaffoldStraighteningComparison

/-! # 指定 scaffold 比較の元の初頂点成分は、同じ係数点の fiber 像を回収する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory Limits SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

variable {E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
  (R : LeftTransportRepresentation ((SSet.uliftFunctor.{u + 1, u}).map p))

/-- 指定 scaffold の nerve 比較の同じ成分を、元の strict Kan 値で表示する。 -/
def scaffoldRestrictionNerveChart (c : TransportSimplexCategory B) :=
  F2.isoNormalizeEndpoints
    (_root_.SerrePositivity.InfinityCategories.F1.Transport.functorIsoValue (scaffoldNerveRepresentationIso
      (pullback.snd p (transportSimplexFirstVertexMap B))
      (R.nativeRestrict (transportSimplexFirstVertexMap B))) (ULift.up (nerveVertex c)))
    (congrArg HomotopyCategory.mk (leftStraighteningCandidate_vertex
      (pullback.snd p (transportSimplexFirstVertexMap B)) c)) rfl

/-- 指定した全制限比較の同じ成分を、元の共同分類値で表示する。 -/
def scaffoldStraighteningRestrictionChart (c : TransportSimplexCategory B) :=
  F2.isoNormalizeEndpoints
    (_root_.SerrePositivity.InfinityCategories.F1.Transport.functorIsoValue (scaffoldStraighteningRestrictionIso p R) (ULift.up (nerveVertex c)))
    (congrArg HomotopyCategory.mk (firstVertexDiagram_source_vertex p c)) rfl

/-- 元の全制限成分は、元の初頂点成分と指定 scaffold の同じ nerve 成分の合成。 -/
theorem scaffoldStraighteningRestrictionChart_factor (c : TransportSimplexCategory B) :
    scaffoldStraighteningRestrictionChart p R c =
      firstVertexRestrictionChart (leftFibrationObjectOf p) c ≪≫
        scaffoldRestrictionNerveChart p R c := by
  have hf := _root_.SerrePositivity.InfinityCategories.Stable.Transport.normalizeValueComposition (leftStraighteningInfinityDiagram_firstVertexIso p)
    (scaffoldNerveRepresentationIso (pullback.snd p (transportSimplexFirstVertexMap B))
      (R.nativeRestrict (transportSimplexFirstVertexMap B))) (ULift.up (nerveVertex c))
    (congrArg HomotopyCategory.mk (firstVertexDiagram_source_vertex p c))
    (congrArg HomotopyCategory.mk (leftStraighteningCandidate_vertex
      (pullback.snd p (transportSimplexFirstVertexMap B)) c)) rfl
  exact hf.trans (congrArg (fun e => e ≪≫ scaffoldRestrictionNerveChart p R c)
    (firstVertexDiagramValueIso_eq p c))

/-- 同じ nerve 成分は、元の strict 切断点の同じ恒等射評価を pointedMap へ送る。 -/
theorem scaffoldRestrictionNerveChart_pointHom (c : TransportSimplexCategory B)
    (v : (leftStrictTransport (pullback.snd p (transportSimplexFirstVertexMap B)) c) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom ((pointedSpaceFiberVertexEquiv ((leftStrictTransportFunctor
      (pullback.snd p (transportSimplexFirstVertexMap B))).obj c)).symm v) ≫
      (scaffoldRestrictionNerveChart p R c).hom =
    _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom ((transportRepresentationPointedFiberMap
      (R.nativeRestrict (transportSimplexFirstVertexMap B)) (ULift.up (nerveVertex c))).app
      (Opposite.op ⦋0⦌) ((uliftVertexFiberIso
        (pullback.snd p (transportSimplexFirstVertexMap B)) (nerveVertex c)).hom.app
          (Opposite.op ⦋0⦌) (ULift.up ((leftStrictTransportEvaluate
            (pullback.snd p (transportSimplexFirstVertexMap B)) c).app
              (Opposite.op ⦋0⦌) v)))) := by
  simp only [scaffoldRestrictionNerveChart, F2.isoNormalizeEndpoints, Iso.trans_hom,
    Iso.symm_hom, eqToIso_refl, Iso.refl_hom, Category.comp_id, _root_.SerrePositivity.InfinityCategories.F1.Transport.functorIsoValue_hom]
  exact scaffoldNerveRepresentationIso_pointHom
    (pullback.snd p (transportSimplexFirstVertexMap B))
    (R.nativeRestrict (transportSimplexFirstVertexMap B)) c v

/-- 元の指定制限成分は、同じ厳密切断の恒等射評価の pointedMap 像を回収する。 -/
theorem scaffoldStraighteningRestrictionChart_pointHom (c : TransportSimplexCategory B)
    (v : (((relativeSectionEnrichedDiagram (transportSimplexDomainFunctor B)).obj c).obj
      (leftFibrationObjectOf p)).obj _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom ((pointedSpaceFiberVertexEquiv
      (((relativeSectionEnrichedDiagram (transportSimplexDomainFunctor B)).obj c).obj
        (leftFibrationObjectOf p))).symm v) ≫
      (straighteningFirstVertexSectionChart (leftFibrationObjectOf p) c).inv ≫
        (scaffoldStraighteningRestrictionChart p R c).hom =
    _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom ((transportRepresentationPointedFiberMap
      (R.nativeRestrict (transportSimplexFirstVertexMap B)) (ULift.up (nerveVertex c))).app
      (Opposite.op ⦋0⦌) ((uliftVertexFiberIso
        (pullback.snd p (transportSimplexFirstVertexMap B)) (nerveVertex c)).hom.app
          (Opposite.op ⦋0⦌) (ULift.up ((leftStrictTransportEvaluate
            (pullback.snd p (transportSimplexFirstVertexMap B)) c).app (Opposite.op ⦋0⦌)
              ((firstVertexStrictSectionMap p c).app (Opposite.op ⦋0⦌) v))))) := by
  have hp := firstVertexRestrictionChart_pointHom_strictSection (leftFibrationObjectOf p) c v
  have he := congrArg (fun m => m ≫ (scaffoldRestrictionNerveChart p R c).hom) hp
  simp only [Category.assoc] at he
  have hn := scaffoldRestrictionNerveChart_pointHom p R c
    ((firstVertexStrictSectionMap p c).app (Opposite.op ⦋0⦌) v)
  rw [scaffoldStraighteningRestrictionChart_factor]
  simp only [Iso.trans_hom]
  exact he.trans hn

end SerrePositivity.KST.Fibration
