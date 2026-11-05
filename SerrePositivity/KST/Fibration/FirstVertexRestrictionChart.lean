module
public import SerrePositivity.KST.Fibration.FirstVertexUnderBaseChange

/-! # 元の初頂点制限比較全体の同じ成分は、制限した切断の同じ pullback 持ち上げ -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w v' w'
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {B : SSet.{u}}

private lemma normalizeSpan {C : Type v} [Category.{w} C]
    {a b c a' b' c' : C} (l : a ≅ b) (e : c ≅ b)
    (ha : a = a') (hb : b = b') (hc : c = c') :
    F2.isoNormalizeEndpoints (l ≪≫ e.symm) ha hc =
      F2.isoNormalizeEndpoints l ha hb ≪≫ (F2.isoNormalizeEndpoints e hc hb).symm := by
  subst a' b' c'
  simp only [F2.isoNormalizeEndpoints, eqToIso_refl, Iso.refl_symm, Iso.refl_trans,
    Iso.trans_refl]

private lemma mapNormalizeSpan {C : Type v} [Category.{w} C]
    {Z : Type v'} [Category.{w'} Z] (F : C ⥤ Z) {a b c : C} {a' b' c' : Z}
    (l : a ≅ b) (e : c ≅ b) (d : a ≅ c) (hd : d = l ≪≫ e.symm)
    (ha : F.obj a = a') (hb : F.obj b = b') (hc : F.obj c = c') :
    F2.isoNormalizeEndpoints (F.mapIso d) ha hc =
      F2.isoNormalizeEndpoints (F.mapIso l) ha hb ≪≫
        (F2.isoNormalizeEndpoints (F.mapIso e) hc hb).symm := by
  subst d
  rw [Functor.mapIso_trans, Functor.mapIso_symm]
  exact normalizeSpan _ _ ha hb hc

/-- 元の初頂点制限同型そのものの成分を、同じ分類値と pullback 切断空間で表示する。 -/
def firstVertexRestrictionChart (X : LeftFibrationObject B)
    (c : TransportSimplexCategory B) :=
  F2.isoNormalizeEndpoints
    (VertexIso.map (leftStraighteningInfinityMap_firstVertexRestrictionIso B)
      (_root_.SerrePositivity.InfinityCategories.F1.KanModels.kanEnrichedDoubleEvaluation X c))
    (congrArg HomotopyCategory.mk (straighteningRestrict_source_vertex X c))
    (congrArg HomotopyCategory.mk (transportUnderBaseChange_source_vertex X c))

/-- 表示変更後も、元の制限同型そのものの同じ指定二重成分を保持する。 -/
theorem firstVertexRestrictionChart_heq_doubleMap
    (X : LeftFibrationObject B) (c : TransportSimplexCategory B) :
    HEq (firstVertexRestrictionChart X c)
      (VertexIso.map (leftStraighteningInfinityMap_firstVertexRestrictionIso B)
        (_root_.SerrePositivity.InfinityCategories.F1.KanModels.kanEnrichedDoubleEvaluation X c)) := by
  unfold firstVertexRestrictionChart F2.isoNormalizeEndpoints
  exact F2.iso_endpoints_heq _ _ _

/-- 同じ元の制限成分は、元の under 実現比較と同じ逆 pullback 比較の合成。 -/
theorem firstVertexRestrictionChart_factor
    (X : LeftFibrationObject B) (c : TransportSimplexCategory B) :
    firstVertexRestrictionChart X c = straighteningUnderRealizationChart X c ≪≫
      (firstVertexUnderBaseChangeChart X c).symm := by
  exact mapNormalizeSpan (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.F1.KanModels.kanEnrichedDoubleEvaluation X c)).toFunctor
    (leftStraighteningInfinityMap_underRealizationIso B)
    (transportSimplexUnderBaseChangeRealizationIso B)
    (leftStraighteningInfinityMap_firstVertexRestrictionIso B) rfl
    (congrArg HomotopyCategory.mk (straighteningRestrict_source_vertex X c))
    (congrArg HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.F1.KanModels.kanEnrichedDoubleEvaluation_vertex
      (relativeSectionEnrichedDiagram (transportSimplexUnderDomains B)) X c))
    (congrArg HomotopyCategory.mk (transportUnderBaseChange_source_vertex X c))

/-- 同じ指定初頂点成分は、元の切断点を under に制限して厳密に持ち上げた点へ送る。 -/
theorem firstVertexRestrictionChart_pointHom
    (X : LeftFibrationObject B) (c : TransportSimplexCategory B)
    (v : (((relativeSectionEnrichedDiagram (transportSimplexDomainFunctor B)).obj c).obj X).obj
      _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom ((pointedSpaceFiberVertexEquiv
      (((relativeSectionEnrichedDiagram (transportSimplexDomainFunctor B)).obj c).obj X)).symm v) ≫
      (straighteningFirstVertexSectionChart X c).inv ≫
        (firstVertexRestrictionChart X c).hom =
    _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom ((pointedSpaceFiberVertexEquiv
      ((((relativeSectionEnrichedDiagram (strictTransportDomains
        (TransportSimplexCategory B))).precompose
          (leftFibrationBaseChangeEnriched (transportSimplexFirstVertexMap B))).obj c).obj X)).symm
            ((relativeFunctorBaseChangeBackward X.val.hom (transportSimplexFirstVertexMap B)
              ((strictTransportDomains (TransportSimplexCategory B)).obj (Opposite.op c)).hom).app
                (Opposite.op ⦋0⦌)
                ((relativeFunctorOverPre X.val.hom
                  ((transportSimplexUnderDomainTransformation B).app (Opposite.op c))).app
                    (Opposite.op ⦋0⦌) v))) := by
  have hu := firstVertexUnderBaseChangeChart_backward_pointHom X c
    ((relativeFunctorOverPre X.val.hom
      ((transportSimplexUnderDomainTransformation B).app (Opposite.op c))).app
        (Opposite.op ⦋0⦌) v)
  have hp := straighteningUnderRealizationChart_pointHom X c v
  have he := congrArg (fun m => m ≫ (firstVertexUnderBaseChangeChart X c).inv) hp
  simp only [Category.assoc] at he
  rw [firstVertexRestrictionChart_factor]
  simp only [Iso.trans_hom, Iso.symm_hom]
  exact he.trans hu

end SerrePositivity.KST.Fibration
