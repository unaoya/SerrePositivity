module
public import SerrePositivity.KST.Fibration.FirstVertexOppositeVertices

/-! # 元の初頂点 transport 比較の同じ成分は、同じ厳密切断点を反転する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w v' w'
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

private lemma normalizeComposition {C : Type v} [Category.{w} C]
    {a b c a' b' c' : C} (l : a ≅ b) (e : b ≅ c)
    (ha : a = a') (hb : b = b') (hc : c = c') :
    F2.isoNormalizeEndpoints (l ≪≫ e) ha hc =
      F2.isoNormalizeEndpoints l ha hb ≪≫ F2.isoNormalizeEndpoints e hb hc := by
  subst a' b' c'
  simp only [F2.isoNormalizeEndpoints, eqToIso_refl, Iso.refl_symm, Iso.refl_trans,
    Iso.trans_refl]

private lemma firstVertexOppositeChart_mapNormalizeCompositionWithEq {C : Type v} [Category.{w} C]
    {Z : Type v'} [Category.{w'} Z] (F : C ⥤ Z) {a b b₀ c : C} {a' b' c' : Z}
    (l : a ≅ b) (e : b₀ ≅ c) (h : b = b₀) (d : a ≅ c)
    (hd : d = l ≪≫ eqToIso h ≪≫ e)
    (ha : F.obj a = a') (hb : F.obj b = b') (hb₀ : F.obj b₀ = b')
    (hc : F.obj c = c') :
    F2.isoNormalizeEndpoints (F.mapIso d) ha hc =
      F2.isoNormalizeEndpoints (F.mapIso l) ha hb ≪≫
        F2.isoNormalizeEndpoints (F.mapIso e) hb₀ hc := by
  subst d b₀
  simp only [eqToIso_refl, Iso.refl_trans, Functor.mapIso_trans]
  exact normalizeComposition _ _ ha hb hc

variable {E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p]

local instance : LeftFibration (pullback.snd p (transportSimplexFirstVertexMap B)) :=
  ⟨leftFibrations.pullback_snd p _ (LeftFibration.mem (p := p))⟩

/-- 元の初頂点反転同型の指定成分を、同じ分類値と元の反転 strict Kan 値で表示する。 -/
def firstVertexOppositeChart (c : TransportSimplexCategory B) :=
  F2.isoNormalizeEndpoints
    (VertexIso.map (leftStraighteningInfinityMap_firstVertexOppositeIso B)
      (_root_.SerrePositivity.InfinityCategories.F1.KanModels.kanEnrichedDoubleEvaluation (firstVertexComparisonObject p) c))
    (congrArg HomotopyCategory.mk (firstVertexEdgewiseRestriction_source_vertex p c))
    (congrArg HomotopyCategory.mk (firstVertexOppositePre_target_vertex p c))

/-- 元の反転同型そのものの指定二重成分を、端点表示だけを除いて保持する。 -/
theorem firstVertexOppositeChart_heq_doubleMap (c : TransportSimplexCategory B) :
    HEq (firstVertexOppositeChart p c)
      (VertexIso.map (leftStraighteningInfinityMap_firstVertexOppositeIso B)
        (_root_.SerrePositivity.InfinityCategories.F1.KanModels.kanEnrichedDoubleEvaluation (firstVertexComparisonObject p) c)) := by
  unfold firstVertexOppositeChart F2.isoNormalizeEndpoints
  exact F2.iso_endpoints_heq _ _ _

/-- 元の指定成分全体は、元の制限成分と同じ pullback strict 切断の反転成分の合成。 -/
theorem firstVertexOppositeChart_factor (c : TransportSimplexCategory B) :
    firstVertexOppositeChart p c = firstVertexRestrictionChart (leftFibrationObjectOf p) c ≪≫
      _root_.SerrePositivity.InfinityCategories.Stable.Transport.strictTransportOppositeComponentIso
        (pullback.snd p (transportSimplexFirstVertexMap B)) c := by
  let T := _root_.SerrePositivity.InfinityCategories.F1.KanModels.kanEnrichedDoubleEvaluation (firstVertexComparisonObject p) c
  have h : edgewiseEnrichedInfinityMap (LeftFibrationObject B) ≫
      (leftFibrationInfinityBaseChange (transportSimplexFirstVertexMap B) ≫
        leftStraighteningCoherentMap (TransportSimplexCategory B)) =
      leftFibrationEdgewiseFirstVertexBaseChange B ≫
        (edgewiseEnrichedInfinityMap
          (LeftFibrationObject (nerve (TransportSimplexCategory B))) ≫
            leftStraighteningCoherentMap (TransportSimplexCategory B)) := by
    rw [← Category.assoc, ← leftFibrationEdgewiseFirstVertexBaseChange_projection, Category.assoc]
  have hf := firstVertexOppositeChart_mapNormalizeCompositionWithEq (hoFunctor.map T).toFunctor
    ((leftStraighteningInfinityMap_firstVertexRestrictionIso B).precomp
      (edgewiseEnrichedInfinityMap (LeftFibrationObject B)))
    ((leftStraighteningCoherentMap_oppositeIso (TransportSimplexCategory B)).precomp
      (leftFibrationEdgewiseFirstVertexBaseChange B))
    (congrArg (fun f => HomotopyCategory.mk (functorVertex f)) h)
    (leftStraighteningInfinityMap_firstVertexOppositeIso B) rfl
    (congrArg HomotopyCategory.mk (firstVertexEdgewiseRestriction_source_vertex p c))
    (congrArg HomotopyCategory.mk (firstVertexEdgewiseRestriction_target_vertex p c))
    (congrArg HomotopyCategory.mk (firstVertexOppositePre_source_vertex p c))
    (congrArg HomotopyCategory.mk (firstVertexOppositePre_target_vertex p c))
  exact hf.trans (congrArg₂ (fun e f => e ≪≫ f)
    (firstVertexEdgewiseRestrictionChart_eq p c) (firstVertexOppositePreChart_eq p c))

/-- 元の同じ指定成分は、同じ厳密 pullback 切断点の反転点を回収する。 -/
theorem firstVertexOppositeChart_pointHom (c : TransportSimplexCategory B)
    (v : (((relativeSectionEnrichedDiagram (transportSimplexDomainFunctor B)).obj c).obj
      (leftFibrationObjectOf p)).obj _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom ((pointedSpaceFiberVertexEquiv
      (((relativeSectionEnrichedDiagram (transportSimplexDomainFunctor B)).obj c).obj
        (leftFibrationObjectOf p))).symm v) ≫
      (straighteningFirstVertexSectionChart (leftFibrationObjectOf p) c).inv ≫
        (firstVertexOppositeChart p c).hom =
    _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom ((pointedSpaceFiberVertexEquiv
      (kanObjectOpFunctor.obj ((leftStrictTransportFunctor
        (pullback.snd p (transportSimplexFirstVertexMap B))).obj c))).symm
          (SSet.opObjEquiv.symm ((firstVertexStrictSectionMap p c).app (Opposite.op ⦋0⦌) v))) := by
  have hp := firstVertexRestrictionChart_pointHom_strictSection (leftFibrationObjectOf p) c v
  have he := congrArg (fun m => m ≫
    (_root_.SerrePositivity.InfinityCategories.Stable.Transport.strictTransportOppositeComponentIso
      (pullback.snd p (transportSimplexFirstVertexMap B)) c).hom) hp
  simp only [Category.assoc] at he
  have ho := strictTransportOppositeComponentIso_pointHom
    (pullback.snd p (transportSimplexFirstVertexMap B)) c
    ((firstVertexStrictSectionMap p c).app (Opposite.op ⦋0⦌) v)
  rw [firstVertexOppositeChart_factor]
  simp only [Iso.trans_hom]
  exact he.trans ho

end SerrePositivity.KST.Fibration
