module
public import SerrePositivity.KST.Fibration.StraighteningUnderRealizationChart
public import SerrePositivity.KST.Fibration.RelativeSectionBaseChangeBackwardPoint

/-! # 元の初頂点 pullback 切断比較を、同じ指定係数成分へ戻す -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {B : SSet.{u}}

/-- 元の初頂点底変換比較は、元の相対切断比較の端点だけを表示変更する。 -/
theorem transportUnderBaseChangeRealizationIso_heq :
    HEq (transportSimplexUnderBaseChangeRealizationIso B)
      (relativeSectionBaseChangeRealizationIso (transportSimplexFirstVertexMap B)
        (strictTransportDomains (TransportSimplexCategory B))) := by
  unfold transportSimplexUnderBaseChangeRealizationIso
  dsimp only [_root_.id]
  have hcast {α β : Sort (u + 2)} (h : α = β) (x : α) : HEq (Eq.mp h x) x := by
    cases h
    rfl
  exact (hcast _ _).trans (hcast _ _)

/-- 元の初頂点底変換の指定成分は、元の同じ相対切断比較の係数成分。 -/
theorem transportUnderBaseChangeComponent_heq_doubleMap
    (X : LeftFibrationObject B) (c : TransportSimplexCategory B) :
    HEq (relativeSectionBaseChangeComponentIso (transportSimplexFirstVertexMap B)
      (strictTransportDomains (TransportSimplexCategory B)) X c)
      (VertexIso.map (transportSimplexUnderBaseChangeRealizationIso B)
        (kanEnrichedDoubleEvaluation X c)) := by
  let k := transportSimplexFirstVertexMap B
  let A := strictTransportDomains (TransportSimplexCategory B)
  have hs := congrArg (fun f => leftFibrationInfinityBaseChange k ≫ f)
    (strictTransportDomains_realization (TransportSimplexCategory B)).symm
  have ht := congrArg (fun F => (relativeSectionEnrichedDiagram F).realization)
    (strictTransportDomains_firstVertex B).symm
  have hm := F2.vertexIso_map_heq_of_heq (transportSimplexUnderBaseChangeRealizationIso B)
    (relativeSectionBaseChangeRealizationIso k A)
    (congrArg functorVertex hs) (congrArg functorVertex ht)
    (transportUnderBaseChangeRealizationIso_heq (B := B)) (kanEnrichedDoubleEvaluation X c)
  exact (relativeSectionBaseChangeComponentIso_heq_doubleMap k A X c).trans hm.symm

/-- 同じ初頂点底変換の始域値は、元の pullback strict 切断空間。 -/
theorem transportUnderBaseChange_source_vertex
    (X : LeftFibrationObject B) (c : TransportSimplexCategory B) :
    (kanEnrichedDoubleEvaluation X c).app (Opposite.op ⦋0⦌)
        (functorVertex
          (leftFibrationInfinityBaseChange (transportSimplexFirstVertexMap B) ≫
            leftStraighteningCoherentMap (TransportSimplexCategory B))) =
      spaceInfinityVertex
        ((((relativeSectionEnrichedDiagram (strictTransportDomains
          (TransportSimplexCategory B))).precompose
            (leftFibrationBaseChangeEnriched
              (transportSimplexFirstVertexMap B))).obj c).obj X) := by
  let k := transportSimplexFirstVertexMap B
  have hs := congrArg (fun f => leftFibrationInfinityBaseChange k ≫ f)
    (strictTransportDomains_realization (TransportSimplexCategory B)).symm
  have hv := congrArg functorVertex hs
  have he := congrArg ((kanEnrichedDoubleEvaluation X c).app (Opposite.op ⦋0⦌)) hv
  exact he.trans (kanEnrichedDoubleEvaluation_precomp_vertex
    (relativeSectionEnrichedDiagram (strictTransportDomains (TransportSimplexCategory B)))
    (leftFibrationBaseChangeEnriched k) X c)

/-- 元の初頂点底変換同型の同じ成分を、元の二つの切断空間で表示する。 -/
def firstVertexUnderBaseChangeChart (X : LeftFibrationObject B)
    (c : TransportSimplexCategory B) :=
  F2.isoNormalizeEndpoints
    (VertexIso.map (transportSimplexUnderBaseChangeRealizationIso B)
      (kanEnrichedDoubleEvaluation X c))
    (congrArg HomotopyCategory.mk (transportUnderBaseChange_source_vertex X c))
    (congrArg HomotopyCategory.mk (kanEnrichedDoubleEvaluation_vertex
      (relativeSectionEnrichedDiagram (transportSimplexUnderDomains B)) X c))

/-- 元の同じ成分は、元の相対切断底変換の係数成分と厳密一致する。 -/
theorem firstVertexUnderBaseChangeChart_eq
    (X : LeftFibrationObject B) (c : TransportSimplexCategory B) :
    firstVertexUnderBaseChangeChart X c =
      relativeSectionBaseChangeComponentIso (transportSimplexFirstVertexMap B)
        (strictTransportDomains (TransportSimplexCategory B)) X c :=
  F2.isoNormalizeEndpoints_eq_of_heq _ _ _ _
    (transportUnderBaseChangeComponent_heq_doubleMap X c).symm

/-- 元の初頂点底変換の指定逆成分は、同じ厳密な pullback 持ち上げ点を回収する。 -/
theorem firstVertexUnderBaseChangeChart_backward_pointHom
    (X : LeftFibrationObject B) (c : TransportSimplexCategory B)
    (v : (((relativeSectionEnrichedDiagram (transportSimplexUnderDomains B)).obj c).obj X).obj
      _⦋0⦌) :
    cosliceFiberPointHom ((pointedSpaceFiberVertexEquiv
      (((relativeSectionEnrichedDiagram (transportSimplexUnderDomains B)).obj c).obj X)).symm v) ≫
      (firstVertexUnderBaseChangeChart X c).inv =
    cosliceFiberPointHom ((pointedSpaceFiberVertexEquiv
      ((((relativeSectionEnrichedDiagram (strictTransportDomains
        (TransportSimplexCategory B))).precompose
          (leftFibrationBaseChangeEnriched (transportSimplexFirstVertexMap B))).obj c).obj X)).symm
            ((relativeFunctorBaseChangeBackward X.val.hom (transportSimplexFirstVertexMap B)
              ((strictTransportDomains (TransportSimplexCategory B)).obj (Opposite.op c)).hom).app
                (Opposite.op ⦋0⦌) v)) := by
  rw [firstVertexUnderBaseChangeChart_eq]
  exact relativeSectionBaseChangeComponentIso_backward_pointHom
    (transportSimplexFirstVertexMap B) (strictTransportDomains (TransportSimplexCategory B)) X c v

end SerrePositivity.KST.Fibration
