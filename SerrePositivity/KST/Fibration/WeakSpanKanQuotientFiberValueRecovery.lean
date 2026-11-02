module
public import SerrePositivity.KST.Fibration.WeakSpanKanQuotientValueCancellation
public import SerrePositivity.InfinityCategories.HomotopyLimits.FilteredExchange.SpaceEdgeTransportValue
public import SerrePositivity.InfinityCategories.F1.Universe.QCatEquivalence

/-!
概要：元の商上の実 fiber 比較を、既存指定値同型で元の Kan 値へ正規化する。
方針：同じ全 fiber transport 比較と元の実二辺の打ち消しを合成し、元の宇宙へ降ろす。
規約：元の実比較・既存値同型・全 fiber を固定する。
使われ方：K-B-S の実全族写像が元の全 Kan 単位を回収することの証明。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
attribute [local instance] vertexFiber_kanComplex_of_leftFibration
variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
  (h : IsVerdierSequence i q) (x : B.obj _⦋0⦌) (c : TransportSimplexCategory B.obj)

/-- 概要：同じ商比較の全 fiber 作用は既存指定値同型で元の fiber 値比較へ戻る。
方針：同じ実 transport と既存値比較の自然性・指定二辺の打ち消しを使う。
規約：別の値比較や点別の同型へ置換しない。
使われ方：元の全族単位と既存指定恒等点の正規化。 -/
def weakSpanKanQuotientSimplexFiberValueRecovery :
    FunctorIso
      (weakSpanKanQuotientSimplexFiberMap h x c ≫
        (weakSpanKanQuotientFiberValueEquivalence h x c).hom)
      (smallLeftUnstraighteningFiberValueEquivalence (weakSpanKanCoherentDiagram i x)
        (nerveVertex c)).hom := by
  let F := weakSpanKanCoherentDiagram i x
  let Q := weakSpanKanQuotientDiagram h x
  let b := nerveVertex c
  let y := (transportSimplexFirstVertexMap B.obj ≫ q.hom).app (Opposite.op ⦋0⦌) b
  let a := F.app (Opposite.op ⦋0⦌) (ULift.up b)
  let z := Q.app (Opposite.op ⦋0⦌) (ULift.up y)
  let e := weakSpanKanQuotientForwardValueEdge h x c
  let d := weakSpanKanQuotientValueEdge h x c
  let fe := F2.spaceInfinityEdgeValue e
  let fd := F2.spaceInfinityEdgeValue d
  let sF := (smallLeftUnstraighteningFiberIso F b).hom ≫
    (leftUnstraighteningFiberIso F (ULift.up b)).hom
  let sQ := (smallLeftUnstraighteningFiberIso Q y).hom ≫
    (leftUnstraighteningFiberIso Q (ULift.up y)).hom
  let vF := (pointedSpaceFiberValueEquivalence a).hom
  let vQ := (pointedSpaceFiberValueEquivalence z).hom
  have hT := (weakSpanKanQuotientSimplexFiberTransportIso h x c).postcomp
    (vQ ≫ (SSet.uliftFunctor.{u + 1, u}).map fd)
  have hV := (FunctorIso.precomp (F2.spaceInfinityEdgeTransportValueIso e).symm sF).postcomp
    ((SSet.uliftFunctor.{u + 1, u}).map fd)
  have hc := weakSpanKanQuotientValueCancellationHomotopy h x c
  change SSet.Homotopy (𝟙 (spaceInfinityObject a).obj)
    (fe ≫ fd) at hc
  have hC := FunctorIso.precomp
    (FunctorIso.ulift.{u, u + 1} (functorIsoOfSimplicialHomotopy hc)).symm (sF ≫ vF)
  simp only [Functor.map_comp, Functor.map_id, Category.comp_id, Category.assoc] at hC
  simp only [Category.assoc] at hT hV
  have hIso := hT ≪≫ hV ≪≫ hC
  have hF := uliftMorphismDown_lift
    (smallLeftUnstraighteningLiftedFiberValueEquivalence F b).hom
  have hQ := uliftMorphismDown_lift
    (smallLeftUnstraighteningLiftedFiberValueEquivalence Q y).hom
  change (SSet.uliftFunctor.{u + 1, u}).map
    (smallLeftUnstraighteningFiberValueEquivalence F b).hom = sF ≫ vF at hF
  change (SSet.uliftFunctor.{u + 1, u}).map
    (smallLeftUnstraighteningFiberValueEquivalence Q y).hom = sQ ≫ vQ at hQ
  have h' : FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map
        (weakSpanKanQuotientSimplexFiberMap h x c ≫
          (weakSpanKanQuotientFiberValueEquivalence h x c).hom))
      ((SSet.uliftFunctor.{u + 1, u}).map
        (smallLeftUnstraighteningFiberValueEquivalence F b).hom) := by
    change FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map
        (weakSpanKanQuotientSimplexFiberMap h x c ≫
          (smallLeftUnstraighteningFiberValueEquivalence Q y).hom ≫
            fd)) _
    rw [Functor.map_comp, Functor.map_comp, hF, hQ]
    simpa only [sF, sQ, Category.assoc] using! hIso
  have hd := functorIsoOfSimplicialHomotopy (unliftSimplicialHomotopy h'.simplicialHomotopy)
  simpa only [uliftMorphismDown_map] using! hd

end SerrePositivity.KST.Fibration
