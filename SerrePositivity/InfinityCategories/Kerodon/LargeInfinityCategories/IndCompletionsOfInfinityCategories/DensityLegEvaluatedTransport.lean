module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.DensityCanonicalTransportAtPoint
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.DensityIntervalAtLeg
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ElementsYonedaSliceInterval
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceIntervalVertices
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeVertexTriangles

/-!
概要：元の密度余錐の実脚を恒等点で評価した輸送の終値は、同じ要素の pointed 値と同型。
方針：元の密度の区間頂点を評価し、指定の実辺の輸送と照合する。
使われ方：離散前層の密度の脚の自然性。
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

variable {C : SSet.{u}} [Quasicategory C]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}) (x : C _⦋0⦌)

/-- 元の密度余錐の実脚を恒等点で評価した輸送の終値は、同じ要素の pointed 値と同型。
Kerodon §9.3（Tag 06FR）の密度比較。HTT 5.1.5.6 へ使う指定脚の輸送。 -/
lemma presheafDensityLeg_evaluatedTransport
    (s : (vertexFiber (smallRightUnstraighteningProjection F) x) _⦋0⦌) :
    let b := SSet.opObjEquiv.symm x
    let R := representablePresheafInfinity x
    let l := (coconeVertexLeg (presheafDensityCocone F) (ULift.up s.val)).ofEq
      (by
        have h : (smallRightUnstraighteningProjection F).app (Opposite.op ⦋0⦌) s.val = x :=
          s.property.trans (pinchedConstant_zero x)
        change (yonedaInfinityMap C).app (Opposite.op ⦋0⦌)
          (ULift.up ((smallRightUnstraighteningProjection F).app
            (Opposite.op ⦋0⦌) s.val)) = _
        rw [h, yonedaInfinityMap_vertex])
      (presheafDensityCocone_vertex F)
    let e := functorEdgeAt (F := R) (G := F) l (ULift.up b)
    let v := smallUnstraighteningPointedImage F b
      ((presheafRightFiberLeftIso F x).hom.app _ (SSet.opObjEquiv.symm s))
    Nonempty (VertexIso ((edgeTransport pointedSpaceProjection e).app _
        (canonicalYonedaPointedIdentity x)) v) := by
  intro b R l e v
  let ev := evaluateFunctorAt (X := (SSet.uliftFunctor.{u + 1, u}).obj C.op)
    (Y := SpaceInfinity.{u}) (ULift.up b)
  let a := presheafDensityCanonicalSourceValue x
  let z := F.app (Opposite.op ⦋0⦌) (ULift.up b)
  let q := canonicalYonedaPointedIdentity x
  let m := intervalMappingPostOfEq ev (functorVertex R) (functorVertex F)
    (evaluateFunctorAt_functorVertex _ _) (evaluateFunctorAt_functorVertex _ _)
  let t := parametrizedFiberTransport pointedSpaceProjection a z
  let H := m ≫ t ≫ evaluateFunctorAt q
  let w : (presheafDensityFiberParameter F x) _⦋0⦌ := ULift.up s
  have hLeg : (presheafElementsYonedaSliceInterval F x).app (Opposite.op ⦋0⦌) w =
      intervalMappingVertexOfEdge l := presheafElementsYonedaSliceInterval_at_leg F x s
  have hIso := VertexIso.map ((presheafDensityFiberIntervalIso F x).postcomp H)
    (evaluateFunctorAt w)
  simp only [evaluateFunctorAt_functorVertex] at hIso
  obtain ⟨hu⟩ := densityCanonicalTransport_at_native_point F x s
  have hv₀ : (presheafElementsYonedaSliceInterval F x ≫ H).app (Opposite.op ⦋0⦌) w =
      (evaluateFunctorAt q).app (Opposite.op ⦋0⦌)
        (t.app (Opposite.op ⦋0⦌) (intervalMappingVertexOfEdge e)) := by
    have hM : m.app (Opposite.op ⦋0⦌) (intervalMappingVertexOfEdge l) =
        intervalMappingVertexOfEdge e :=
      intervalMappingPostOfEq_vertex ev _ _ l
    simp only [H, NatTrans.comp_app, ConcreteCategory.comp_apply, hLeg]
    exact congrArg (fun z' => (evaluateFunctorAt q).app (Opposite.op ⦋0⦌)
      (t.app (Opposite.op ⦋0⦌) z')) hM
  have hEnd := VertexIso.map (parametrizedFiberTransport_at_edgeIso pointedSpaceProjection e)
    (evaluateFunctorAt q)
  rw [evaluateFunctorAt_functorVertex, evaluateFunctorAt_functorVertex] at hEnd
  have hCoe : functorVertex ((functorVertexEquiv _ _).symm
      (t.app (Opposite.op ⦋0⦌) (intervalMappingVertexOfEdge e))) =
      t.app (Opposite.op ⦋0⦌) (intervalMappingVertexOfEdge e) :=
    (functorVertexEquiv _ _).apply_symm_apply _
  have hPre := congrArg (fun z' => (evaluateFunctorAt q).app (Opposite.op ⦋0⦌) z') hCoe
  rw [evaluateFunctorAt_functorVertex] at hPre
  exact ⟨hEnd.symm ≪≫ eqToIso (congrArg HomotopyCategory.mk hPre) ≪≫
    eqToIso (congrArg HomotopyCategory.mk hv₀.symm) ≪≫ hIso ≪≫ hu⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
