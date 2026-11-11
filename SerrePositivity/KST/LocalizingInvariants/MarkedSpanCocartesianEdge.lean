module

public import SerrePositivity.KST.LocalizingInvariants.SpanEndpointCocartesian
public import SerrePositivity.KST.LocalizingInvariants.FixedSpanApexComparison

/-!
概要：分母付き span の始点で可逆な射は、二つの終点への制限に対して cocartesian。
方針：元の span の外ホーン充填を使い、全頂点を既存のホーン族から回収する。
規約：分母集合に閉性の条件を課さない。使われ方：固定第一終点の族の輸送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

lemma markedSpanApex_evaluation (X : SSet.{u}) (W : Set (X _⦋1⦌)) :
    markedSpanApex X W = markedSpanInclusion X W ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt spanApexVertex := by
  rw [markedSpanApex, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.stable_pre_evaluateFunctorAt]
  rfl

lemma hasCocartesianHornLifting_markedSpanBoundary_of_apex
    {X : SSet.{u}} [Quasicategory X] (W : Set (X _⦋1⦌))
    {f g : (markedSpans X W) _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj (markedSpans X W)) f g)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (e.map ((truncation 2).map (markedSpanApex X W)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.HasCocartesianHornLifting (markedSpanBoundary X W) e := by
  let r := markedSpanInclusion X W
  let e' := e.map ((truncation 2).map r)
  have he' : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge
      (e'.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt spanApexVertex))) := by
    have h := congrArg (fun k : markedSpans X W ⟶ X => k.app (Opposite.op ⦋1⦌) e.edge)
      (markedSpanApex_evaluation X W)
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr h).mp he
  have hc := hasCocartesianHornLifting_spanEndpointRestriction_of_apex e' he'
  intro m σ β hσ hw
  have hs : (σ ≫ r).app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge m) = e'.edge := by
    exact congrArg (r.app (Opposite.op ⦋1⦌)) hσ
  have hw' : (σ ≫ r) ≫ (pre spanEndpointInclusion).app X = (horn (m + 2) 0).ι ≫ β := by
    change (σ ≫ markedSpanInclusion X W) ≫ (pre spanEndpointInclusion).app X = _
    rw [Category.assoc, ← markedSpanBoundary_restriction]
    exact hw
  obtain ⟨G, hG, hGr⟩ := hc m (σ ≫ r) β hs hw'
  have hv : ∀ v : (Δ[m + 2] : SSet.{u}) _⦋0⦌,
      spanLeftEdge (G.app (Opposite.op ⦋0⦌) v) ∈ W := by
    intro v
    let w : (horn (m + 2) 0 : SSet.{u}) _⦋0⦌ := ⟨v, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertex_mem_horn m 0 v⟩
    have h := congrArg (fun k => k.app (Opposite.op ⦋0⦌) w) hG
    have hp := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex (σ.app (Opposite.op ⦋0⦌) w)
    change G.app (Opposite.op ⦋0⦌) v = (σ.app (Opposite.op ⦋0⦌) w).val at h
    exact h.symm ▸ hp
  let F := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift (fun v => spanLeftEdge v ∈ W) G hv
  have hF : F ≫ r = G := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _
  refine ⟨F, ?_, ?_⟩
  · have : Mono r := by dsimp [r, markedSpanInclusion]; infer_instance
    apply (cancel_mono r).mp
    rw [Category.assoc, hF]
    exact hG
  · rw [markedSpanBoundary_restriction, ← Category.assoc, hF]
    exact hGr

end SerrePositivity.KST.LocalizingInvariants
