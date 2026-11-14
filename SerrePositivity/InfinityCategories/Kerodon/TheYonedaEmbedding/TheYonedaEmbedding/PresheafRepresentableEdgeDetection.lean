module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.YonedaPresheafEvaluationPostcomposition
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorEdgePointwise
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalenceCalculus
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.Reflection

/-!
概要：表現可能前層からの元の写像空間の後合成が、前層の辺の可逆性を検出する。
方針：元の Yoneda 評価の全族自然性で各点の Kan 射に移し、点ごとの可逆性を適用する。
規約：自然性や検出性を入力に加えない。
使われ方：G14 の反映した表現可能生成族による検出。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors
open SerrePositivity.InfinityCategories.Project.FilteredExchange
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding

/-- 全表現可能前層からの後合成の同値性は、元の前層の辺の可逆性を検出する。 -/
lemma presheafEdge_isInvertible_of_representable_post {C : SSet.{u}} [Quasicategory C]
    (F G : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u})
    (e : SSet.Edge (functorVertex F) (functorVertex G))
    (h : ∀ y : C _⦋0⦌, IsQCatEquivalence
      (postcompose (functorVertex (representablePresheafInfinity y))
        (SSet.Truncated.HomotopyCategory.homMk e.toTruncated))) : IsInvertibleEdge e := by
  apply (isInvertibleEdge_iff_evaluateFunctorAt e.toTruncated).mpr
  rintro ⟨b⟩
  let y : C _⦋0⦌ := SSet.opObjEquiv b
  have hn := yonedaPresheafEvaluation_postcomposeIso y F G e
  have hc := ((h y).comp (yonedaPresheafEvaluation_isQCatEquivalence y G)).ofFunctorIso hn
  have hv := (yonedaPresheafEvaluation_isQCatEquivalence y F).cancel_left hc
  have hk := (isQCatEquivalence_ulift_iff_of_kan _).mp hv
  have hi := coherentKanEdge_isInvertible_of_isQCatEquivalence hk
  have he : IsInvertibleEdge (functorEdgeAt e (ULift.up b)).toTruncated := by
    have h' := (isInvertibleEdge_congr (spaceInfinityEdgeValue_edge
      (functorEdgeAt e (ULift.up (SSet.opObjEquiv.symm y))))).mp hi
    have hby : SSet.opObjEquiv.symm y = b :=
      (SSet.opObjEquiv : C.op _⦋0⦌ ≃ C _⦋0⦌).symm_apply_apply b
    change IsInvertibleEdge (functorEdgeAt e (ULift.up (SSet.opObjEquiv.symm y))).toTruncated at h'
    rw [hby] at h'
    exact h'
  exact (isInvertibleEdge_congr
    (e := (functorEdgeAt e (ULift.up b)).toTruncated)
    (f := e.toTruncated.map ((truncation 2).map (evaluateFunctorAt (ULift.up b)))) rfl).mp he

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
