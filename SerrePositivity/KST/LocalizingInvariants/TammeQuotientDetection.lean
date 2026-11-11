module

public import SerrePositivity.KST.LocalizingInvariants.TammeQuotientCandidate
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.InvertingFunctorIsoInvariance

/-!
概要：一般商候補が反転する元の辺を厳密に同定し、核の像を零対象の像と比較する。
方針：元の差の coherent な因子化で反転を反映し、零始点の辺の可逆性へ適用する。
規約：商内の零対象性はまだ主張しない。使われ方：商の pointed 性と真の核の後続証明。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable {C D E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)

lemma tammeQuotientMap_invertedEdges :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertedEdges (tammeQuotientMap p q) = tammeLocalizingEdges p q := by
  apply Set.Subset.antisymm
  · have h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges (tammeQuotientMap p q ≫ tammeQuotientComparison p q)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertedEdges (tammeQuotientMap p q)) :=
      (show _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges (tammeQuotientMap p q) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertedEdges (tammeQuotientMap p q)) from
        Set.Subset.refl _).comp (tammeQuotientComparison p q)
    unfold _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges at h
    rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.invertedEdges_functorIso (tammeQuotientComparisonIso p q)] at h
    rw [tammeLocalizingEdges_eq]
    exact h
  · exact (tammeQuotient_isLocalization p q).choose

/-- 核の対象は、商候補で選んだ零対象の像と同型になる。逆も元の差の像で検出できる。 -/
lemma tammeQuotient_zeroImageIso_iff (x : (laxCategory p q).obj _⦋0⦌) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((tammeQuotientMap p q).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.chosenZeroVertex (laxCategory p q).obj).vertex)
      ((tammeQuotientMap p q).app (Opposite.op ⦋0⦌) x)) ↔
        _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((laxDifference p q).app (Opposite.op ⦋0⦌) x) := by
  let z := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.chosenZeroVertex (laxCategory p q).obj
  have hz := laxDifference_preservesZero p q z.vertex z.isZero
  constructor
  · rintro ⟨e⟩
    let d := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorIso.app (tammeQuotientComparisonIso p q) z.vertex).symm ≪≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e (tammeQuotientComparison p q) ≪≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorIso.app (tammeQuotientComparisonIso p q) x
    exact hz.of_vertexIso d
  · intro hx
    obtain ⟨e⟩ := z.isInitial.nonempty_edge x
    have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (e.map ((truncation 2).map (laxDifference p q))) := by
      change IsIso (SSet.Truncated.HomotopyCategory.homMk _)
      have hh := hx.2.isTerminalHo.hom_ext
        (SSet.Truncated.HomotopyCategory.homMk (e.map ((truncation 2).map (laxDifference p q))))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.terminalVertexIso hz.2 hx.2).hom
      rw [hh]
      infer_instance
    have hw : e.edge ∈ tammeLocalizingEdges p q := by
      rw [tammeLocalizingEdges_eq]
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := e.map ((truncation 2).map (laxDifference p q)))
        (f := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex e.edge).map ((truncation 2).map (laxDifference p q))) rfl).mp hi
    have hq := (tammeQuotient_isLocalization p q).choose hw
    have hiq : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (e.map ((truncation 2).map (tammeQuotientMap p q))) :=
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := e.map ((truncation 2).map (tammeQuotientMap p q)))
        (f := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex e.edge).map ((truncation 2).map (tammeQuotientMap p q))) rfl).mpr hq
    have : IsIso (SSet.Truncated.HomotopyCategory.homMk
      (e.map ((truncation 2).map (tammeQuotientMap p q)))) := hiq
    exact ⟨asIso (SSet.Truncated.HomotopyCategory.homMk
      (e.map ((truncation 2).map (tammeQuotientMap p q))))⟩

lemma tammeQuotient_zeroImageIso_iff_essentialImage (x : (laxCategory p q).obj _⦋0⦌) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((tammeQuotientMap p q).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.chosenZeroVertex (laxCategory p q).obj).vertex)
      ((tammeQuotientMap p q).app (Opposite.op ⦋0⦌) x)) ↔
        x ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage (pullbackInclusion p q) :=
  (tammeQuotient_zeroImageIso_iff p q x).trans (laxDifference_kernel p q x)

end SerrePositivity.KST.LocalizingInvariants
