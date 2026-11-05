module

public import SerrePositivity.KST.LocalizingInvariants.TammeQuotientCandidate
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.InvertingFunctorIsoInvariance

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
variable {C D E : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap D E)

lemma tammeQuotientMap_invertedEdges :
    invertedEdges (tammeQuotientMap p q) = tammeLocalizingEdges p q := by
  apply Set.Subset.antisymm
  · have h : InvertsEdges (tammeQuotientMap p q ≫ tammeQuotientComparison p q)
        (invertedEdges (tammeQuotientMap p q)) :=
      (show InvertsEdges (tammeQuotientMap p q) (invertedEdges (tammeQuotientMap p q)) from
        Set.Subset.refl _).comp (tammeQuotientComparison p q)
    unfold InvertsEdges at h
    rw [invertedEdges_functorIso (tammeQuotientComparisonIso p q)] at h
    rw [tammeLocalizingEdges_eq]
    exact h
  · exact (tammeQuotient_isLocalization p q).choose

/-- 核の対象は、商候補で選んだ零対象の像と同型になる。逆も元の差の像で検出できる。 -/
lemma tammeQuotient_zeroImageIso_iff (x : (laxCategory p q).obj _⦋0⦌) :
    Nonempty (VertexIso ((tammeQuotientMap p q).app (Opposite.op ⦋0⦌)
      (chosenZeroVertex (laxCategory p q).obj).vertex)
      ((tammeQuotientMap p q).app (Opposite.op ⦋0⦌) x)) ↔
        IsZeroVertex ((laxDifference p q).app (Opposite.op ⦋0⦌) x) := by
  let z := chosenZeroVertex (laxCategory p q).obj
  have hz := laxDifference_preservesZero p q z.vertex z.isZero
  constructor
  · rintro ⟨e⟩
    let d := (FunctorIso.app (tammeQuotientComparisonIso p q) z.vertex).symm ≪≫
      VertexIso.map e (tammeQuotientComparison p q) ≪≫
        FunctorIso.app (tammeQuotientComparisonIso p q) x
    exact hz.of_vertexIso d
  · intro hx
    obtain ⟨e⟩ := z.isInitial.nonempty_edge x
    have hi : IsInvertibleEdge (e.map ((truncation 2).map (laxDifference p q))) := by
      change IsIso (SSet.Truncated.HomotopyCategory.homMk _)
      have hh := hx.2.isTerminalHo.hom_ext
        (SSet.Truncated.HomotopyCategory.homMk (e.map ((truncation 2).map (laxDifference p q))))
        (terminalVertexIso hz.2 hx.2).hom
      rw [hh]
      infer_instance
    have hw : e.edge ∈ tammeLocalizingEdges p q := by
      rw [tammeLocalizingEdges_eq]
      exact (isInvertibleEdge_congr (e := e.map ((truncation 2).map (laxDifference p q)))
        (f := (edgeOfSimplex e.edge).map ((truncation 2).map (laxDifference p q))) rfl).mp hi
    have hq := (tammeQuotient_isLocalization p q).choose hw
    have hiq : IsInvertibleEdge (e.map ((truncation 2).map (tammeQuotientMap p q))) :=
      (isInvertibleEdge_congr (e := e.map ((truncation 2).map (tammeQuotientMap p q)))
        (f := (edgeOfSimplex e.edge).map ((truncation 2).map (tammeQuotientMap p q))) rfl).mpr hq
    have : IsIso (SSet.Truncated.HomotopyCategory.homMk
      (e.map ((truncation 2).map (tammeQuotientMap p q)))) := hiq
    exact ⟨asIso (SSet.Truncated.HomotopyCategory.homMk
      (e.map ((truncation 2).map (tammeQuotientMap p q))))⟩

lemma tammeQuotient_zeroImageIso_iff_essentialImage (x : (laxCategory p q).obj _⦋0⦌) :
    Nonempty (VertexIso ((tammeQuotientMap p q).app (Opposite.op ⦋0⦌)
      (chosenZeroVertex (laxCategory p q).obj).vertex)
      ((tammeQuotientMap p q).app (Opposite.op ⦋0⦌) x)) ↔
        x ∈ _root_.SerrePositivity.InfinityCategories.Stable.Verdier.essentialImage (pullbackInclusion p q) :=
  (tammeQuotient_zeroImageIso_iff p q x).trans (laxDifference_kernel p q x)

end SerrePositivity.KST.LocalizingInvariants
