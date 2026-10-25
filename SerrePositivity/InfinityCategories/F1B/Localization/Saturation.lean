module

public import SerrePositivity.InfinityCategories.F1B.Localization.PrecompositionCriterion
public import SerrePositivity.InfinityCategories.Core.PrecompositionEquivalence

/-!
概要：元の局所化が反転する辺の範囲内で、指定辺集合を拡大しても局所化である。
方針：新旧の反転関手圏の全包含と、元の前合成の充満忠実性・本質的全射性を使う。
規約：反射・随伴・局所化存在の仮定を追加しない。
使われ方：D-16 の局所化の飽和への移行。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
/-- 概要：元の局所化の反転辺内での指定集合の拡大は同じ局所化を表す。
方針：新旧の全反転関手圏を比較。規約：同じ F。使われ方：飽和への移行。 -/
lemma IsLocalization.of_subset_invertedEdges {X D : SSet.{u}} {F : X ⟶ D}
    {W W' : Set (X _⦋1⦌)} (hF : IsLocalization F W)
    (hWW' : W ⊆ W') (hW' : W' ⊆ invertedEdges F) : IsLocalization F W' := by
  obtain ⟨hW, hF⟩ := hF
  refine ⟨hW', fun E _ ↦ ?_⟩
  let U := localizationPrecomposition F W hW E
  let U' := localizationPrecomposition F W' hW' E
  let S : (invertingFunctors X E W' : SSet.{u}) ⟶ (invertingFunctors X E W : SSet.{u}) :=
    fullSubcomplexLift (IsInvertingFunctorVertex X E W) (invertingFunctors X E W').ι (by
      intro v
      have hv : IsInvertingFunctorVertex X E W' v.val := fullSubcomplexOnVertices_vertex v
      exact fun s hs ↦ hv (hWW' hs))
  have hS : S ≫ (invertingFunctors X E W).ι = (invertingFunctors X E W').ι :=
    fullSubcomplexLift_ι _ _ _
  have hcomp : U' ≫ S = U := by
    apply (cancel_mono (invertingFunctors X E W).ι).mp
    rw [Category.assoc, hS]
    exact (localizationPrecomposition_ι F W' hW' E).trans
      (localizationPrecomposition_ι F W hW E).symm
  have hSff : IsFullyFaithful S := by
    apply (isFullyFaithful_fullSubcomplexOnVertices_ι ((ihom X).obj E)
      (IsInvertingFunctorVertex X E W)).cancel_right
    change IsFullyFaithful (S ≫ (invertingFunctors X E W).ι)
    rw [hS]
    exact isFullyFaithful_fullSubcomplexOnVertices_ι ((ihom X).obj E)
      (IsInvertingFunctorVertex X E W')
  have hU : IsQCatEquivalence U := hF E
  apply isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective
  · apply hSff.cancel_right
    rw [hcomp]
    exact hU.isFullyFaithful
  · intro b
    obtain ⟨a, ⟨e⟩⟩ := hU.choose.isEssentiallySurjective (S.app (Opposite.op ⦋0⦌) b)
    have ha := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) a) hcomp
    let e' : VertexIso (S.app (Opposite.op ⦋0⦌) (U'.app (Opposite.op ⦋0⦌) a))
        (S.app (Opposite.op ⦋0⦌) b) :=
      eqToIso (congrArg HomotopyCategory.mk ha) ≪≫ e
    exact ⟨a, ⟨hSff.preimageVertexIso e'⟩⟩

/-- 概要：元の局所化は、その反転する全ての辺についても局所化である。
方針：反転辺の全体への拡大。規約：同じ F。使われ方：飽和集合の公開。 -/
lemma IsLocalization.saturate {X D : SSet.{u}} {F : X ⟶ D}
    {W : Set (X _⦋1⦌)} (hF : IsLocalization F W) :
    IsLocalization F (invertedEdges F) :=
  hF.of_subset_invertedEdges hF.choose (Set.Subset.refl _)

end SerrePositivity.InfinityCategories
