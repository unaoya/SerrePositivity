module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.PrecompositionCriterion
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionEquivalence
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：元の局所化が反転する辺の範囲内で、指定辺集合を拡大しても局所化である。
方針：新旧の反転関手圏の全包含と、元の前合成の充満忠実性・本質的全射性を使う。
規約：反射・随伴・局所化存在の仮定を追加しない。
使われ方：D-16 の局所化の飽和への移行。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
/-- 概要：元の局所化の反転辺内での指定集合の拡大は同じ局所化を表す。
方針：新旧の全反転関手圏を比較。規約：同じ F。使われ方：飽和への移行。 -/
@[kerodon 02LT]
lemma IsLocalization.of_subset_invertedEdges {X D : SSet.{u}} {F : X ⟶ D}
    {W W' : Set (X _⦋1⦌)} (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization F W)
    (hWW' : W ⊆ W') (hW' : W' ⊆ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertedEdges F) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization F W' := by
  obtain ⟨hW, hF⟩ := hF
  refine ⟨hW', fun E _ ↦ ?_⟩
  let U := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition F W hW E
  let U' := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition F W' hW' E
  let S : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors X E W' : SSet.{u}) ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors X E W : SSet.{u}) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsInvertingFunctorVertex X E W) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors X E W').ι (by
      intro v
      have hv : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsInvertingFunctorVertex X E W' v.val := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex v
      exact fun s hs ↦ hv (hWW' hs))
  have hS : S ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors X E W).ι = (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors X E W').ι :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _
  have hcomp : U' ≫ S = U := by
    apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors X E W).ι).mp
    rw [Category.assoc, hS]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition_ι F W' hW' E).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition_ι F W hW E).symm
  have hSff : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful S := by
    apply (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι ((ihom X).obj E)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsInvertingFunctorVertex X E W)).cancel_right
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (S ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors X E W).ι)
    rw [hS]
    exact _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι ((ihom X).obj E)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsInvertingFunctorVertex X E W')
  have hU : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence U := hF E
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective
  · apply hSff.cancel_right
    rw [hcomp]
    exact hU.isFullyFaithful
  · intro b
    obtain ⟨a, ⟨e⟩⟩ := hU.choose.isEssentiallySurjective (S.app (Opposite.op ⦋0⦌) b)
    have ha := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) a) hcomp
    let e' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (S.app (Opposite.op ⦋0⦌) (U'.app (Opposite.op ⦋0⦌) a))
        (S.app (Opposite.op ⦋0⦌) b) :=
      eqToIso (congrArg HomotopyCategory.mk ha) ≪≫ e
    exact ⟨a, ⟨hSff.preimageVertexIso e'⟩⟩

/-- 概要：元の局所化は、その反転する全ての辺についても局所化である。
方針：反転辺の全体への拡大。規約：同じ F。使われ方：飽和集合の公開。 -/
@[kerodon 04JH]
lemma IsLocalization.saturate {X D : SSet.{u}} {F : X ⟶ D}
    {W : Set (X _⦋1⦌)} (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization F W) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization F (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertedEdges F) :=
  hF.of_subset_invertedEdges hF.choose (Set.Subset.refl _)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
