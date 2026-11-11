module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.InitialEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.PresheafSubcategory
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.YonedaPresheafEvaluation
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseZeroObjects

/-!
概要：元の小さい圏の始対象は、Indκ への同じ Yoneda 因子化でも始対象。
方針：Ind の評価値の終対象性を Yoneda の全写像空間比較と全部分包含で反映する。
規約：ℵ₀ ≤ κ を明示。使われ方：安定性に先立つ零対象の構成。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 可縮 Kan 複体の元の頂点の終対象性を使い、同じ複体の宇宙持ち上げも可縮とする。 -/
lemma isContractibleKan_ulift {K : SSet.{u}} (hK : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan K) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan ((SSet.uliftFunctor.{v, u}).obj K) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.isContractibleKan_of_nonempty_of_all_terminal
  · exact hK.nonempty.map ULift.up
  · rintro ⟨x⟩
    exact (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.isTerminalVertex_iff_ulift x).mp (hK.isTerminalVertex x)

/-- 同じ Ind Yoneda 頂点を前層へ含めると、元の表現可能前層の頂点そのもの。 -/
lemma indYoneda_vertex_inclusion (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C]
    (z : C _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indInclusionPresheaf κ C).app (Opposite.op ⦋0⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ C).app (Opposite.op ⦋0⦌) (ULift.up z)) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity z) := by
  have h := congrArg (fun f => f.app (Opposite.op ⦋0⦌) (ULift.up z))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda_inclusion κ C)
  exact h.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap_vertex z)

/-- 同じ元の Yoneda 因子化は、始対象を Indκ の始対象へ送る。 -/
lemma indYoneda_isInitial_of_initial (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ)
    {C : SSet.{u}} [Quasicategory C] {z : C _⦋0⦌} (hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ C).app (Opposite.op ⦋0⦌) (ULift.up z)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanIsInitialVertex_of_pinchedHom_isContractibleKan
  intro w
  let F := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafInfinityObjectEquiv C).symm w.val
  have hw : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F = w.val := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafInfinityObjectEquiv C).apply_symm_apply w.val
  have ht := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indVertex_evaluation_isTerminal_of_initial κ hκ hz
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex w)
  have ht' : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (F.app (Opposite.op ⦋0⦌)
      (ULift.up (SSet.opObjEquiv.symm z))) := by
    rw [← hw] at ht
    have he := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex (ULift.up (SSet.opObjEquiv.symm z)) F
    exact (congrArg (fun s => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex s) he).mp ht
  have hU := isContractibleKan_ulift.{u, u + 1}
    ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spaceInfinity_isTerminal_iff_value_isContractibleKan _).mp ht')
  have hm := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaPresheafEvaluationEquivalence z F).isContractibleKan_iff.mpr hU
  apply ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indInclusionPresheaf_isFullyFaithful κ C) _ w).isContractibleKan_iff.mpr
  rw [indYoneda_vertex_inclusion]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity z)) w.val)
  rw [← hw]
  exact hm

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
