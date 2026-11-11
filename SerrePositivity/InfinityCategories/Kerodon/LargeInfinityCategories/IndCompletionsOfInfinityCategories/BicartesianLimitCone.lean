module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.FiniteHornDiagramPresentation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ConeCompletionBaseIso
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.CospanSquareCompletion
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.YonedaCospanSquareFamily
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.FiniteLimitsColimits
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.LimitConeDiagramComparison
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SquareFunctorTransport

/-!
概要：安定な C の Ind の指定 cospan は、実押し出しでもある極限全錐を持つ。
方針：同じ単一 filtered 表示の全極限錐族を補完し、両普遍性を元の図式へ輸送する。
規約：明示交換入力と C の有限極限存在を保持し、元の全図式を結論する。
使われ方：I-2 c の Ind の零角列の一致と安定性。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 指定した元の cospan の極限全錐を、同時に実押し出し四角形として構成する。 -/
lemma ind_exists_bicartesianLimitCone (κ : Cardinal.{u}) [Fact κ.IsRegular]
    (hκ : Cardinal.aleph0 ≤ κ) (hex : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndFiniteLimitExchangeInput.{u})
    {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits C]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj (horn 2 2) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C) :
    ∃ d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone D, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone d ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare ((_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.uliftCospanSquareReadingIso.{u, u + 1}).inv ≫ d.val) := by
  obtain ⟨I, hI, hfiltered, a, d0, hdv, hd⟩ :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ind_cospan_has_singleFilteredDiagramPresentation κ D
  letI := hI
  letI := hfiltered
  obtain ⟨l, hl, hlim⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.exists_yoneda_finiteLimit_coneFamily a
  let p := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYonedaConeFamily κ l
  obtain ⟨c, hc, hp, hinc⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.exists_indFunctor_kappaFiltered_colimit κ p
  have hr (i : I _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indInclusionPresheaf κ C)
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorVertexCone (p.app (Opposite.op ⦋0⦌) (ULift.up i)))) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYonedaConeFamily_inclusion_isLimit κ l (fun i => (hlim i).1) i
  have ht := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ind_filteredLimitCone_isLimit κ hκ (hex.exchange (horn 2 2)) p c hinc hr
  let r := (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.uliftCospanSquareReadingIso.{u, u + 1}).inv
  have hs (i : ((SSet.uliftFunctor.{u + 1, u}).obj I) _⦋0⦌) :
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (r ≫ (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorVertexCone (p.app (Opposite.op ⦋0⦌) i)).val) := by
    obtain ⟨i⟩ := i
    have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYonedaCospanSquareFamily_bicartesian κ hκ hex l
      (fun i => (hlim i).1) i).2
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm
      (((pre r).app (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C)).app _ (p.app _ (ULift.up i)))) at h
    rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorVertexMap_precomp] at h
    exact h
  have hb := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ind_cospanSquare_completion_isPushout κ p c hp hs
  letI : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C) := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ind_hasFiniteLimits κ hκ hex C
  letI : ((SSet.uliftFunctor.{u + 1, u}).obj (horn 2 2 : SSet.{u})).Finite :=
    SSet.finite_of_iso (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftHornIso.{u, u + 1} 2 2).symm
  obtain ⟨d, hdl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits.hasLimit D
  have e := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indConeCompletionBaseIso κ a l hl c hp D d0 hd hdv
  have ec := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.limitConeDiagramIso (fun q => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits.hasLimit q)
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorVertexCone c.vertex) d ht.1 hdl e
  exact ⟨d, hdl, hb.of_functorIso (ec.precomp r)⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
