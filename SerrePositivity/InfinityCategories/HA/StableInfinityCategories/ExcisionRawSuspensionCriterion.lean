module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionThetaInvertibleComposite
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionCoreInputCriterion
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionFullCoreConeChoice
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridSuspensionParameters

/-!
概要：四つの実 suspension 面の引き戻し性から、元の押し出しの像の普遍性を導く。
方針：全 cospan の厳密保存、同じ θ と対角合成、元の入力面の極限錐を接続する。
規約：標的の零対象や一般安定性は仮定しない。使われ方：一般切除・loop 同値判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

lemma excisionCoreOuter_isPullback_of_raw_suspension {X : SSet.{u}}
    (F : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u} ⟶ X)
    (hF : ∀ k : ((Δ[1] : SSet.{u}) ⊗ Δ[1]) _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionRawSuspensionSquare F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.grid22Face (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreDiagram ≫
      (nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreInclusion ≫ nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridMiddleInclusion ≫ F)) 1 1) := by
  have h := hF (stdSimplex.obj₀Equiv.symm 0, stdSimplex.obj₀Equiv.symm 0)
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionRawSuspensionSquare_evaluate, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSuspensionAt_source] at h
  simpa only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.grid22Face, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare, Category.assoc] using h

lemma excisionFullInput_isPullback_of_raw_suspension {X : SSet.{u}} [Quasicategory X]
    [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits X] (F : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u} ⟶ X)
    (hF : ∀ k : ((Δ[1] : SSet.{u}) ⊗ Δ[1]) _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionRawSuspensionSquare F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSquareEmbedding ≫ F) := by
  let G := nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreInclusion ≫ nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridMiddleInclusion ≫ F
  obtain ⟨i, hi⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits.hasLimit
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.grid22Face (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreDiagram ≫ G) 2 2))
  obtain ⟨c, hc, hr, _⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exists_excisionFullLimitCone_of_input F i hi
  have := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.hasFiniteLimits_functorCategory ((Δ[1] : SSet.{u}) ⊗ Δ[1]) X
  obtain ⟨d, hd⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits.hasLimit
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionRawSuspensionSquare (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionReplaceInitial c)))
  obtain ⟨e, he, z, v, hv⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionComparison_theta_invertible_postcomp
    F i hi c hc hr d hd hF
  let a := Classical.choice (hi.nonempty_edge
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.grid22Face (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreDiagram ≫ G) 2 2)))
  let b := Classical.choice (he.nonempty_edge
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.grid22Face (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreDiagram ≫ G) 1 1)))
  have ho : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.grid22Face (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreDiagram ≫ G) 1 1) :=
    excisionCoreOuter_isPullback_of_raw_suspension F hF
  have hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge b := isIso_of_isTerminal ho.isTerminalHo he.isTerminalHo _
  have h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreInput_isPullback_of_comparison_factors G i hi e he a b
    (hb.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.grid22Face (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreDiagram ≫ G) 1 1)))) v hv
  have hsq : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.grid22Face (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreDiagram ≫ G) 2 2 =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSquareEmbedding ≫ F := by
    have hh := congrArg (fun q ↦ q ≫ G) _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreDiagram_lowerLeft.{u}
    simpa only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.grid22Face, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSquareEmbedding, G,
      Category.assoc] using hh
  rw [hsq] at h
  exact h

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
