module
public import SerrePositivity.InfinityCategories.Stable.ExcisionThetaInvertibleComposite
public import SerrePositivity.InfinityCategories.Stable.ExcisionCoreInputCriterion
public import SerrePositivity.InfinityCategories.Stable.ExcisionFullCoreConeChoice
public import SerrePositivity.InfinityCategories.Stable.ExcisionGridSuspensionParameters

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
namespace SerrePositivity.InfinityCategories

lemma excisionCoreOuter_isPullback_of_raw_suspension {X : SSet.{u}}
    (F : nerve ExcisionGridIndex.{u} ⟶ X)
    (hF : ∀ k : ((Δ[1] : SSet.{u}) ⊗ Δ[1]) _⦋0⦌,
      IsPullbackSquare (excisionRawSuspensionSquare F ≫ evaluateFunctorAt k)) :
    IsPullbackSquare (grid22Face (excisionGridCoreDiagram ≫
      (nerveMap excisionGridCoreInclusion ≫ nerveMap excisionGridMiddleInclusion ≫ F)) 1 1) := by
  have h := hF (stdSimplex.obj₀Equiv.symm 0, stdSimplex.obj₀Equiv.symm 0)
  rw [excisionRawSuspensionSquare_evaluate, excisionGridSuspensionAt_source] at h
  simpa only [grid22Face, pastingSquare, Category.assoc] using h

lemma excisionFullInput_isPullback_of_raw_suspension {X : SSet.{u}} [Quasicategory X]
    [HasFiniteLimits X] (F : nerve ExcisionGridIndex.{u} ⟶ X)
    (hF : ∀ k : ((Δ[1] : SSet.{u}) ⊗ Δ[1]) _⦋0⦌,
      IsPullbackSquare (excisionRawSuspensionSquare F ≫ evaluateFunctorAt k)) :
    IsPullbackSquare (excisionGridSquareEmbedding ≫ F) := by
  let G := nerveMap excisionGridCoreInclusion ≫ nerveMap excisionGridMiddleInclusion ≫ F
  obtain ⟨i, hi⟩ := HasFiniteLimits.hasLimit
    (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ G) 2 2))
  obtain ⟨c, hc, hr, _⟩ := exists_excisionFullLimitCone_of_input F i hi
  have := hasFiniteLimits_functorCategory ((Δ[1] : SSet.{u}) ⊗ Δ[1]) X
  obtain ⟨d, hd⟩ := HasFiniteLimits.hasLimit
    (pullbackCospan (excisionRawSuspensionSquare (excisionReplaceInitial c)))
  obtain ⟨e, he, z, v, hv⟩ := excisionComparison_theta_invertible_postcomp
    F i hi c hc hr d hd hF
  let a := Classical.choice (hi.nonempty_edge
    (pullbackCone (grid22Face (excisionGridCoreDiagram ≫ G) 2 2)))
  let b := Classical.choice (he.nonempty_edge
    (pullbackCone (grid22Face (excisionGridCoreDiagram ≫ G) 1 1)))
  have ho : IsPullbackSquare (grid22Face (excisionGridCoreDiagram ≫ G) 1 1) :=
    excisionCoreOuter_isPullback_of_raw_suspension F hF
  have hb : IsInvertibleEdge b := isIso_of_isTerminal ho.isTerminalHo he.isTerminalHo _
  have h := excisionCoreInput_isPullback_of_comparison_factors G i hi e he a b
    (hb.map (sliceOverProjection
      (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ G) 1 1)))) v hv
  have hsq : grid22Face (excisionGridCoreDiagram ≫ G) 2 2 =
      excisionGridSquareEmbedding ≫ F := by
    have hh := congrArg (fun q ↦ q ≫ G) excisionGridCoreDiagram_lowerLeft.{u}
    simpa only [grid22Face, pastingSquare, excisionGridSquareEmbedding, G,
      Category.assoc] using hh
  rw [hsq] at h
  exact h

end SerrePositivity.InfinityCategories
