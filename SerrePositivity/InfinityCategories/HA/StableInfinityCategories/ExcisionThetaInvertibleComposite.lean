module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionComparisonCospanEquivalence
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.FunctorEdgeBottomReadback
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionComparisonTheta
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PullbackComparisonDiagonalInvertible
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ArrowIsoPostcompTransport
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.FunctorFiniteLimits

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

lemma excisionComparison_theta_invertible_postcomp {X : SSet.{u}} [Quasicategory X]
    [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits X] (F : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u} ⟶ X)
    (i : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.grid22Face (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreDiagram ≫
      (nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreInclusion ≫ nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridMiddleInclusion ≫ F)) 2 2)))
    (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone i)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionFullPunctured) ≫ F))
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c)
    (hr : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.restrictJoinCone c (nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCorePuncturedToFull.toFunctor)).val =
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCorePuncturedLimitCone
        (nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreInclusion ≫ nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridMiddleInclusion ≫ F)
        i hi).val)
    (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionRawSuspensionSquare (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionReplaceInitial c))))
    (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone d)
    (hF : ∀ k : ((Δ[1] : SSet.{u}) ⊗ Δ[1]) _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionRawSuspensionSquare F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k)) :
    ∃ (e : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.grid22Face (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreDiagram ≫
        (nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreInclusion ≫ nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridMiddleInclusion ≫ F)) 1 1)))
      (he : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone e) (z : hoFunctor.obj X)
      (v : (HomotopyCategory.mk e.vertex : hoFunctor.obj X) ⟶ z),
      IsIso (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreComparisonEdge
        (nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreInclusion ≫ nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridMiddleInclusion ≫ F)
        i hi e he) ≫ v) := by
  let A := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionPullbackComparisonFamily c d hd
  have := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.hasFiniteLimits_functorCategory (Δ[1] : SSet.{u}) X
  obtain ⟨l, hl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits.hasLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan A)
  let t := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.functorPullbackComparisonEdge A l hl
  let Q := uncurry (SSet.yonedaEquiv.symm t.edge)
  have hdiag : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagonalArrow Q) :=
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.functorPullbackComparison_diagonal_isInvertible A l hl
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionPullbackComparisonFamily_source_isPullback c hc d hd)
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionComparison_cospan_isEquivalencePath c d hd hF)
  have hcomp : IsIso (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareBottomArrow Q) ≫
      Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareRightArrow Q)) := by
    rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareBottomRight_homMk_diagonal]
    exact hdiag
  obtain ⟨e, he, htheta⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionRawSuspensionComparison_source_theta F i hi c hr d hd
  have hb := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareBottomArrow_functorEdge_edge t
  have hb0 := hb.trans (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pullbackCone_vertex A))
  let k : ((Δ[1] : SSet.{u}) ⊗ Δ[1]) _⦋0⦌ :=
    (stdSimplex.obj₀Equiv.symm 0, stdSimplex.obj₀Equiv.symm 0)
  have hvertex := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.arrowFamilyOfFunctorEdge_vertex_edge
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.functorPullbackComparisonEdge (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionRawSuspensionSquare (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionReplaceInitial c))
      d hd) k
  have hraw : (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareBottomArrow Q).edge =
      ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.functorPullbackComparisonEdge
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionRawSuspensionSquare (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionReplaceInitial c)) d hd).map
          ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k))).edge := hb0.trans hvertex
  have heq := (Truncated.HomotopyCategory.congr_arrowMk_homMk _ _ hraw).trans htheta
  have h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isIso_comp_of_arrowMk_eq
    (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareBottomArrow Q))
    (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreComparisonEdge
      (nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreInclusion ≫ nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridMiddleInclusion ≫ F)
      i hi e he))
    (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareRightArrow Q)) heq hcomp
  exact ⟨e, he, (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex Q 1 1) : hoFunctor.obj X),
    eqToHom (congrArg Arrow.right heq).symm ≫
      Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareRightArrow Q), h⟩

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
