module
public import SerrePositivity.InfinityCategories.Stable.ExcisionComparisonCospanEquivalence
public import SerrePositivity.InfinityCategories.Stable.FunctorEdgeBottomReadback
public import SerrePositivity.InfinityCategories.Stable.ExcisionComparisonTheta
public import SerrePositivity.InfinityCategories.Stable.PullbackComparisonDiagonalInvertible
public import SerrePositivity.InfinityCategories.Stable.ArrowIsoPostcompTransport
public import SerrePositivity.InfinityCategories.Stable.FunctorFiniteLimits

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

lemma excisionComparison_theta_invertible_postcomp {X : SSet.{u}} [Quasicategory X]
    [HasFiniteLimits X] (F : nerve ExcisionGridIndex.{u} ⟶ X)
    (i : JoinCone (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫
      (nerveMap excisionGridCoreInclusion ≫ nerveMap excisionGridMiddleInclusion ≫ F)) 2 2)))
    (hi : IsLimitCone i)
    (c : JoinCone (nerveMap (posetSubtypeInclusion IsExcisionFullPunctured) ≫ F))
    (hc : IsLimitCone c)
    (hr : (F2.restrictJoinCone c (nerveMap excisionCorePuncturedToFull.toFunctor)).val =
      (excisionCorePuncturedLimitCone
        (nerveMap excisionGridCoreInclusion ≫ nerveMap excisionGridMiddleInclusion ≫ F)
        i hi).val)
    (d : JoinCone (pullbackCospan (excisionRawSuspensionSquare (excisionReplaceInitial c))))
    (hd : IsLimitCone d)
    (hF : ∀ k : ((Δ[1] : SSet.{u}) ⊗ Δ[1]) _⦋0⦌,
      IsPullbackSquare (excisionRawSuspensionSquare F ≫ evaluateFunctorAt k)) :
    ∃ (e : JoinCone (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫
        (nerveMap excisionGridCoreInclusion ≫ nerveMap excisionGridMiddleInclusion ≫ F)) 1 1)))
      (he : IsLimitCone e) (z : hoFunctor.obj X)
      (v : (HomotopyCategory.mk e.vertex : hoFunctor.obj X) ⟶ z),
      IsIso (Truncated.HomotopyCategory.homMk (excisionCoreComparisonEdge
        (nerveMap excisionGridCoreInclusion ≫ nerveMap excisionGridMiddleInclusion ≫ F)
        i hi e he) ≫ v) := by
  let A := excisionPullbackComparisonFamily c d hd
  have := hasFiniteLimits_functorCategory (Δ[1] : SSet.{u}) X
  obtain ⟨l, hl⟩ := HasFiniteLimits.hasLimit (pullbackCospan A)
  let t := functorPullbackComparisonEdge A l hl
  let Q := uncurry (SSet.yonedaEquiv.symm t.edge)
  have hdiag : IsInvertibleEdge (squareDiagonalArrow Q) :=
    functorPullbackComparison_diagonal_isInvertible A l hl
      (excisionPullbackComparisonFamily_source_isPullback c hc d hd)
      (excisionComparison_cospan_isEquivalencePath c d hd hF)
  have hcomp : IsIso (Truncated.HomotopyCategory.homMk (squareBottomArrow Q) ≫
      Truncated.HomotopyCategory.homMk (squareRightArrow Q)) := by
    rw [squareBottomRight_homMk_diagonal]
    exact hdiag
  obtain ⟨e, he, htheta⟩ := excisionRawSuspensionComparison_source_theta F i hi c hr d hd
  have hb := squareBottomArrow_functorEdge_edge t
  have hb0 := hb.trans (congrArg intervalFunctorVertexEdge (pullbackCone_vertex A))
  let k : ((Δ[1] : SSet.{u}) ⊗ Δ[1]) _⦋0⦌ :=
    (stdSimplex.obj₀Equiv.symm 0, stdSimplex.obj₀Equiv.symm 0)
  have hvertex := arrowFamilyOfFunctorEdge_vertex_edge
    (functorPullbackComparisonEdge (excisionRawSuspensionSquare (excisionReplaceInitial c))
      d hd) k
  have hraw : (squareBottomArrow Q).edge =
      ((functorPullbackComparisonEdge
        (excisionRawSuspensionSquare (excisionReplaceInitial c)) d hd).map
          ((truncation 2).map (evaluateFunctorAt k))).edge := hb0.trans hvertex
  have heq := (Truncated.HomotopyCategory.congr_arrowMk_homMk _ _ hraw).trans htheta
  have h := isIso_comp_of_arrowMk_eq
    (Truncated.HomotopyCategory.homMk (squareBottomArrow Q))
    (Truncated.HomotopyCategory.homMk (excisionCoreComparisonEdge
      (nerveMap excisionGridCoreInclusion ≫ nerveMap excisionGridMiddleInclusion ≫ F)
      i hi e he))
    (Truncated.HomotopyCategory.homMk (squareRightArrow Q)) heq hcomp
  exact ⟨e, he, (HomotopyCategory.mk (squareVertex Q 1 1) : hoFunctor.obj X),
    eqToHom (congrArg Arrow.right heq).symm ≫
      Truncated.HomotopyCategory.homMk (squareRightArrow Q), h⟩

end SerrePositivity.InfinityCategories
