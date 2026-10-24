module
public import SerrePositivity.InfinityCategories.Stable.IntervalCofiberSourceReflection
public import SerrePositivity.InfinityCategories.Stable.SliceSquareIntervalFamily
public import SerrePositivity.InfinityCategories.Stable.FunctorPushoutPointwise
public import SerrePositivity.InfinityCategories.Stable.PullbackComparisonReflection
/-!
概要：実 loop 同値から任意の零角の fiber/cofiber 判定を導く。
方針：同じ cospan の極限錐への比較を cofiber 区間族へ移し、始点の可逆性を反映する。
規約：有限余極限や IsStable を追加仮定にしない。
使われ方：一般の loop 同値による安定性定理の零角条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

lemma ZeroTriangle.isFiber_of_isCofiber_of_loopEquivalence {X : SSet.{u}}
    [Quasicategory X] [HasZeroVertex X] [HasFiniteLimits X]
    (s : X ⟶ loopDiagrams X) (hs : s ≫ loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : IsQCatEquivalence (s ≫ loopDiagramEvaluation X 0 0))
    (t : ZeroTriangle X) (ht : IsCofiberSequence t) : IsFiberSequence t := by
  obtain ⟨c, hc⟩ := HasFiniteLimits.hasLimit (pullbackCospan t.square)
  obtain ⟨a⟩ := hc.nonempty_edge (pullbackCone t.square)
  let R := sliceSquareIntervalFamily a
  let k₀ : (horn 2 2 : SSet.{u}) _⦋0⦌ :=
    horn₂₂.ι₁₂.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))
  have hzero : (pullbackCospan t.square).app (Opposite.op ⦋0⦌) k₀ =
      squareVertex t.square 0 1 := by
    change t.square.app (Opposite.op ⦋0⦌)
      (cospanSquareBoundary.app (Opposite.op ⦋0⦌) k₀) = _
    rw [cospanSquareBoundary_source_top]
    rfl
  have hRzero : IsZeroVertex (squareVertex R 0 1) := by
    have hb := sliceSquareIntervalFamily_boundary a k₀
    rw [cospanSquareBoundary_source_top, hzero] at hb
    change IsZeroVertex ((sliceSquareIntervalFamily a).app (Opposite.op ⦋0⦌)
      (squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) 0 1))
    rw [hb]
    apply isZeroVertex_functorVertex_of_pointwise
    intro k
    change IsZeroVertex (PinchedHom.constant (squareVertex t.square 0 1) 0)
    rw [pinchedConstant_zero]
    exact t.zero_corner
  let T : ZeroTriangle ((ihom (Δ[1] : SSet.{u})).obj X) := ⟨R, hRzero⟩
  have hT : IsCofiberSequence T := by
    apply isPushoutSquare_functorCategory_of_pointwise
    intro k
    obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective k
    dsimp only [T, R]
    fin_cases i
    · change IsPushoutSquare (sliceSquareIntervalFamily a ≫
        evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
      rw [sliceSquareIntervalFamily_source]
      change IsPushoutSquare (cospanConeSquareIso.inv ≫ (cospanConeSquareIso.hom ≫ t.square))
      simpa only [Iso.inv_hom_id_assoc] using (show IsPushoutSquare t.square from ht)
    · change IsPushoutSquare (sliceSquareIntervalFamily a ≫
        evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
      rw [sliceSquareIntervalFamily_target]
      exact isPushoutSquare_of_isPullback_of_loopEquivalence s hs hΩ _
        (coneSquare_isPullback c hc)
  have hmiddle : IsEquivalencePathVertex (squareVertex T.square 1 0) := by
    have hb := sliceSquareIntervalFamily_boundary a
      (horn₂₂.ι₀₂.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
    rw [cospanSquareBoundary_source_right] at hb
    change IsEquivalencePathVertex ((sliceSquareIntervalFamily a).app (Opposite.op ⦋0⦌)
      (squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) 1 0))
    rw [hb]
    exact isEquivalencePathVertex_const _
  have htarget : IsEquivalencePathVertex (squareVertex T.square 1 1) := by
    have hb := sliceSquareIntervalFamily_boundary a cospanTargetVertex
    rw [cospanSquareBoundary_targetVertex] at hb
    change IsEquivalencePathVertex ((sliceSquareIntervalFamily a).app (Opposite.op ⦋0⦌)
      (squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) 1 1))
    rw [hb]
    exact isEquivalencePathVertex_const _
  have hsource := T.source_isEquivalencePath_of_middle_target s hs hΩ hT hmiddle htarget
  change IsInvertibleEdge (edgeOfSimplex
    (intervalFunctorVertexEdge (squareVertex (sliceSquareIntervalFamily a) 0 0))) at hsource
  rw [sliceSquareIntervalFamily_sourceEdge] at hsource
  apply isPullbackSquare_of_invertible_coneComparison t.square c hc a
  exact (isInvertibleEdge_congr (e := edgeOfSimplex
    ((a.map ((truncation 2).map (sliceOverProjection (pullbackCospan t.square))))).edge)
    (f := a.map ((truncation 2).map (sliceOverProjection (pullbackCospan t.square))))
    rfl).mp hsource

lemma ZeroTriangle.isFiber_iff_isCofiber_of_loopEquivalence {X : SSet.{u}}
    [Quasicategory X] [HasZeroVertex X] [HasFiniteLimits X]
    (s : X ⟶ loopDiagrams X) (hs : s ≫ loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : IsQCatEquivalence (s ≫ loopDiagramEvaluation X 0 0))
    (t : ZeroTriangle X) : IsFiberSequence t ↔ IsCofiberSequence t :=
  ⟨fun ht ↦ isPushoutSquare_of_isPullback_of_loopEquivalence s hs hΩ t.square ht,
    t.isFiber_of_isCofiber_of_loopEquivalence s hs hΩ⟩

end SerrePositivity.InfinityCategories
