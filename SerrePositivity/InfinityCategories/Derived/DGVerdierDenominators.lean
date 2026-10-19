module
public import SerrePositivity.InfinityCategories.Derived.DGQuotientLocalizingEdges
public import SerrePositivity.InfinityCategories.Stable.CofiberLocalizingBaseChange
public import SerrePositivity.InfinityCategories.Stable.CofiberLocalizingComposition

/-! # Native dg nerve の実 Verdier 分母の計算

概要：前三角 dg 圏の実 Verdier 辺は二対三性と基底変更を満たす。
方針：実 dg nerve の安定性から一般の実 cofiber 計算を適用する。
規約：元の Hom の平坦性を要求しない。使われ方：有限族の共通分母。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded SSet MonoidalCategory
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]

/-- 全ての実可逆辺は Verdier 分母である。 -/
lemma dgVerdierEdges_of_isInvertible (P : Set D) {a : (dgNerve A D) _⦋1⦌}
    (ha : IsInvertibleEdge (edgeOfSimplex a)) : a ∈ dgVerdierEdges A D P := by
  let := dgNerve_isStable_of_pretriangulated A D
  exact cofiberStableEdges_of_isInvertible _ ha

/-- 実合成二単体の三辺に対する Verdier 分母の二対三性。 -/
theorem dgVerdierEdges_twoOfThree (P : Set D) (τ : Δ[2] ⟶ dgNerve A D) :
    let W := fun i : Fin 3 => SSet.yonedaEquiv (stdSimplex.δ i ≫ τ) ∈ dgVerdierEdges A D P
    (W 2 → W 0 → W 1) ∧ (W 2 → W 1 → W 0) ∧ (W 0 → W 1 → W 2) := by
  let := dgNerve_isStable_of_pretriangulated A D
  exact cofiberStableEdges_twoOfThree _ τ

/-- 実押し出しの左右の辺は Verdier 分母として同時に所属する。 -/
theorem dgVerdierEdges_pushout_iff (P : Set D)
    (L : Δ[1] ⊗ Δ[1] ⟶ dgNerve A D) (hL : IsPushoutSquare L) :
    (squareLeftArrow L).edge ∈ dgVerdierEdges A D P ↔
      (squareRightArrow L).edge ∈ dgVerdierEdges A D P := by
  let := dgNerve_isStable_of_pretriangulated A D
  exact cofiberStableEdges_pushout_iff _ L hL

/-- 実引き戻しの左右の辺は Verdier 分母として同時に所属する。 -/
theorem dgVerdierEdges_pullback_iff (P : Set D)
    (L : Δ[1] ⊗ Δ[1] ⟶ dgNerve A D) (hL : IsPullbackSquare L) :
    (squareLeftArrow L).edge ∈ dgVerdierEdges A D P ↔
      (squareRightArrow L).edge ∈ dgVerdierEdges A D P := by
  let := dgNerve_isStable_of_pretriangulated A D
  exact cofiberStableEdges_pullback_iff _ L hL

end SerrePositivity.InfinityCategories
