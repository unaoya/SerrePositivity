module

public import SerrePositivity.InfinityCategories.F2.Presentable.LocalPushoutRestriction
public import SerrePositivity.InfinityCategories.Stable.SquareTranspose

/-!
概要：S-equivalence の元の辺集合が任意の coherent な pushout で保たれることを証明する。
方針：余極限余錐全体への coslice の持ち上げと、元の span の厳密な引き戻しを使う。
規約：元の辺・頂点・四角形を保持。使われ方：HTT 5.5.4.5(1)・5.5.4.11。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet HomotopicalAlgebra
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {X : SSet.{u}} [Quasicategory X]

/-- 元の coherent な pushout 四角形の下辺への局所性は上辺へ保存される。 -/
lemma isLocalForHom_pushout_top_of_bottom
    (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hR : IsPushoutSquare R) (z : X _⦋0⦌)
    (h : IsLocalForHom (SSet.Truncated.HomotopyCategory.homMk
      (edgeCosliceEdge (squareBottomEdge ≫ R))) z) :
    IsLocalForHom (SSet.Truncated.HomotopyCategory.homMk
      (edgeCosliceEdge (squareTopEdge ≫ R))) z := by
  have hp : IsLocalForHom (SSet.Truncated.HomotopyCategory.homMk
      (edgeCosliceEdge (horn₂₀.ι₀₁ ≫ pushoutSpan R))) z := by
    have he : horn₂₀.ι₀₁ ≫ pushoutSpan R = squareBottomEdge ≫ R := by
      rw [pushoutSpan, ← Category.assoc, spanSquareBoundary_bottomEdge]
    rw [he]
    exact h
  have h0 := pushoutCoconeRestriction_trivial R hR z
  have h1 := spanCoconeMapping_rightTarget_trivial_of_local (pushoutSpan R) z hp
  have h2 := pushoutTopCoconeRestriction_trivial R z
  have hcomp : IsQCatEquivalence (cosliceRestrictionFiberMap R
      (stdSimplex.δ (1 : Fin 2) ≫ squareTopEdge) z) := by
    rw [← local_pushout_topSource_shape, ← coconeMappingSpace_restrict_comp]
    have : TrivialKanFibration (cosliceRestrictionFiberMap R spanSquareBoundary z) := h0
    have : TrivialKanFibration (cosliceRestrictionFiberMap (spanSquareBoundary ≫ R)
      (stdSimplex.δ (0 : Fin 2) ≫ horn₂₀.ι₀₂) z) := h1
    exact (isQCatEquivalence_of_trivialKanFibration _).comp
      (isQCatEquivalence_of_trivialKanFibration _)
  rw [← coconeMappingSpace_restrict_comp] at hcomp
  apply (isLocalForHom_edge_iff_sourceRestriction _ z).mpr
  exact (isQCatEquivalence_of_trivialKanFibration
    (cosliceRestrictionFiberMap R squareTopEdge z)).cancel_left hcomp
/-- 元の coherent な pushout 四角形の左辺への局所性は右辺へ保存される。 -/
lemma isLocalForHom_pushout_right_of_left
    (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hR : IsPushoutSquare R) (z : X _⦋0⦌)
    (h : IsLocalForHom (SSet.Truncated.HomotopyCategory.homMk
      (edgeCosliceEdge (squareLeftEdge ≫ R))) z) :
    IsLocalForHom (SSet.Truncated.HomotopyCategory.homMk
      (edgeCosliceEdge (squareRightEdge ≫ R))) z := by
  have hb : squareBottomEdge ≫ ((β_ Δ[1] Δ[1]).hom ≫ R) = squareLeftEdge ≫ R := by
    rw [← Category.assoc]
    rfl
  have ht : squareTopEdge ≫ ((β_ Δ[1] Δ[1]).hom ≫ R) = squareRightEdge ≫ R := by
    rw [← Category.assoc]
    rfl
  have h' : IsLocalForHom (SSet.Truncated.HomotopyCategory.homMk
      (edgeCosliceEdge (squareBottomEdge ≫ ((β_ Δ[1] Δ[1]).hom ≫ R)))) z := by
    rw [hb]
    exact h
  have htop := isLocalForHom_pushout_top_of_bottom ((β_ Δ[1] Δ[1]).hom ≫ R)
    ((isPushoutSquare_iff_transpose R).mp hR) z h'
  rwa [ht] at htop

/-- S-equivalence の元の辺集合は pushout の下辺から上辺へ保存される。 -/
lemma localEquivalences_pushout_bottom_top (W : Set (X _⦋1⦌))
    (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hR : IsPushoutSquare R)
    (h : SSet.yonedaEquiv (squareBottomEdge ≫ R) ∈ localEquivalences W) :
    SSet.yonedaEquiv (squareTopEdge ≫ R) ∈ localEquivalences W := by
  apply (localEquivalenceHom_iff_edge_mem W (edgeCosliceEdge (squareTopEdge ≫ R))).mp
  intro z hz
  apply isLocalForHom_pushout_top_of_bottom R hR z
  exact ((localEquivalenceHom_iff_edge_mem W (edgeCosliceEdge (squareBottomEdge ≫ R))).mpr h) z hz

/-- S-equivalence の元の辺集合は pushout の左辺から右辺へ保存される。 -/
lemma localEquivalences_pushout_left_right (W : Set (X _⦋1⦌))
    (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hR : IsPushoutSquare R)
    (h : SSet.yonedaEquiv (squareLeftEdge ≫ R) ∈ localEquivalences W) :
    SSet.yonedaEquiv (squareRightEdge ≫ R) ∈ localEquivalences W := by
  apply (localEquivalenceHom_iff_edge_mem W (edgeCosliceEdge (squareRightEdge ≫ R))).mp
  intro z hz
  apply isLocalForHom_pushout_right_of_left R hR z
  exact ((localEquivalenceHom_iff_edge_mem W (edgeCosliceEdge (squareLeftEdge ≫ R))).mpr h) z hz

end
end SerrePositivity.InfinityCategories.HomotopyLimits
