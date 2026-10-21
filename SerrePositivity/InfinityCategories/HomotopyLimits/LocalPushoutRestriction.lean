module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CoconeUniversalRestriction
public import SerrePositivity.InfinityCategories.HomotopyLimits.LocalSpanRestriction
public import SerrePositivity.InfinityCategories.Stable.CosliceRestriction
public import SerrePositivity.InfinityCategories.Stable.FiniteShapes
public import SerrePositivity.InfinityCategories.F1.PrismEndpointRightAnodyne

/-!
概要：元の pushout の余錐制限と span の局所的な余錐制限を照合する。
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
/-- 正方形の上辺の包含は right anodyne。 -/
lemma local_squareTopEdge_rightAnodyne : rightAnodyneExtensions (squareTopEdge.{u}) := by
  have h : squareTopEdge.{u} = prismEndpoint 1 (Δ[1] : SSet.{u}) ≫ (β_ Δ[1] Δ[1]).hom := by
    rfl
  rw [h, rightAnodyneExtensions.cancel_right_of_respectsIso]
  exact prismEndpoint_one_rightAnodyne _

/-- 上辺の包含は単射。 -/
lemma local_squareTopEdge_mono : Mono (squareTopEdge.{u}) := by
  change Mono (prismEndpoint 1 (Δ[1] : SSet.{u}) ≫ (β_ Δ[1] Δ[1]).hom)
  infer_instance

variable {X : SSet.{u}} [Quasicategory X]
omit [Quasicategory X] in
/-- 元の pushout 四角形全体から固定 span への余錐制限は自明 Kan 射。 -/
lemma pushoutCoconeRestriction_trivial
    (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hR : IsPushoutSquare R) (z : X _⦋0⦌) :
    TrivialKanFibration (cosliceRestrictionFiberMap R spanSquareBoundary z) := by
  have := sliceUnderRestrict_cocone_trivial (pushoutCocone R) hR
  have h0 := cosliceRestrictionFiberMap_trivialKanFibration R spanCoconeSquareIso.hom z
  have h1 := cosliceRestrictionFiberMap_trivialKanFibration (pushoutCocone R).val
    (joinInl (horn 2 0 : SSet.{u}) Δ[0]) z
  change TrivialKanFibration (cosliceRestrictionFiberMap R
    (joinInl (horn 2 0 : SSet.{u}) Δ[0] ≫ spanCoconeSquareIso.hom) z)
  rw [← coconeMappingSpace_restrict_comp]
  exact ⟨trivialKanFibrations.comp_mem _ _ h0.mem h1.mem⟩

/-- 元の四角形から上辺への終点固定余錐の制限は自明 Kan 射。 -/
lemma pushoutTopCoconeRestriction_trivial
    (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (z : X _⦋0⦌) :
    TrivialKanFibration (cosliceRestrictionFiberMap R squareTopEdge z) := by
  have := local_squareTopEdge_mono.{u}
  have := sliceUnderRestrict_trivialKanFibration R squareTopEdge local_squareTopEdge_rightAnodyne
  exact cosliceRestrictionFiberMap_trivialKanFibration R squareTopEdge z

/-- 左枝への局所性から、右枝の終点への余錐制限の全境界充填性を得る。 -/
lemma spanCoconeMapping_rightTarget_trivial_of_local
    (p : (horn 2 0 : SSet.{u}) ⟶ X) (z : X _⦋0⦌)
    (h : IsLocalForHom (SSet.Truncated.HomotopyCategory.homMk
      (edgeCosliceEdge (horn₂₀.ι₀₁ ≫ p))) z) :
    TrivialKanFibration (cosliceRestrictionFiberMap p
      (stdSimplex.δ (0 : Fin 2) ≫ horn₂₀.ι₀₂) z) := by
  have h0 := spanCoconeMapping_right_trivial_of_local p z h
  have h1 := cosliceTriangleTarget_trivialKanFibration (horn₂₀.ι₀₂ ≫ p) z
  rw [← coconeMappingSpace_restrict_comp]
  exact ⟨trivialKanFibrations.comp_mem _ _ h0.mem h1.mem⟩

/-- span の第二枝の終点と正方形の上辺の始点は同じ元の頂点。 -/
lemma local_pushout_topSource_shape :
    (stdSimplex.δ (0 : Fin 2) ≫ horn₂₀.ι₀₂) ≫ spanSquareBoundary.{u} =
      stdSimplex.δ (1 : Fin 2) ≫ squareTopEdge := by
  rw [Category.assoc, spanSquareBoundary_leftEdge]
  apply SSet.yonedaEquiv.injective
  apply Prod.ext <;> decide

end
end SerrePositivity.InfinityCategories.HomotopyLimits
