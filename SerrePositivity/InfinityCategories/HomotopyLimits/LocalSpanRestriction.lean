module

public import SerrePositivity.InfinityCategories.HomotopyLimits.LocalEdgeRestriction
public import SerrePositivity.InfinityCategories.Stable.SpanCoconeMappingPullback

/-!
概要：局所対象への span の余錐を右枝・その終点へ制限する射の全境界充填性。
方針：両枝の余錐空間の厳密な引き戻しと、辺の始点制限の自明 Kan 性を使う。
規約：元の span と指定辺を保持。pushout の脚との照合は別工程。使われ方：HTT 5.5.4.5。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {X : SSet.{u}} [Quasicategory X]

/-- 左枝への局所性は、span の余錐の右枝への制限の自明 Kan 性を与える。 -/
lemma spanCoconeMapping_right_trivial_of_local
    (p : (horn 2 0 : SSet.{u}) ⟶ X) (z : X _⦋0⦌)
    (h : IsLocalForHom (SSet.Truncated.HomotopyCategory.homMk
      (edgeCosliceEdge (horn₂₀.ι₀₁ ≫ p))) z) :
    TrivialKanFibration (cosliceRestrictionFiberMap p horn₂₀.ι₀₂ z) := by
  have := (isLocalForHom_edge_iff_sourceRestriction_trivial _ z).mp h
  exact ⟨trivialKanFibrations.of_isPullback (spanCoconeMapping_isPullback p z)
    (TrivialKanFibration.mem (p := cosliceRestrictionFiberMap
      (horn₂₀.ι₀₁ ≫ p) (stdSimplex.δ (1 : Fin 2)) z))⟩
/-- 指定辺集合に属する左枝から、局所対象への余錐の右枝制限の全境界充填性を得る。 -/
lemma spanCoconeMapping_right_trivial_of_localObject (W : Set (X _⦋1⦌))
    (p : (horn 2 0 : SSet.{u}) ⟶ X) (he : SSet.yonedaEquiv (horn₂₀.ι₀₁ ≫ p) ∈ W)
    {z : X _⦋0⦌} (hz : IsLocalObject W z) :
    TrivialKanFibration (cosliceRestrictionFiberMap p horn₂₀.ι₀₂ z) := by
  apply spanCoconeMapping_right_trivial_of_local p z
  apply (isLocalForHom_homMk_iff_edgeOfSimplex (edgeCosliceEdge (horn₂₀.ι₀₁ ≫ p)) z).mpr
  exact hz _ he

/-- 指定左枝が属する辺集合の局所対象に対し、右枝の終点への余錐制限は自明 Kan 射。 -/
lemma spanCoconeMapping_rightTarget_trivial_of_localObject (W : Set (X _⦋1⦌))
    (p : (horn 2 0 : SSet.{u}) ⟶ X) (he : SSet.yonedaEquiv (horn₂₀.ι₀₁ ≫ p) ∈ W)
    {z : X _⦋0⦌} (hz : IsLocalObject W z) :
    TrivialKanFibration (cosliceRestrictionFiberMap p
      (stdSimplex.δ (0 : Fin 2) ≫ horn₂₀.ι₀₂) z) := by
  have := spanCoconeMapping_right_trivial_of_localObject W p he hz
  have := cosliceTriangleTarget_trivialKanFibration (horn₂₀.ι₀₂ ≫ p) z
  rw [← coconeMappingSpace_restrict_comp]
  exact ⟨trivialKanFibrations.comp_mem _ _ (TrivialKanFibration.mem (p :=
    cosliceRestrictionFiberMap p horn₂₀.ι₀₂ z)) (TrivialKanFibration.mem (p :=
      cosliceRestrictionFiberMap (horn₂₀.ι₀₂ ≫ p) (stdSimplex.δ (0 : Fin 2)) z))⟩

end
end SerrePositivity.InfinityCategories.HomotopyLimits
