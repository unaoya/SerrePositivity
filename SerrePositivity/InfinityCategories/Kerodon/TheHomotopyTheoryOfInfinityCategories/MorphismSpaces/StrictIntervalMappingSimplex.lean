module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.StrictDiagramMappingNaturality

/-!
概要：二点の図式の間の strict 変換の単体を、同じ二つの成分から復元する。
方針：交差射に関する厳密な可換式だけで自然性を構成する。
規約：各値の充填性を要求せず、元の両成分を保持する。
使われ方：一次元セルの全変換空間の pullback の普遍性。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 元の二つの成分と交差射の可換式から、同じ strict 変換の単体を作る。 -/
def strictIntervalMappingSimplex (F G : ULift.{u} (Fin 2) ⥤ SSet.{u})
    (n : SimplexCategoryᵒᵖ)
    (a : ((ihom (F.obj (ULift.up 0))).obj (G.obj (ULift.up 0))).obj n)
    (b : ((ihom (F.obj (ULift.up 1))).obj (G.obj (ULift.up 1))).obj n)
    (h : ((ihom (F.obj (ULift.up 0))).map (G.map _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.strictIntervalIndexArrow)).app n a =
      ((pre (F.map _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.strictIntervalIndexArrow)).app (G.obj (ULift.up 1))).app n b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSimplex F G n := by
  refine ⟨fun i ↦ ?_, ?_⟩
  · rcases i with ⟨i⟩
    cases i using Fin.cases with
    | zero => exact a
    | succ i => obtain rfl : i = 0 := Subsingleton.elim _ _; exact b
  intro i j f k α x
  rcases i with ⟨i⟩
  rcases j with ⟨j⟩
  fin_cases i <;> fin_cases j
  · obtain rfl : f = 𝟙 (ULift.up (0 : Fin 2) : ULift.{u} (Fin 2)) := Subsingleton.elim _ _
    change (G.map (𝟙 (ULift.up (0 : Fin 2) : ULift.{u} (Fin 2)))).app k (a.app k α x) =
      a.app k α ((F.map (𝟙 (ULift.up (0 : Fin 2) : ULift.{u} (Fin 2)))).app k x)
    rw [F.map_id, G.map_id]
    rfl
  · obtain rfl : f = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.strictIntervalIndexArrow := Subsingleton.elim _ _
    have hh := congrArg (fun θ ↦ θ.app k α x) h
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.internalHomPre_evaluate] at hh
    exact hh
  · have hf := leOfHom f
    change (1 : Fin 2) ≤ 0 at hf
    omega
  · obtain rfl : f = 𝟙 (ULift.up (1 : Fin 2) : ULift.{u} (Fin 2)) := Subsingleton.elim _ _
    change (G.map (𝟙 (ULift.up (1 : Fin 2) : ULift.{u} (Fin 2)))).app k (b.app k α x) =
      b.app k α ((F.map (𝟙 (ULift.up (1 : Fin 2) : ULift.{u} (Fin 2)))).app k x)
    rw [F.map_id, G.map_id]
    rfl

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
