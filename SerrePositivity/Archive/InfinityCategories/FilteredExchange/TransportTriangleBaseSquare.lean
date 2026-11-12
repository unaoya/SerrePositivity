module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.TransportTriangleParameter
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.TriangleFirstEdgePrismSquares
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IntervalSquare

/-!
概要：任意の全係数付き実二単体を、元の三辺を保持する輸送四角形へ移す。
方針：同じ実二単体を既存の折り畳みで制限し、三つの端点から区間族を回収する。
規約：coherent 図式を strict 化しない。使われ方：高次図式の各三角形面。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 任意の実二単体を、同じ三頂点・三辺と定値終辺を持つ元の係数四角形へ束ねる。 -/
def transportTriangleBaseSquare {B P : SSet.{u}} (β : (Δ[2] : SSet.{u}) ⊗ P ⟶ B)
    (a b d : B _⦋0⦌)
    (h₀ : (prismEndpoint 0 P ≫ (stdSimplex.δ (2 : Fin 3) ▷ P)) ≫ β = SSet.const a)
    (h₁ : (prismEndpoint 1 P ≫ (stdSimplex.δ (2 : Fin 3) ▷ P)) ≫ β = SSet.const b)
    (h₂ : (prismEndpoint 1 P ≫ (stdSimplex.δ (1 : Fin 3) ▷ P)) ≫ β = SSet.const d) :
    TransportIntervalSquare P a b d d := by
  have hs₀ : prismEndpoint 0 P ≫ ((stdSimplex.δ (2 : Fin 3) ▷ P) ≫ β) = SSet.const a :=
    (Category.assoc _ _ _).symm.trans h₀
  have he₀ : prismEndpoint 1 P ≫ ((stdSimplex.δ (2 : Fin 3) ▷ P) ≫ β) = SSet.const b :=
    (Category.assoc _ _ _).symm.trans h₁
  have hs₁ : prismEndpoint 0 P ≫ ((stdSimplex.δ (1 : Fin 3) ▷ P) ≫ β) = SSet.const a := by
    rw [← Category.assoc, triangleFirstEdge_long_initial_square]; exact h₀
  have he₁ : prismEndpoint 1 P ≫ ((stdSimplex.δ (1 : Fin 3) ▷ P) ≫ β) = SSet.const d :=
    (Category.assoc _ _ _).symm.trans h₂
  have hs₂ : prismEndpoint 0 P ≫ ((stdSimplex.δ (0 : Fin 3) ▷ P) ≫ β) = SSet.const b := by
    rw [← Category.assoc, triangleFirstEdge_last_initial_square]; exact h₁
  have he₂ : prismEndpoint 1 P ≫ ((stdSimplex.δ (0 : Fin 3) ▷ P) ≫ β) = SSet.const d := by
    rw [← Category.assoc, triangleFirstEdge_last_final_square]; exact h₂
  exact {
    bottom := intervalMappingCurryOfEndpoints _ hs₀ he₀
    left := intervalMappingCurryOfEndpoints _ hs₁ he₁
    right := intervalMappingCurryOfEndpoints _ hs₂ he₂
    top := intervalMappingCurryOfEndpoints (SSet.const d)
      (SSet.comp_const _ _) (SSet.comp_const _ _)
    square := transportTriangleParameter P ≫ β
    zero := by
      rw [← Category.assoc, transportTriangleParameter_bottom,
        intervalMappingUncurry_curryOfEndpoints]
    one := by
      rw [← Category.assoc, transportTriangleParameter_top_factor, Category.assoc, h₂,
        SSet.comp_const, intervalMappingUncurry_curryOfEndpoints]
    inner_zero := by
      rw [← Category.assoc, transportTriangleParameter_left,
        intervalMappingUncurry_curryOfEndpoints]
    inner_one := by
      rw [← Category.assoc, transportTriangleParameter_right,
        intervalMappingUncurry_curryOfEndpoints] }

end SerrePositivity.InfinityCategories.F2
