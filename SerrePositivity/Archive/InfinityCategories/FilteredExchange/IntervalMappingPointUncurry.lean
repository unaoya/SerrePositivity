module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceIntervalComparison

/-!
概要：元の区間全族の指定点での全係数制限を、同じ一点区間の定値族へ戻す。
方針：uncurry の前合成と定値射の合成の式を使う。
規約：元の点・元の全区間を保持。使われ方：同じ普遍対角 prism の係数照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 同じ指定点での元の全区間の制限は、元の同じ一点区間の定値族の uncurry。 -/
lemma intervalMappingPoint_uncurry {B C K : SSet.{u}} {a b : B _⦋0⦌}
    (c : C ⟶ intervalMappingSpace a b) (l : C _⦋0⦌) :
    (Δ[1] ◁ (SSet.const l : K ⟶ C)) ≫ intervalMappingUncurry c =
      intervalMappingUncurry (SSet.const (c.app (Opposite.op ⦋0⦌) l) :
        K ⟶ intervalMappingSpace a b) := by
  rw [← intervalMappingUncurry_precomp, SSet.const_comp]

/-- 元の指定点の全区間を再 curry しても、同じ一点区間の定値族を回収する。 -/
lemma intervalMappingPoint_curry {B C K : SSet.{u}} {a b : B _⦋0⦌}
    (c : C ⟶ intervalMappingSpace a b) (l : C _⦋0⦌)
    (h₀ : prismEndpoint 0 K ≫
      ((Δ[1] ◁ (SSet.const l : K ⟶ C)) ≫ intervalMappingUncurry c) = SSet.const a)
    (h₁ : prismEndpoint 1 K ≫
      ((Δ[1] ◁ (SSet.const l : K ⟶ C)) ≫ intervalMappingUncurry c) = SSet.const b) :
    intervalMappingCurryOfEndpoints
      ((Δ[1] ◁ (SSet.const l : K ⟶ C)) ≫ intervalMappingUncurry c) h₀ h₁ =
      SSet.const (c.app (Opposite.op ⦋0⦌) l) := by
  apply intervalMappingUncurry_injective
  rw [intervalMappingUncurry_curryOfEndpoints, intervalMappingPoint_uncurry]

end SerrePositivity.InfinityCategories.F2
