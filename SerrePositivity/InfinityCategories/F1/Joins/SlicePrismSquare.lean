module

public import SerrePositivity.InfinityCategories.F1.MappingSpaces.MappingSpaceIntervalComparison
public import SerrePositivity.InfinityCategories.Core.SliceMap

/-!
概要：終点固定の slice 内の prism を、二段合成を比較する同じ底の四角形へ展開する。
方針：元の錐の族を uncurry し、既存の右 join 区間比較で引き戻す。
規約：二つの時間と全パラメーターを保ち、充填性は仮定しない。
使われ方：右 Hom の合成と pointed 輸送の二順序を同じ四角形で照合する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 終点固定の slice の prism を、外側が終点へ向かう区間である四角形へ展開する。 -/
def slicePrismSquare {X P : SSet.{u}} (z : X _⦋0⦌)
    (W : (Δ[1] : SSet.{u}) ⊗ P ⟶ sliceOver (SSet.yonedaEquiv.symm z)) :
    Δ[1] ⊗ (Δ[1] ⊗ P) ⟶ X :=
  rightMappingSpacePrism _ ≫ sliceOverUncurry W

/-- 外側の零端は、元の slice prism の射影そのもの。 -/
lemma slicePrismSquare_zero {X P : SSet.{u}} (z : X _⦋0⦌)
    (W : (Δ[1] : SSet.{u}) ⊗ P ⟶ sliceOver (SSet.yonedaEquiv.symm z)) :
    prismEndpoint 0 _ ≫ slicePrismSquare z W =
      W ≫ sliceOverProjection (SSet.yonedaEquiv.symm z) := by
  rw [slicePrismSquare, ← Category.assoc, rightMappingSpacePrism_zero,
    sliceOverUncurry_projection]

/-- 外側の一端は、元の固定終点に全パラメーターで厳密に定値。 -/
lemma slicePrismSquare_one {X P : SSet.{u}} (z : X _⦋0⦌)
    (W : (Δ[1] : SSet.{u}) ⊗ P ⟶ sliceOver (SSet.yonedaEquiv.symm z)) :
    prismEndpoint 1 _ ≫ slicePrismSquare z W = SSet.const z := by
  rw [slicePrismSquare, ← Category.assoc, rightMappingSpacePrism_one,
    Category.assoc, sliceOverUncurry_fixed, const_point_comp_yoneda]

/-- 内側の各端は、元の錐の同じ端点制限を右区間比較で展開した族。 -/
lemma slicePrismSquare_inner {X P : SSet.{u}} (z : X _⦋0⦌)
    (W : (Δ[1] : SSet.{u}) ⊗ P ⟶ sliceOver (SSet.yonedaEquiv.symm z)) (i : Fin 2) :
    (Δ[1] ◁ prismEndpoint i P) ≫ slicePrismSquare z W =
      rightMappingSpacePrism P ≫ sliceOverUncurry (prismEndpoint i P ≫ W) := by
  rw [slicePrismSquare, ← Category.assoc, rightMappingSpacePrism_naturality,
    Category.assoc, ← sliceOverUncurry_precomp]

end SerrePositivity.InfinityCategories
