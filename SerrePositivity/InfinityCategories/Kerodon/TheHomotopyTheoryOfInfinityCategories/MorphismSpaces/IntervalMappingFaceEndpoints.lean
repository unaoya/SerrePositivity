module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalMappingVertexEquivalence

/-!
概要：両端固定の区間 Hom の族を、頂点の面に沿う厳密な族として制限する。
方針：境界の普遍条件を各頂点の包含に沿って引き戻す。
規約：全パラメーターを保持し、標的の充填性は不要。
使われ方：一辺が可変な合成三角形のホーンを全 Hom 空間上で貼る。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 区間族の始点の面は、元の始点の Yoneda 族に定値。 -/
lemma intervalMappingUncurry_face_source {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y) :
    (stdSimplex.δ (1 : Fin 2) ▷ A) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry f =
      fst (Δ[0] : SSet.{u}) A ≫ SSet.yonedaEquiv.symm x := by
  calc
    _ = (boundary.ι (1 : Fin 2) ▷ A) ≫
        ((boundary 1).ι ▷ A) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry f := by
      rw [← Category.assoc, ← comp_whiskerRight, boundary.ι_ι]
    _ = _ := by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_boundary, ← Category.assoc, whiskerRight_fst,
        Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingBoundary_face_one]

/-- 区間族の終点の面は、元の終点の Yoneda 族に定値。 -/
lemma intervalMappingUncurry_face_target {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y) :
    (stdSimplex.δ (0 : Fin 2) ▷ A) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry f =
      fst (Δ[0] : SSet.{u}) A ≫ SSet.yonedaEquiv.symm y := by
  calc
    _ = (boundary.ι (0 : Fin 2) ▷ A) ≫
        ((boundary 1).ι ▷ A) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry f := by
      rw [← Category.assoc, ← comp_whiskerRight, boundary.ι_ι]
    _ = _ := by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_boundary, ← Category.assoc, whiskerRight_fst,
        Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingBoundary_face_zero]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
