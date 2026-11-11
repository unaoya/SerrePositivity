module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CospanHomHorn
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CompositionCorrespondenceDiagonal

/-!
概要：同じ指定対角と終域辺の外ホーン条件から、第一辺の二端点を回収する。
方針：外ホーンの二辺を制限し、標準単体の頂点の合成則で第一辺へ移す。
規約：元の三角形と対角の全パラメーターを保持する。
使われ方：対角評価の外ホーン pullback の持ち上げ。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

variable {X T : SSet.{u}} (x : X _⦋0⦌) {y z : X _⦋0⦌} (g : X.Edge y z)
variable (a : T ⟶ (ihom (Δ[2] : SSet.{u})).obj X) (b : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x z)
variable (h : a ≫ (pre (horn 2 2).ι).app X = b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cospanHomHornMap x g)
include h

/-- 指定外ホーンの対角は、元の指定対角の区間族そのもの。 -/
lemma compositionCorrespondenceDiagonalLift_diagonal :
    (stdSimplex.δ (1 : Fin 3) ▷ T) ≫ uncurry a = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry b := by
  calc
    _ = (horn₂₂.ι₀₂ ▷ T) ≫ uncurry (a ≫ (pre (horn 2 2).ι).app X) := by
      rw [uncurry_pre_app, ← Category.assoc, ← comp_whiskerRight, horn.ι_ι]
    _ = _ := by rw [h, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cospanHomHornMap_diagonal]

/-- 指定外ホーンの終域辺は、元の指定辺に定値。 -/
lemma compositionCorrespondenceDiagonalLift_target :
    (stdSimplex.δ (0 : Fin 3) ▷ T) ≫ uncurry a =
      fst (Δ[1] : SSet.{u}) T ≫ SSet.yonedaEquiv.symm g.edge := by
  calc
    _ = (horn₂₂.ι₁₂ ▷ T) ≫ uncurry (a ≫ (pre (horn 2 2).ι).app X) := by
      rw [uncurry_pre_app, ← Category.assoc, ← comp_whiskerRight, horn.ι_ι]
    _ = _ := by rw [h, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cospanHomHornMap_target]

/-- 元の三角形の第一辺の始点は、同じ指定対角の始点。 -/
lemma compositionCorrespondenceDiagonalLift_first_source :
    (stdSimplex.δ (1 : Fin 2) ▷ T) ≫ (stdSimplex.δ (2 : Fin 3) ▷ T) ≫ uncurry a =
      fst (Δ[0] : SSet.{u}) T ≫ SSet.yonedaEquiv.symm x := by
  have hδ : (stdSimplex.δ (1 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) ≫
      stdSimplex.δ (2 : Fin 3) = stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (1 : Fin 3) := by
    apply SSet.yonedaEquiv.injective
    decide
  rw [← Category.assoc, ← comp_whiskerRight, hδ, comp_whiskerRight, Category.assoc,
    compositionCorrespondenceDiagonalLift_diagonal x g a b h, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_face_source]

/-- 元の三角形の第一辺の終点は、同じ指定終域辺の始点。 -/
lemma compositionCorrespondenceDiagonalLift_first_target :
    (stdSimplex.δ (0 : Fin 2) ▷ T) ≫ (stdSimplex.δ (2 : Fin 3) ▷ T) ≫ uncurry a =
      fst (Δ[0] : SSet.{u}) T ≫ SSet.yonedaEquiv.symm y := by
  have hδ : (stdSimplex.δ (0 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) ≫
      stdSimplex.δ (2 : Fin 3) = stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3) := by
    apply SSet.yonedaEquiv.injective
    decide
  rw [← Category.assoc, ← comp_whiskerRight, hδ, comp_whiskerRight, Category.assoc,
    compositionCorrespondenceDiagonalLift_target x g a b h, ← Category.assoc, whiskerRight_fst,
    Category.assoc, g.δ_one_yonedaEquiv_symm]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
