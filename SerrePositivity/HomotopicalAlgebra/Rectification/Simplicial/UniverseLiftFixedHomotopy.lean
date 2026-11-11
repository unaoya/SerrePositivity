module

public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftTensor
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.RelativeChoiceSpace

/-!
# 中断した任意モデル源への一般化：UniverseLiftFixedHomotopy

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Lifting the same selected whole edge with its endpoints and entire relative boundary。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0594][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0594
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Lifting the same selected whole edge with its endpoints and entire relative boundary
-/

@[expose] public section
universe w v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

namespace SerrePositivity.SimplicialModel.RelativeChoiceSpace.FixedBoundaryHomotopy
variable {V K P : SSet.{v}} (i : V ⟶ K) (b : V ⟶ P) (e₀ e₁ : K ⟶ P)
  (he₀ : i ≫ e₀ = b) (he₁ : i ≫ e₁ = b)
  (s : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ⟶ obj i b)
  (hs₀ : SSet.stdSimplex.δ (1 : Fin 2) ≫ s = ofExtension i b e₀ he₀)
  (hs₁ : SSet.stdSimplex.δ (0 : Fin 2) ≫ s = ofExtension i b e₁ he₁)

/-- Use the already selected edge, without choosing a replacement homotopy. -/
def ofEdge : FixedBoundaryHomotopy i b e₀ e₁ where
  hom := family i b s
  at_zero := (family_naturality i b s (SSet.stdSimplex.δ (1 : Fin 2))).symm.trans
    ((congrArg (family i b) hs₀).trans (family_ofExtension i b e₀ he₀))
  at_one := (family_naturality i b s (SSet.stdSimplex.δ (0 : Fin 2))).symm.trans
    ((congrArg (family i b) hs₁).trans (family_ofExtension i b e₁ he₁))
  relative := family_fixed_boundary i b s

end SerrePositivity.SimplicialModel.RelativeChoiceSpace.FixedBoundaryHomotopy

namespace SerrePositivity.SimplicialModel.UniverseLift
variable {V K P : SSet.{v}} {i : V ⟶ K} {b : V ⟶ P} {e₀ e₁ : K ⟶ P}
  (H : RelativeChoiceSpace.FixedBoundaryHomotopy i b e₀ e₁)

lemma point_projection (K : SSet.{v}) : K ◁ RelativeChoiceSpace.pointUnitIso.hom ≫
    (ρ_ K).hom = fst K (SSet.stdSimplex.obj (SimplexCategory.mk 0)) := by
  ext n x
  rfl

lemma whole_projection (V T : SSet.{v}) :
    V ◁ (SSet.stdSimplex.isTerminalObj₀.from T ≫ RelativeChoiceSpace.pointUnitIso.hom) ≫
      (ρ_ V).hom = fst V T := by
  ext n x
  rfl

abbrev fixedHomotopyMap : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} K ⊗ SSet.stdSimplex.{max w v}.obj (SimplexCategory.mk 1) ⟶
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} P := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexTensorMap.{w} H.hom

lemma fixedHomotopyMap_zero : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} K ◁ SSet.stdSimplex.δ (1 : Fin 2) ≫
    fixedHomotopyMap H = fst (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} K) (SSet.stdSimplex.obj (SimplexCategory.mk 0)) ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map e₀ := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexTensorMap_operator.{w} (SimplexCategory.δ (1 : Fin 2)) H.hom).trans
  rw [H.at_zero, ← Category.assoc, point_projection, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexTensorMap_constant]

lemma fixedHomotopyMap_one : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} K ◁ SSet.stdSimplex.δ (0 : Fin 2) ≫
    fixedHomotopyMap H = fst (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} K) (SSet.stdSimplex.obj (SimplexCategory.mk 0)) ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map e₁ := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexTensorMap_operator.{w} (SimplexCategory.δ (0 : Fin 2)) H.hom).trans
  rw [H.at_one, ← Category.assoc, point_projection, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexTensorMap_constant]

lemma fixedHomotopyMap_relative : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{w} i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫
    fixedHomotopyMap H = fst (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} V) (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map b := by
  rw [fixedHomotopyMap, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexTensorMap_source, H.relative, ← Category.assoc,
    whole_projection, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexTensorMap_constant]

lemma fixedHomotopyMap_recover : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.lowerSimplexTensor (fixedHomotopyMap.{w} H) = H.hom :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.lowerSimplexTensor_simplexTensorMap H.hom

end SerrePositivity.SimplicialModel.UniverseLift
