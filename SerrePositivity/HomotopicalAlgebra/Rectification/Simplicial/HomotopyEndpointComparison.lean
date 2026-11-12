module

public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.LargeParameterRelativeChoice

public import SerrePositivity.HomotopicalAlgebra.Simplicial.HomotopyFaces

/-!
# 中断した任意モデル源への一般化：HomotopyEndpointComparison

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Compare actual selected homotopies relative to both entire endpoint families。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0404][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0404
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Compare actual selected homotopies relative to both entire endpoint families

Only finite fillers in the small value space are used. Both original
homotopies remain literal parameter faces of the comparison.
-/

@[expose] public section
universe r w v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory

namespace SerrePositivity.SimplicialModel.HomotopyEndpointComparison

variable {P : SSet.{v}} (hp : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.BoundaryFillers P) {K : SSet.{max w v}}
  {e₀ e₁ : K ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} P} (H H' : SSet.Homotopy e₀ e₁)

/-- Both actual homotopies are retained and both original endpoint families stay fixed. -/
abbrev homotopy : SSet.Homotopy H.h H'.h :=
  LargeParameterRelativeChoice.homotopy hp (K ◁ (SSet.boundary.{max w v} 1).ι)
    (LargeParameterHomotopy.boundaryMap e₀ e₁) H.h H'.h (boundary_eq H) (boundary_eq H')

lemma fixed_endpoints : (K ◁ (SSet.boundary.{max w v} 1).ι) ▷
    SSet.stdSimplex.{max w v}.obj (SimplexCategory.mk 1) ≫ (homotopy hp H H').h =
      (K ⊗ (SSet.boundary.{max w v} 1).toSSet) ◁
          (SSet.stdSimplex.isTerminalObj₀.from _ ≫ RelativeChoiceSpace.pointUnitIso.hom) ≫
        (ρ_ _).hom ≫ LargeParameterHomotopy.boundaryMap e₀ e₁ :=
  LargeParameterRelativeChoice.homotopy_relative _ _ _ _ _ _ _

end SerrePositivity.SimplicialModel.HomotopyEndpointComparison
