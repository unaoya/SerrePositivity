module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PastingSplitProjection

/-! # 長方形の上辺の合成

概要：長方形の二つの上辺の合成は外側上辺となる。
方針：上側二単体を端点つきの合成二単体として読む。
規約：値域への仮定は不要。使われ方：幾何学的な射影と標準余積射影の一致。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：長方形の上側二単体は左・右・外側上辺の合成二単体である。
方針：三つの面をそれぞれの上辺への制限と照合する。
規約：quasicategory 性は不要。使われ方：長方形の上辺の合成式。 -/
def pastingTopCompStruct {X : SSet.{u}}
    (F : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareTopArrow (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 2)).CompStruct
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareTopArrow (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 0)) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareTopArrow (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 1)) where
  simplex := SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingTopTriangle F)
  d₂ := by
    change X.δ 2 (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingTopTriangle F)) = _
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare_topEdge]
    exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareTopArrow_edge (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 2)).symm
  d₀ := by
    change X.δ 0 (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingTopTriangle F)) = _
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare_topEdge]
    exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareTopArrow_edge (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 0)).symm
  d₁ := by
    change X.δ 1 (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingTopTriangle F)) = _
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare_topEdge]
    exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareTopArrow_edge (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 1)).symm

/-- 概要：長方形の二つの上辺の類の合成は外側上辺の類。
方針：合成二単体をホモトピー圏で読む。
規約：値域への仮定なし。使われ方：左上辺と右上辺の厳密な関係。 -/
lemma pastingTop_hom_comp {X : SSet.{u}}
    (F : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoTop (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 2) ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoTop (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 0) =
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoTop (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 1) :=
  SSet.Truncated.HomotopyCategory.homMk_comp_homMk (pastingTopCompStruct F)

/-- 概要：列四角形を外側に持つ長方形の上側合成は恒等射を表す。
方針：合成式の外側上辺の一次単体を恒等辺と照合する。
規約：端点の等号は Arrow の等号に含める。使われ方：指定された切断の保持。 -/
lemma pastingTop_composite_arrow_of_outer_column {X : SSet.{u}}
    (F : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ X) (g : (Δ[1] : SSet.{u}) ⟶ X)
    (ho : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 1 = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareColumnDiagram g) :
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoTop (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 2) ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoTop (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 0)) =
      Arrow.mk (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 2) 0 1)) := by
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 1 =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 1) 0 1) := by
    rw [ho]
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareColumnDiagram, ← Category.assoc, lift_snd, SSet.const_comp]
    rfl
  have he : (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareTopArrow (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 1)).edge =
      (SSet.Truncated.Edge.id (X := (truncation 2).obj X)
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 2) 0 1)).edge := by
    rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareTopArrow_edge, hi]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one _
  rw [pastingTop_hom_comp]
  have ha := SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareTopArrow (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 1))
    (SSet.Truncated.Edge.id (X := (truncation 2).obj X)
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 2) 0 1)) he
  rw [SSet.Truncated.HomotopyCategory.homMk_id] at ha
  exact ha

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
