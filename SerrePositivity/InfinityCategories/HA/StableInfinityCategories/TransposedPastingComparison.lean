module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PastingComparisonHomotopy
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HomotopyPrecomposition

/-! # 転置した長方形の左から外側への比較

概要：転置した比較は底辺の両端を固定し、右上を次の長方形の上辺に沿って動かす。
方針：転置と比較形状の合成を有限頂点で計算する。
規約：値域に充填性や普遍性を仮定しない。使われ方：八面体の二つ目の比較の三成分。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：転置した左から外側への比較形状は底辺の各頂点を固定する。
方針：旧横座標は零であり、時間によって変化しないことを各頂点で計算する。
規約：底辺の両端を一つの式で扱う。使われ方：始点・中間成分の恒等性。 -/
lemma transposedPastingLeftToOuterShape_bottom (j : Fin 2) :
    ((stdSimplex.δ j.rev ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge) ▷ (Δ[1] : SSet.{u})) ≫
      (((β_ (Δ[1] : SSet.{u}) Δ[1]).hom ▷ Δ[1]) ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingLeftToOuterShape) =
    snd Δ[0] Δ[1] ≫ SSet.const
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex ((β_ (Δ[1] : SSet.{u}) Δ[1]).hom ≫
        (stdSimplex.δ (2 : Fin 3) ▷ Δ[1])) j 0) := by
  apply CartesianMonoidalCategory.hom_ext
  all_goals
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.stdSimplex_hom_ext_vertices
    apply ConcreteCategory.hom_ext
    rintro ⟨p, q⟩
    obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective p
    obtain ⟨k, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective q
    fin_cases j <;> fin_cases i <;> fin_cases k <;> rfl

/-- 概要：転置した比較ホモトピーは底辺の各頂点で定値。
方針：形状の固定式を長方形で評価する。
規約：単体的な道の厳密な等号。使われ方：八面体の二成分を恒等射に同定する。 -/
lemma transposedPastingLeftToOuterHomotopy_bottom {X : SSet.{u}}
    (F : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ X) (j : Fin 2) :
    ((stdSimplex.δ j.rev ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge) ▷ (Δ[1] : SSet.{u})) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableHomotopyPrecomp (β_ (Δ[1] : SSet.{u}) Δ[1]).hom
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingLeftToOuterHomotopy F)).h =
    snd Δ[0] Δ[1] ≫ SSet.const
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex ((β_ (Δ[1] : SSet.{u}) Δ[1]).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 2) j 0) := by
  change _ ≫ (((β_ (Δ[1] : SSet.{u}) Δ[1]).hom ▷ Δ[1]) ≫
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingLeftToOuterShape ≫ F)) = _
  rw [← Category.assoc ((β_ (Δ[1] : SSet.{u}) Δ[1]).hom ▷ Δ[1]),
    ← Category.assoc, transposedPastingLeftToOuterShape_bottom,
    Category.assoc, SSet.const_comp]
  rfl

/-- 概要：転置した比較の右上の道は右面の上辺。
方針：右上の頂点は転置で変わらないことを使う。
規約：端点の表示を変えない。使われ方：二つの cofiber を結ぶ第二の射。 -/
lemma transposedPastingLeftToOuterHomotopy_target {X : SSet.{u}}
    (F : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    ((stdSimplex.δ (0 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge) ▷ (Δ[1] : SSet.{u})) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableHomotopyPrecomp (β_ (Δ[1] : SSet.{u}) Δ[1]).hom
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingLeftToOuterHomotopy F)).h =
    snd Δ[0] Δ[1] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 0) := by
  change _ ≫ (((β_ (Δ[1] : SSet.{u}) Δ[1]).hom ▷ Δ[1]) ≫ _) = _
  rw [← Category.assoc]
  have h : ((stdSimplex.δ (0 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge) ▷ (Δ[1] : SSet.{u})) ≫
      ((β_ (Δ[1] : SSet.{u}) Δ[1]).hom ▷ Δ[1]) =
    (stdSimplex.δ (0 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge) ▷ Δ[1] := by
    apply CartesianMonoidalCategory.hom_ext
    all_goals try apply CartesianMonoidalCategory.hom_ext
    all_goals
      apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.stdSimplex_hom_ext_vertices
      apply ConcreteCategory.hom_ext
      rintro ⟨p, q⟩
      obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective p
      obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective q
      fin_cases i
      fin_cases j <;> rfl
  rw [h]
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingLeftToOuterHomotopy_target F

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
