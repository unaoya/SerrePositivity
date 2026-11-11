module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.ProductBoundaryCotensor
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveProductParameter

/-!
# 中断した任意モデル源への一般化：NerveMovingBoundary

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Gluing all whole facet systems with a moving parameter and moving values。

## 方針（定義・証明）
bar型の鎖パラメータと整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0480][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0480
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Gluing all whole facet systems with a moving parameter and moving values
-/

@[expose] public section
universe w uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open SerrePositivity.NerveSimplexEndpoint
open SerrePositivity.SimplicialModel.NerveCylinderBoundary
open SerrePositivity.SimplicialModel.NerveBiparameterMaps

namespace SerrePositivity.SimplicialModel.NerveMovingBoundary
variable {D : Type uD} [Category.{vD} D] (K F : D ⥤ SSet.{w}) {n : ℕ}

abbrev Compatible (faces : Fin (n + 3) → NerveBiparameter.System
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product K (SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)))) F) : Prop :=
  ∀ (j k : Fin (n + 3)) (hjk : j < k),
    faces j ≫ restriction _ _ F (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical (SSet.stdSimplex.δ
      (k.pred (Fin.ne_zero_of_lt hjk))) K) =
    faces k ≫ restriction _ _ F (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical (SSet.stdSimplex.δ
      (j.castPred (Fin.ne_last_of_lt hjk))) K)

variable (faces : Fin (n + 3) → NerveBiparameter.System
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product K (SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)))) F)
  (hf : Compatible K F faces)

include hf in
lemma component_compatible (s : Index D) :
    ProductBoundaryCotensor.Compatible (fun k => (faces k).app s) := by
  intro j k hjk
  exact congr_app (hf j k hjk) s

/-- Glue the actual boundary product, keeping all whole facets in every external degree. -/
def boundary : NerveBiparameter.System (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product K (SSet.boundary (n + 2)).toSSet) F where
  app s := ProductBoundaryCotensor.standardDesc (fun k => (faces k).app s)
    (component_compatible K F faces hf s)
  naturality {s t} f := by
    apply ProductBoundaryCotensor.hom_ext
    intro k
    simp only [Category.assoc, ProductBoundaryCotensor.standardDesc_fac]
    have hn := (restriction (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product K (SSet.stdSimplex.obj (SimplexCategory.mk (n + 1))))
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product K (SSet.boundary (n + 2)).toSSet) F (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical (SSet.boundary.ι k) K)).naturality f
    rw [restriction_app, restriction_app] at hn
    have hg := ProductBoundaryCotensor.standardDesc_fac (fun k => (faces k).app s)
      (component_compatible K F faces hf s) k
    exact ((faces k).naturality f).trans
      ((congrArg (fun a => a ≫ (NerveBiparameter.values
        (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product K (SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)))) F).map f) hg.symm).trans
        ((Category.assoc _ _ _).trans (congrArg (fun a => ProductBoundaryCotensor.standardDesc
          (fun k => (faces k).app s) (component_compatible K F faces hf s) ≫ a) hn.symm)))

lemma boundary_face (k : Fin (n + 3)) : boundary K F faces hf ≫ restriction _ _ F
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical (SSet.boundary.ι k) K) = faces k := by
  apply NatTrans.ext
  funext s
  exact ProductBoundaryCotensor.standardDesc_fac (fun k => (faces k).app s)
    (component_compatible K F faces hf s) k

lemma hom_ext {m : ℕ}
    {a b : NerveBiparameter.System (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product K (SSet.boundary (m + 1)).toSSet) F}
    (h : ∀ k : Fin (m + 2), a ≫ restriction _ _ F (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical (SSet.boundary.ι k) K) =
      b ≫ restriction _ _ F (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical (SSet.boundary.ι k) K)) : a = b := by
  apply NatTrans.ext
  funext s
  apply ProductBoundaryCotensor.hom_ext
  intro k
  exact congr_app (h k) s

/-- A common whole natural vertex boundary survives the actual facet gluing. -/
lemma boundary_vertices (V : D ⥤ SSet.{w}) (i : V ⟶ K) (b : V ⟶ F)
    (hv : ∀ k : Fin (n + 3), faces k ≫ restriction _ _ F
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.horizontal V K i (SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)))) =
      NerveNaturalBoundary.ofNatTrans _ _
        (NerveProductParameter.projection V
          (SSet.stdSimplex.obj (SimplexCategory.mk (n + 1))) ≫ b)) :
    boundary K F faces hf ≫ restriction _ _ F
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.horizontal V K i (SSet.boundary (n + 2)).toSSet) =
      NerveNaturalBoundary.ofNatTrans _ _
        (NerveProductParameter.projection V (SSet.boundary (n + 2)).toSSet ≫ b) := by
  apply hom_ext V F
  intro k
  rw [Category.assoc, restriction_comp, ← _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.commute V K i (SSet.boundary.ι k),
    ← restriction_comp, ← Category.assoc, boundary_face, hv k, restrict_natural]
  apply congrArg (NerveNaturalBoundary.ofNatTrans _ _)
  rw [← Category.assoc, NerveProductParameter.projection_vertical]

end SerrePositivity.SimplicialModel.NerveMovingBoundary
