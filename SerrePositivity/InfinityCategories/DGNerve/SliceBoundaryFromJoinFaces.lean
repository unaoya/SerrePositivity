module
public import SerrePositivity.InfinityCategories.Core.JoinLifting

/-! # join の面から slice の境界充填へ

概要：join 上の写像が境界の全ての面と一致すれば、slice の境界充填を与える。
方針：一つの面から右因子の固定条件を得て curry し、全ての面の一致を uncurry で比較する。
規約：HTT §1.2.13・§2.1.2。使われ方：dg nerve の直接の二セル充填を終対象性へ戻す。
-/

@[expose] public section
noncomputable section

universe u

namespace SerrePositivity.InfinityCategories.DGNerve

open CategoryTheory
open scoped Simplicial

/-- 概要：join の全ての境界面が指定された slice 境界に一致する写像は、右因子上で元の図式に等しい。
方針：零番目の面の等式を右因子包含で評価し、uncurry の固定条件を使う。
規約：HTT §2.1.2。使われ方：join の充填写像を slice へ curry するための固定条件。 -/
lemma joinBoundaryFaces_fixed {n : ℕ} {K X : SSet.{u}} (p : K ⟶ X)
    (b : (SSet.boundary (n + 1) : SSet) ⟶ sliceOver p) (F : join Δ[n + 1] K ⟶ X)
    (hfaces : ∀ j : Fin (n + 2), joinMap (SSet.stdSimplex.δ j) (𝟙 K) ≫ F =
      joinMap (SSet.boundary.ι j) (𝟙 K) ≫ sliceOverUncurry b) :
    joinInr Δ[n + 1] K ≫ F = p := by
  have H := congrArg (fun T => joinInr (Δ[n] : SSet.{u}) K ≫ T) (hfaces 0)
  simpa only [← Category.assoc, joinInr_joinMap, Category.id_comp,
    sliceOverUncurry_fixed] using H

/-- 概要：join の面が元の slice 境界の面に一致する写像を curry すると元の境界を延長する。
方針：境界の面による外延性と uncurry の単射性を使う。
規約：HTT §2.1.2。使われ方：直接構成した充填の境界条件の最終検証。 -/
lemma sliceOverCurry_boundary_of_joinFaces {n : ℕ} {K X : SSet.{u}} (p : K ⟶ X)
    (b : (SSet.boundary (n + 1) : SSet) ⟶ sliceOver p) (F : join Δ[n + 1] K ⟶ X)
    (hfaces : ∀ j : Fin (n + 2), joinMap (SSet.stdSimplex.δ j) (𝟙 K) ≫ F =
      joinMap (SSet.boundary.ι j) (𝟙 K) ≫ sliceOverUncurry b) :
    (SSet.boundary (n + 1)).ι ≫ sliceOverCurry F (joinBoundaryFaces_fixed p b F hfaces) = b := by
  apply SSet.boundary.hom_ext
  intro j
  rw [← Category.assoc, SSet.boundary.ι_ι]
  apply sliceOverUncurry_injective p
  rw [sliceOverUncurry_precomp, sliceOverUncurry_curry, sliceOverUncurry_precomp]
  exact hfaces j

end SerrePositivity.InfinityCategories.DGNerve
