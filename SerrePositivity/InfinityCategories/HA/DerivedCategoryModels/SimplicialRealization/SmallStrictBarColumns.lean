module

public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarDiagram
import all SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarDiagram

/-!
# 小さい strict 図式の同じ coherent bar の一次列

## 概要
係数環と別の宇宙0の射列でも、高次 prefix が消え、同じ通常の面と最初の射だけが残る。

## 方針
元の高次零成分を shift ブロックへ移し、有限和を第零項へ制限する。

## 規約
既存の theta・shift ブロック・符号をそのまま保つ。

## 使われ方
HA 1.2.4。単体的置換の微分と native coherent bar の同じ微分の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits SerrePositivity.DifferentialGraded SSet
open scoped _root_.Simplicial
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Project.DerivedCategories
variable (A : Type u) [CommRing A] {J : Type} [SmallCategory J]
variable (F : J ⥤ ModuleCategory A PUnit.{1})

/-- strict な小さい射列でも、高次 prefix の同じ Hom 成分は零。 -/
theorem smallStrictBarPrefixHom_eq_zero {n : ℕ}
    (s : ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) _⦋n⦌)
    (k : ℕ) (hk : 0 < k) (h : k + 1 ≤ n) :
    dgCoherentBarPrefixHom A PUnit.{1} (smallStrictBarDiagram A F) s k h = 0 := by
  unfold dgCoherentBarPrefixHom
  rw [coherentDiagramTop, smallStrictBarDiagram_higher A F hk]
  exact map_zero _

/-- 高次 prefix の同じ shift ブロックは零。 -/
theorem smallStrictBarPrefixBlock_eq_zero {n : ℕ}
    (s : ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) _⦋n⦌)
    (k : ℕ) (hk : 0 < k) (h : k + 1 ≤ n) :
    dgCoherentBarPrefixBlock A PUnit.{1} (smallStrictBarDiagram A F) s k h = 0 := by
  unfold dgCoherentBarPrefixBlock
  rw [smallStrictBarPrefixHom_eq_zero A F s k hk h]
  simp only [moduleHomShiftBlock, zero_compose, compose_zero]

/-- 高次 prefix の同じ直和への列は零。 -/
theorem smallStrictBarPrefixColumn_eq_zero {n : ℕ}
    (s : ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) _⦋n⦌)
    (k : ℕ) (hk : 0 < k) (h : k + 1 ≤ n) :
    dgCoherentBarPrefixColumn A PUnit.{1} (smallStrictBarDiagram A F) s k h = 0 := by
  unfold dgCoherentBarPrefixColumn
  rw [smallStrictBarPrefixBlock_eq_zero A F s k hk h, map_zero]

/-- 元の theta の列は、同じ面と先頭の射の一次列だけになる。 -/
theorem smallStrictBarColumn {n : ℕ}
    (s : ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) _⦋n + 1⦌) :
    dgCoherentBarColumn A PUnit.{1} (smallStrictBarDiagram A F) ⟨n + 1, s⟩ =
      (∑ i : Fin (n + 1), ((n : ℤ) + 1 + (i.val : ℤ) + 1).negOnePow •
        dgCoherentBarFaceColumn A PUnit.{1} (smallStrictBarDiagram A F) s i) +
      ((n : ℤ) + 1).negOnePow •
        dgCoherentBarPrefixColumn A PUnit.{1} (smallStrictBarDiagram A F) s 0 (by omega) := by
  have hs : (∑ k : Fin (n + 1),
      dgCoherentBarPrefixColumn A PUnit.{1} (smallStrictBarDiagram A F) s k.val (by omega)) =
      dgCoherentBarPrefixColumn A PUnit.{1} (smallStrictBarDiagram A F) s 0 (by omega) := by
    apply Fintype.sum_eq_single (0 : Fin (n + 1))
    intro i hi
    apply smallStrictBarPrefixColumn_eq_zero A F s i.val
    have h0 : i.val ≠ 0 := fun h => hi (Fin.ext h)
    omega
  change (∑ i : Fin (n + 1), ((n : ℤ) + 1 + (i.val : ℤ) + 1).negOnePow •
    dgCoherentBarFaceColumn A PUnit.{1} (smallStrictBarDiagram A F) s i) +
      ((n : ℤ) + 1).negOnePow • (∑ k : Fin (n + 1),
        dgCoherentBarPrefixColumn A PUnit.{1} (smallStrictBarDiagram A F) s k.val (by omega)) = _
  rw [hs]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
