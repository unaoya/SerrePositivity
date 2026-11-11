module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentLayerFaceHomologyMatrix
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentFirstHomologyColumns
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.ModuleCoproductHomologyInclusions
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.HomologyBarNondegDifferential

/-!
概要：実一次ホモロジー作用素は自然な層同型を通して非退化 H(G) bar の微分と一致する。
方針：各実列で有限交代面和を比較し、実直和ホモロジーの普遍性を使う。
規約：元の coherent 入力・実一次作用素・全整数次数を保持する。
使われ方：filtered bar の正次数完全性と有限 support の下降。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits DifferentialGraded SSet
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {J : Type u} [PartialOrder J]
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve J) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

lemma dgCoherentBarFirstLayerHomology_differential (x : D) (q : ℤ) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarFirstLayerHomologyMap R D G x q n ≫
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNaturalLayerHomologyIso R D G x n (q + 1) (q + ((n : ℤ) + 1)) (by omega)).hom =
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNaturalLayerHomologyIso R D G x (n + 1) q (q + ((n : ℤ) + 1)) (by omega)).hom ≫
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarNondegComplex R
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyDiagram R D G x (q + ((n : ℤ) + 1)))).d (n + 1) n := by
  let P := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgModuleCoproductHomologyIso R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerFamily R D G (n + 1)) x q
  rw [← cancel_epi P.inv]
  apply Sigma.hom_ext
  intro t
  obtain ⟨s, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerIndexEquiv (nerve J) (n + 1)).surjective t
  simp only [P, Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgModuleCoproductHomologyIso_ι_inv_assoc]
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarFirstLayerHomology_column_sum,
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNaturalLayerHomologyIso_ι_assoc, Preadditive.sum_comp,
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarNondegDifferential]
  simp only [Preadditive.zsmul_comp, Preadditive.comp_sum, Preadditive.comp_zsmul]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [Nat.cast_add, Nat.cast_one] using!
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerFaceHomology_matrix_zero R D G s x q
  · simpa only [Nat.cast_add, Nat.cast_one] using!
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerFaceHomology_matrix_succ R D G s j x q

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
