module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentLayerFaceHomologyMatrix
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentFirstHomologyColumns
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.ModuleCoproductHomologyInclusions
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.HomologyBarNondegDifferential

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {J : Type u} [PartialOrder J]
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve J) ⟶
    dgNerve R (RightModule R D))

lemma dgCoherentBarFirstLayerHomology_differential (x : D) (q : ℤ) (n : ℕ) :
    dgCoherentBarFirstLayerHomologyMap R D G x q n ≫
      (dgCoherentBarNaturalLayerHomologyIso R D G x n (q + 1) (q + ((n : ℤ) + 1)) (by omega)).hom =
    (dgCoherentBarNaturalLayerHomologyIso R D G x (n + 1) q (q + ((n : ℤ) + 1)) (by omega)).hom ≫
      (dgHomologyBarNondegComplex R
        (dgCoherentBarHomologyDiagram R D G x (q + ((n : ℤ) + 1)))).d (n + 1) n := by
  let P := dgModuleCoproductHomologyIso R D (dgCoherentBarLayerFamily R D G (n + 1)) x q
  rw [← cancel_epi P.inv]
  apply Sigma.hom_ext
  intro t
  obtain ⟨s, rfl⟩ := (dgCoherentBarLayerIndexEquiv (nerve J) (n + 1)).surjective t
  simp only [P, Category.assoc, dgModuleCoproductHomologyIso_ι_inv_assoc]
  rw [← Category.assoc, dgCoherentBarFirstLayerHomology_column_sum,
    dgCoherentBarNaturalLayerHomologyIso_ι_assoc, Preadditive.sum_comp,
    dgHomologyBarNondegDifferential]
  simp only [Preadditive.zsmul_comp, Preadditive.comp_sum, Preadditive.comp_zsmul]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [Nat.cast_add, Nat.cast_one] using!
      dgCoherentBarLayerFaceHomology_matrix_zero R D G s x q
  · simpa only [Nat.cast_add, Nat.cast_one] using!
      dgCoherentBarLayerFaceHomology_matrix_succ R D G s j x q

end SerrePositivity.InfinityCategories
