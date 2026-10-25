module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.HomologyBarNondegFaces

/-!
概要：poset 上の非退化ホモロジー bar の実微分の交代面和公式。
方針：canonical splitting の射影を、面射の非退化部分への制限で消去する。
規約：非退化複体自体の微分を計算し、別の模型を導入しない。
使われ方：実一次ホモロジー複体との微分の一致。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits Opposite SSet AlgebraicTopology
open scoped Simplicial
variable (R : Type u) [CommRing R] {J : Type u} [PartialOrder J]
  (F : J ⥤ ModuleCat.{u} R)

lemma dgHomologyBarNondegInclusion_projection (n : ℕ) :
    dgHomologyBarNondegInclusion R F n ≫
      (dgHomologyBarSplitting R F).πSummand (SimplicialObject.Splitting.IndexSet.id (op ⦋n⦌)) =
        𝟙 _ := by
  have h := (dgHomologyBarSplitting R F).cofan_inj_πSummand_eq_id
    (SimplicialObject.Splitting.IndexSet.id (op ⦋n⦌))
  simpa only [SimplicialObject.Splitting.cofan_inj_id] using! h

lemma dgHomologyBarNondegDifferential (n : ℕ) :
    (dgHomologyBarNondegComplex R F).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • dgHomologyBarNondegFaceMap R F n i := by
  change (dgHomologyBarSplitting R F).d (n + 1) n = _
  rw [SimplicialObject.Splitting.d, SimplicialObject.Splitting.cofan_inj_id]
  change dgHomologyBarNondegInclusion R F (n + 1) ≫
    (AlternatingFaceMapComplex.obj (dgHomologyBarSimplicial R F)).d (n + 1) n ≫ _ = _
  rw [AlternatingFaceMapComplex.obj_d_eq, Preadditive.sum_comp, Preadditive.comp_sum]
  apply Finset.sum_congr rfl
  intro i hi
  erw [Preadditive.zsmul_comp, Preadditive.comp_zsmul,
    ← Category.assoc, ← dgHomologyBarNondegFaceMap_inclusion, Category.assoc,
    dgHomologyBarNondegInclusion_projection, Category.comp_id]

end SerrePositivity.InfinityCategories
