module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.HomologyBarTopAppend
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex

/-!
概要：終頂点を持つ poset 上のホモロジー bar の正次数を縮約する。
方針：末尾付加と各面の可換式を交代和にし、二つの符号を相殺する。
規約：この段階は通常のホモロジー図式だけを扱う。
使われ方：filtered bar の正次数消滅を局所から全体へ運ぶ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits Opposite SSet AlgebraicTopology
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] {J : Type u} [PartialOrder J] [OrderTop J]
  (F : J ⥤ ModuleCat.{u} R)

lemma dgHomologyBarAppend_boundary (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarAppend R F (n + 1) ≫
      AlternatingFaceMapComplex.objD (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarSimplicial R F) (n + 1) =
    AlternatingFaceMapComplex.objD (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarSimplicial R F) n ≫
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarAppend R F n + (-1 : ℤ) ^ (n + 2) • 𝟙 _ := by
  unfold AlternatingFaceMapComplex.objD
  rw [Preadditive.comp_sum, Fin.sum_univ_castSucc]
  simp only [Preadditive.comp_zsmul, Fin.val_castSucc, Fin.val_last,
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarAppend_face, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarAppend_face_last, Preadditive.sum_comp,
    Preadditive.zsmul_comp]

def dgHomologyBarTopHomotopy (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarSimplicial R F) _⦋n⦌ ⟶ (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarSimplicial R F) _⦋n + 1⦌ :=
  (-1 : ℤ) ^ (n + 1) • _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarAppend R F n

lemma dgHomologyBarTopHomotopy_positive (n : ℕ) :
    dgHomologyBarTopHomotopy R F (n + 1) ≫
      AlternatingFaceMapComplex.objD (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarSimplicial R F) (n + 1) +
    AlternatingFaceMapComplex.objD (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarSimplicial R F) n ≫
      dgHomologyBarTopHomotopy R F n = 𝟙 _ := by
  have hs : (-1 : ℤ) ^ (n + 2) = -((-1 : ℤ) ^ (n + 1)) := by
    rw [pow_succ]
    ring
  have hsq : (-1 : ℤ) ^ (n + 2) * (-1 : ℤ) ^ (n + 2) = 1 := by
    rw [← mul_pow]
    simp only [neg_mul_neg, one_mul, one_pow]
  unfold dgHomologyBarTopHomotopy
  rw [Preadditive.zsmul_comp, dgHomologyBarAppend_boundary, smul_add, smul_smul,
    hsq, one_smul, Preadditive.comp_zsmul, hs, neg_smul]
  abel

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
