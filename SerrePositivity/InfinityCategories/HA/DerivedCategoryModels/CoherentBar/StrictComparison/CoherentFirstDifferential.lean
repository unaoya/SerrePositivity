module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentFiltration

/-!
概要：coherent bar の theta を一次成分と高次 HA 成分に分ける。
方針：元の prefix 和の零番を取り出し、残りの全項の支持を二段下へ送る。
規約：一次成分を単独の二乗零微分とは主張しない。高次項は全て保持する。
使われ方：単体次元フィルトレーションに誘導されるホモロジー微分の同定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

def dgCoherentBarFirstColumn {n : ℕ} (s : I _⦋n + 1⦌) :
    (_root_.SerrePositivity.DifferentialGraded.moduleHom R D
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D G ⟨n + 1, s⟩))
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D G))).X 1 :=
  (∑ i : Fin (n + 1), ((n : ℤ) + 1 + (i.val : ℤ) + 1).negOnePow •
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFaceColumn R D G s i) +
  ((n : ℤ) + 1).negOnePow • _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixColumn R D G s 0 (by omega)

def dgCoherentBarHigherColumn {n : ℕ} (s : I _⦋n + 1⦌) :
    (_root_.SerrePositivity.DifferentialGraded.moduleHom R D
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D G ⟨n + 1, s⟩))
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D G))).X 1 :=
  ((n : ℤ) + 1).negOnePow • ∑ k : Fin n,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixColumn R D G s (k.val + 1) (by omega)

lemma dgCoherentBarColumn_eq_first_add_higher {n : ℕ} (s : I _⦋n + 1⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarColumn R D G ⟨n + 1, s⟩ =
      dgCoherentBarFirstColumn R D G s + dgCoherentBarHigherColumn R D G s := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarColumn, dgCoherentBarFirstColumn, dgCoherentBarHigherColumn]
  rw [Fin.sum_univ_succ (fun k : Fin (n + 1) =>
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixColumn R D G s k.val (by omega)), smul_add, add_assoc]
  rfl

set_option maxHeartbeats 800000 in
-- 元の coproduct Hom end と高次係数の支持を照合する局所上限。
lemma dgCoherentBarHigherColumn_mem_filtration {n : ℕ} (s : I _⦋n + 1⦌) :
    dgCoherentBarHigherColumn R D G s ∈
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarHomFiltration R D G (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D G ⟨n + 1, s⟩)
        1 (n - 1) := by
  unfold dgCoherentBarHigherColumn
  rw [Units.smul_def]
  apply (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarHomFiltration R D G
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D G ⟨n + 1, s⟩) 1 (n - 1)).toAddSubgroup.zsmul_mem
  apply Submodule.sum_mem
  intro k _
  exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarHomFiltration_mono R D G
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D G ⟨n + 1, s⟩) 1 (by omega)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarPrefixColumn_mem_filtration R D G s (k.val + 1) (by omega))

lemma dgCoherentBarColumn_sub_first_mem_filtration {n : ℕ} (s : I _⦋n + 1⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarColumn R D G ⟨n + 1, s⟩ - dgCoherentBarFirstColumn R D G s ∈
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarHomFiltration R D G (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D G ⟨n + 1, s⟩)
        1 (n - 1) := by
  rw [dgCoherentBarColumn_eq_first_add_higher, add_sub_cancel_left]
  exact dgCoherentBarHigherColumn_mem_filtration R D G s

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
