module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentFirstDifferential
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentLayerAnnihilation

/-!
概要：各実 theta 列を直下一次元層へ射影すると一次列と一致する。
方針：高次 HA 項の二段下降を次数付き元へ適用する。
規約：高次項を図式から除かず、指定した層への射影での消滅を示す。
使われ方：連結射の代表元公式と通常の bar 微分の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits DifferentialGraded SSet
open HomologicalComplex CochainComplex HomComplex
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

lemma dgCoherentBarSupportedHom_layer_zero (M : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D) (r : ℤ)
    {m n : ℕ} (hmn : m < n)
    (z : (_root_.SerrePositivity.DifferentialGraded.moduleHom R D (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) M)
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D G))).X r)
    (hz : z ∈ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarHomFiltration R D G M r m)
    (x : D) (q : ℤ) (a : (_root_.SerrePositivity.DifferentialGraded.moduleDegreeEvaluation R D x q).obj M) :
    (_root_.SerrePositivity.DifferentialGraded.moduleDegreeEvaluation R D x (q + r)).map
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedProjection R D G ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerProjection R D G n)
        ((((_root_.SerrePositivity.DifferentialGraded.moduleHomπ R D (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) M)
          (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D G)) x).f r z).v
            q (q + r) rfl) a) = 0 := by
  rw [CategoryTheory.Functor.map_comp, ModuleCat.comp_apply]
  apply _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerProjection_annihilate R D G x (q + r) hmn
  exact Submodule.mem_map.mpr
    ⟨_, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomFiltration_apply R D G M r m z hz x q a, rfl⟩

lemma dgCoherentBarHigherColumn_projected_zero {n : ℕ} (s : I _⦋n + 1⦌)
    (x : D) (q : ℤ) (a : (_root_.SerrePositivity.DifferentialGraded.moduleDegreeEvaluation R D x q).obj
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D G ⟨n + 1, s⟩)) :
    (_root_.SerrePositivity.DifferentialGraded.moduleDegreeEvaluation R D x (q + 1)).map
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedProjection R D G ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerProjection R D G n)
        ((((_root_.SerrePositivity.DifferentialGraded.moduleHomπ R D
          (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D G ⟨n + 1, s⟩))
          (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D G)) x).f 1
            (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHigherColumn R D G s)).v q (q + 1) rfl) a) = 0 := by
  cases n with
  | zero =>
    simp only [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHigherColumn, Fin.sum_univ_zero, smul_zero, map_zero,
      Cochain.zero_v]
    change (_root_.SerrePositivity.DifferentialGraded.moduleDegreeEvaluation R D x (q + 1)).map
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedProjection R D G ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerProjection R D G 0) 0 = 0
    exact map_zero _
  | succ n =>
    exact dgCoherentBarSupportedHom_layer_zero R D G _ 1 (by omega)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHigherColumn R D G s) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHigherColumn_mem_filtration R D G s)
        x q a

lemma dgCoherentBarColumn_projected_first {n : ℕ} (s : I _⦋n + 1⦌)
    (x : D) (q : ℤ) (a : (_root_.SerrePositivity.DifferentialGraded.moduleDegreeEvaluation R D x q).obj
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D G ⟨n + 1, s⟩)) :
    (_root_.SerrePositivity.DifferentialGraded.moduleDegreeEvaluation R D x (q + 1)).map
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedProjection R D G ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerProjection R D G n)
        ((((_root_.SerrePositivity.DifferentialGraded.moduleHomπ R D
          (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D G ⟨n + 1, s⟩))
          (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D G)) x).f 1
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarColumn R D G ⟨n + 1, s⟩)).v q (q + 1) rfl) a) =
    (_root_.SerrePositivity.DifferentialGraded.moduleDegreeEvaluation R D x (q + 1)).map
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedProjection R D G ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerProjection R D G n)
        ((((_root_.SerrePositivity.DifferentialGraded.moduleHomπ R D
          (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D G ⟨n + 1, s⟩))
          (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D G)) x).f 1
            (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarFirstColumn R D G s)).v q (q + 1) rfl) a) := by
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarColumn_eq_first_add_higher]
  simp only [map_add]
  erw [Cochain.add_v]
  let p := (_root_.SerrePositivity.DifferentialGraded.moduleDegreeEvaluation R D x (q + 1)).map
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedProjection R D G ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerProjection R D G n)
  let f := (((_root_.SerrePositivity.DifferentialGraded.moduleHomπ R D
    (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D G ⟨n + 1, s⟩))
    (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D G)) x).f 1
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarFirstColumn R D G s)).v q (q + 1) rfl)
  let g := (((_root_.SerrePositivity.DifferentialGraded.moduleHomπ R D
    (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D G ⟨n + 1, s⟩))
    (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D G)) x).f 1
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHigherColumn R D G s)).v q (q + 1) rfl)
  change p ((f + g) a) = p (f a)
  have hadd : (f + g) a = f a + g a := rfl
  rw [hadd, map_add, dgCoherentBarHigherColumn_projected_zero R D G s x q a, add_zero]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
