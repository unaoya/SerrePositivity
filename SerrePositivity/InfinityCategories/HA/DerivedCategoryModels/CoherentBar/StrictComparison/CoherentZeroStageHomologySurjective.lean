module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentStageHomologyDescent

/-!
概要：filtered coherent bar のホモロジーは零単体次元の段階から生成される。
方針：実長完全列による一段下降を有限 support の上限について帰納する。
規約：高次 HA 項を残した実複体を扱い、有界性や形式的収束を仮定しない。
使われ方：最終ホモロジーを一次微分の余核として同定する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits DifferentialGraded SSet
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {J : Type u} [PartialOrder J] [IsFiltered J]
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve J) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

lemma dgCoherentBarStageHomology_from_zero (x : D) (q : ℤ) (n : ℕ)
    (a : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedStageComplex R D G x n).homology q) :
    ∃ b : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedStageComplex R D G x 0).homology q,
      HomologicalComplex.homologyMap (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedStageInclusion R D G x 0) q b =
      HomologicalComplex.homologyMap (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedStageInclusion R D G x n) q a := by
  induction n with
  | zero => exact ⟨a, rfl⟩
  | succ n ih =>
    obtain ⟨b, hb⟩ := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStageHomology_descent R D G x q n a
    have h : HomologicalComplex.homologyMap
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedStageInclusion R D G x n) q b =
      HomologicalComplex.homologyMap
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedStageInclusion R D G x (n + 1)) q a := by
      have h := congrArg (fun z => HomologicalComplex.homologyMap
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedStageInclusion R D G x (n + 2)) q z) hb
      simpa only [← ModuleCat.comp_apply, ← HomologicalComplex.homologyMap_comp,
        _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedStageMap_inclusion] using! h
    obtain ⟨c, hc⟩ := ih b
    exact ⟨c, hc.trans h⟩

lemma dgCoherentBarZeroStageHomology_surjective (x : D) (q : ℤ) :
    Function.Surjective
      (HomologicalComplex.homologyMap (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedStageInclusion R D G x 0) q) := by
  intro a
  obtain ⟨n, b, hb⟩ := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStageHomology_exhaustive R D G x q a
  obtain ⟨c, hc⟩ := dgCoherentBarStageHomology_from_zero R D G x q n b
  exact ⟨c, hc.trans hb⟩

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
