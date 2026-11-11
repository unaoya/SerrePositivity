module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentCutTransition
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentCutLayerProjection

/-!
概要：隣接二段と最高次元層の間の、微分変更前の分裂射と分解公式。
方針：単体次元が n 以下か n+1 に等しいかで同じ直和添字を分ける。
規約：後続では分裂射の閉性を要求せず、全斉次作用との可換性だけを使う。
使われ方：実 MC 段階の ModuleGradedSplit。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits Preadditive DifferentialGraded SSet
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

@[reassoc]
lemma dgCoherentBarCutProjection_ι_of_not (n : ℕ) (s : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedIndex I)
    (hs : ¬ s.val.1 ≤ n) :
    Sigma.ι (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedFamily R D G) s ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutProjection R D G n = 0 := by
  classical
  simp only [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutProjection, Sigma.ι_comp_desc, dif_neg hs]

lemma dgCoherentBarLayerInclusion_cut_recover (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerInclusion R D G n ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutProjection R D G n ≫
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutInclusion R D G n = _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerInclusion R D G n := by
  apply Sigma.hom_ext
  intro s
  have hs : s.val.val.1 ≤ n := Nat.le_of_eq s.property
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerInclusion_ι_assoc,
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutProjection_ι_assoc R D G n ⟨s.val, hs⟩,
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutInclusion_ι, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerInclusion_ι]

@[reassoc]
lemma dgBarLayerProjection_ι_of_ne (n : ℕ) (s : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedIndex I)
    (hs : s.val.1 ≠ n) :
    Sigma.ι (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedFamily R D G) s ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerProjection R D G n = 0 :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerProjection_ι_of_ne R D G n s hs

def dgCoherentBarCutGradedRetraction (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutGraded R D G (n + 1) ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutGraded R D G n :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutInclusion R D G (n + 1) ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutProjection R D G n

def dgCoherentBarCutGradedSection (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerGraded R D G (n + 1) ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutGraded R D G (n + 1) :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerInclusion R D G (n + 1) ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutProjection R D G (n + 1)

lemma dgCoherentBarCutGraded_inclusion_retraction (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutGradedMap R D G (Nat.le_succ n) ≫
      dgCoherentBarCutGradedRetraction R D G n = 𝟙 _ := by
  dsimp only [dgCoherentBarCutGradedRetraction]
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutGradedMap_inclusion,
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutInclusion_projection]

lemma dgCoherentBarCutGraded_section_projection (n : ℕ) :
    dgCoherentBarCutGradedSection R D G n ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutToLayerGraded R D G (n + 1) = 𝟙 _ := by
  dsimp only [dgCoherentBarCutGradedSection, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutToLayerGraded]
  calc
    _ = (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerInclusion R D G (n + 1) ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutProjection R D G (n + 1) ≫
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutInclusion R D G (n + 1)) ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerProjection R D G (n + 1) := by
      simp only [Category.assoc]
    _ = _ := by rw [dgCoherentBarLayerInclusion_cut_recover, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerInclusion_projection]

lemma dgCoherentBarCutGraded_section_retraction (n : ℕ) :
    dgCoherentBarCutGradedSection R D G n ≫ dgCoherentBarCutGradedRetraction R D G n = 0 := by
  dsimp only [dgCoherentBarCutGradedSection, dgCoherentBarCutGradedRetraction]
  have h := congrArg (fun f : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerGraded R D G (n + 1) ⟶
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedGraded R D G => f ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutProjection R D G n)
    (dgCoherentBarLayerInclusion_cut_recover R D G (n + 1))
  rw [Category.assoc, Category.assoc] at h
  rw [Category.assoc, h]
  apply Sigma.hom_ext
  intro s
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerInclusion_ι_assoc, dgCoherentBarCutProjection_ι_of_not]
  · simp only [comp_zero]
  · omega

lemma dgCoherentBarCutGraded_inclusion_projection (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutGradedMap R D G (Nat.le_succ n) ≫
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutToLayerGraded R D G (n + 1) = 0 := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutToLayerGraded]
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutGradedMap_inclusion]
  apply Sigma.hom_ext
  intro s
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutInclusion_ι_assoc, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerProjection_ι_of_ne]
  · simp only [comp_zero]
  · omega

lemma dgCoherentBarCutGraded_decomposition (n : ℕ) :
    dgCoherentBarCutGradedRetraction R D G n ≫
        _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutGradedMap R D G (Nat.le_succ n) +
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutToLayerGraded R D G (n + 1) ≫ dgCoherentBarCutGradedSection R D G n = 𝟙 _ := by
  classical
  apply Sigma.hom_ext
  intro s
  dsimp only [dgCoherentBarCutGradedRetraction, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutGradedMap,
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutToLayerGraded, dgCoherentBarCutGradedSection]
  simp only [Preadditive.comp_add, Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutInclusion_ι_assoc,
    Category.comp_id]
  by_cases hs : s.val.val.1 ≤ n
  · have hn : s.val.val.1 ≠ n + 1 := by omega
    rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutProjection_ι_assoc R D G n ⟨s.val, hs⟩,
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutInclusion_ι_assoc, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutProjection_ι R D G (n + 1) s,
      dgBarLayerProjection_ι_of_ne_assoc R D G (n + 1) s.val hn,
      zero_comp, add_zero]
  · have hn : s.val.val.1 = n + 1 := by omega
    rw [dgCoherentBarCutProjection_ι_of_not_assoc R D G n s.val hs,
      zero_comp, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerProjection_ι_assoc R D G (n + 1) ⟨s.val, hn⟩,
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerInclusion_ι_assoc, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutProjection_ι R D G (n + 1) s,
      zero_add]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
