module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentCutTransition
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentCutLayerProjection

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits Preadditive DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

@[reassoc]
lemma dgCoherentBarCutProjection_ι_of_not (n : ℕ) (s : dgCoherentBarNormalizedIndex I)
    (hs : ¬ s.val.1 ≤ n) :
    Sigma.ι (dgCoherentBarNormalizedFamily R D G) s ≫ dgCoherentBarCutProjection R D G n = 0 := by
  classical
  simp only [dgCoherentBarCutProjection, Sigma.ι_comp_desc, dif_neg hs]

lemma dgCoherentBarLayerInclusion_cut_recover (n : ℕ) :
    dgCoherentBarLayerInclusion R D G n ≫ dgCoherentBarCutProjection R D G n ≫
      dgCoherentBarCutInclusion R D G n = dgCoherentBarLayerInclusion R D G n := by
  apply Sigma.hom_ext
  intro s
  have hs : s.val.val.1 ≤ n := Nat.le_of_eq s.property
  rw [dgCoherentBarLayerInclusion_ι_assoc,
    dgCoherentBarCutProjection_ι_assoc R D G n ⟨s.val, hs⟩,
    dgCoherentBarCutInclusion_ι, dgCoherentBarLayerInclusion_ι]

@[reassoc]
lemma dgBarLayerProjection_ι_of_ne (n : ℕ) (s : dgCoherentBarNormalizedIndex I)
    (hs : s.val.1 ≠ n) :
    Sigma.ι (dgCoherentBarNormalizedFamily R D G) s ≫ dgCoherentBarLayerProjection R D G n = 0 :=
  dgCoherentBarLayerProjection_ι_of_ne R D G n s hs

def dgCoherentBarCutGradedRetraction (n : ℕ) :
    dgCoherentBarCutGraded R D G (n + 1) ⟶ dgCoherentBarCutGraded R D G n :=
  dgCoherentBarCutInclusion R D G (n + 1) ≫ dgCoherentBarCutProjection R D G n

def dgCoherentBarCutGradedSection (n : ℕ) :
    dgCoherentBarLayerGraded R D G (n + 1) ⟶ dgCoherentBarCutGraded R D G (n + 1) :=
  dgCoherentBarLayerInclusion R D G (n + 1) ≫ dgCoherentBarCutProjection R D G (n + 1)

lemma dgCoherentBarCutGraded_inclusion_retraction (n : ℕ) :
    dgCoherentBarCutGradedMap R D G (Nat.le_succ n) ≫
      dgCoherentBarCutGradedRetraction R D G n = 𝟙 _ := by
  dsimp only [dgCoherentBarCutGradedRetraction]
  rw [← Category.assoc, dgCoherentBarCutGradedMap_inclusion,
    dgCoherentBarCutInclusion_projection]

lemma dgCoherentBarCutGraded_section_projection (n : ℕ) :
    dgCoherentBarCutGradedSection R D G n ≫ dgCoherentBarCutToLayerGraded R D G (n + 1) = 𝟙 _ := by
  dsimp only [dgCoherentBarCutGradedSection, dgCoherentBarCutToLayerGraded]
  calc
    _ = (dgCoherentBarLayerInclusion R D G (n + 1) ≫ dgCoherentBarCutProjection R D G (n + 1) ≫
      dgCoherentBarCutInclusion R D G (n + 1)) ≫ dgCoherentBarLayerProjection R D G (n + 1) := by
      simp only [Category.assoc]
    _ = _ := by rw [dgCoherentBarLayerInclusion_cut_recover, dgCoherentBarLayerInclusion_projection]

lemma dgCoherentBarCutGraded_section_retraction (n : ℕ) :
    dgCoherentBarCutGradedSection R D G n ≫ dgCoherentBarCutGradedRetraction R D G n = 0 := by
  dsimp only [dgCoherentBarCutGradedSection, dgCoherentBarCutGradedRetraction]
  have h := congrArg (fun f : dgCoherentBarLayerGraded R D G (n + 1) ⟶
      dgCoherentBarNormalizedGraded R D G => f ≫ dgCoherentBarCutProjection R D G n)
    (dgCoherentBarLayerInclusion_cut_recover R D G (n + 1))
  rw [Category.assoc, Category.assoc] at h
  rw [Category.assoc, h]
  apply Sigma.hom_ext
  intro s
  rw [dgCoherentBarLayerInclusion_ι_assoc, dgCoherentBarCutProjection_ι_of_not]
  · simp only [comp_zero]
  · omega

lemma dgCoherentBarCutGraded_inclusion_projection (n : ℕ) :
    dgCoherentBarCutGradedMap R D G (Nat.le_succ n) ≫
      dgCoherentBarCutToLayerGraded R D G (n + 1) = 0 := by
  dsimp only [dgCoherentBarCutToLayerGraded]
  rw [← Category.assoc, dgCoherentBarCutGradedMap_inclusion]
  apply Sigma.hom_ext
  intro s
  rw [dgCoherentBarCutInclusion_ι_assoc, dgCoherentBarLayerProjection_ι_of_ne]
  · simp only [comp_zero]
  · omega

lemma dgCoherentBarCutGraded_decomposition (n : ℕ) :
    dgCoherentBarCutGradedRetraction R D G n ≫
        dgCoherentBarCutGradedMap R D G (Nat.le_succ n) +
      dgCoherentBarCutToLayerGraded R D G (n + 1) ≫ dgCoherentBarCutGradedSection R D G n = 𝟙 _ := by
  classical
  apply Sigma.hom_ext
  intro s
  dsimp only [dgCoherentBarCutGradedRetraction, dgCoherentBarCutGradedMap,
    dgCoherentBarCutToLayerGraded, dgCoherentBarCutGradedSection]
  simp only [Preadditive.comp_add, Category.assoc, dgCoherentBarCutInclusion_ι_assoc,
    Category.comp_id]
  by_cases hs : s.val.val.1 ≤ n
  · have hn : s.val.val.1 ≠ n + 1 := by omega
    rw [dgCoherentBarCutProjection_ι_assoc R D G n ⟨s.val, hs⟩,
      dgCoherentBarCutInclusion_ι_assoc, dgCoherentBarCutProjection_ι R D G (n + 1) s,
      dgBarLayerProjection_ι_of_ne_assoc R D G (n + 1) s.val hn,
      zero_comp, add_zero]
  · have hn : s.val.val.1 = n + 1 := by omega
    rw [dgCoherentBarCutProjection_ι_of_not_assoc R D G n s.val hs,
      zero_comp, dgCoherentBarLayerProjection_ι_assoc R D G (n + 1) ⟨s.val, hn⟩,
      dgCoherentBarLayerInclusion_ι_assoc, dgCoherentBarCutProjection_ι R D G (n + 1) s,
      zero_add]

end SerrePositivity.InfinityCategories
