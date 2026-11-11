module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.NormalizedGraded
/-!
概要：元の graded bar を非退化因子と退化因子に分裂し、恒等射を二つの射影に分ける。
方針：同じ単体ラベルの所属条件で直和射を定め、包含への制限で等式を検証する。
規約：実 theta による退化部分の保存は別の命題。内部微分での分裂をそのまま実 retract としない。
使われ方：正規化商の微分と、退化部分の縮約からの補正包含。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open CategoryTheory Limits Preadditive DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

abbrev dgCoherentBarDegenerateFamily (s : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarDegenerateIndex I) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F s.val

abbrev dgCoherentBarDegenerateGraded : ModuleCategory R D :=
  ∐ dgCoherentBarDegenerateFamily R D F

def dgCoherentBarDegenerateInclusion :
    dgCoherentBarDegenerateGraded R D F ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F :=
  Sigma.desc (fun s => Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) s.val)

def dgCoherentBarDegenerateProjection :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F ⟶ dgCoherentBarDegenerateGraded R D F := by
  classical
  exact Sigma.desc (fun s => if h : s.2 ∈ I.degenerate s.1 then
    Sigma.ι (dgCoherentBarDegenerateFamily R D F) ⟨s, h⟩ else 0)

@[reassoc (attr := simp)]
lemma dgCoherentBarDegenerateInclusion_ι (s : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarDegenerateIndex I) :
    Sigma.ι (dgCoherentBarDegenerateFamily R D F) s ≫
      dgCoherentBarDegenerateInclusion R D F =
    Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) s.val := by
  simp [dgCoherentBarDegenerateInclusion]

@[reassoc (attr := simp)]
lemma dgCoherentBarDegenerateProjection_ι (s : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarDegenerateIndex I) :
    Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) s.val ≫
      dgCoherentBarDegenerateProjection R D F =
    Sigma.ι (dgCoherentBarDegenerateFamily R D F) s := by
  classical
  simp [dgCoherentBarDegenerateProjection, s.property]

lemma dgCoherentBarDegenerateInclusion_projection :
    dgCoherentBarDegenerateInclusion R D F ≫
      dgCoherentBarDegenerateProjection R D F = 𝟙 _ := by
  apply Sigma.hom_ext
  intro s
  rw [← Category.assoc, dgCoherentBarDegenerateInclusion_ι,
    dgCoherentBarDegenerateProjection_ι, Category.comp_id]

lemma dgCoherentBarGraded_identity_decomposition :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedProjection R D F ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedInclusion R D F +
      dgCoherentBarDegenerateProjection R D F ≫ dgCoherentBarDegenerateInclusion R D F =
    𝟙 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F) := by
  classical
  apply Sigma.hom_ext
  intro s
  by_cases hs : s.2 ∈ I.degenerate s.1
  · rw [comp_add, ← Category.assoc, ← Category.assoc]
    have hn := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedProjection_ι_degenerate R D F ⟨s, hs⟩
    rw [hn, zero_comp, zero_add]
    rw [show Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) s ≫
      dgCoherentBarDegenerateProjection R D F =
      Sigma.ι (dgCoherentBarDegenerateFamily R D F) ⟨s, hs⟩ from
        dgCoherentBarDegenerateProjection_ι R D F ⟨s, hs⟩]
    rw [dgCoherentBarDegenerateInclusion_ι, Category.comp_id]
  · rw [comp_add, ← Category.assoc, ← Category.assoc]
    have hn : s.2 ∈ I.nonDegenerate s.1 := hs
    rw [show Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) s ≫
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedProjection R D F =
      Sigma.ι (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedFamily R D F) ⟨s, hn⟩ from
        _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedProjection_ι R D F ⟨s, hn⟩]
    have hg : Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) s ≫
        dgCoherentBarDegenerateProjection R D F = 0 := by
      simp only [dgCoherentBarDegenerateProjection, Sigma.ι_comp_desc, dite_eq_right hs]
    rw [hg, zero_comp, add_zero, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedInclusion_ι, Category.comp_id]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
