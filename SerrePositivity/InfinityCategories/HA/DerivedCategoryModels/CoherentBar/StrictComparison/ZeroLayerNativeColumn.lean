module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentZeroLayerInclusion
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.NativeColumns

/-!
概要：零次元層の実包含の係数は、B の同じ native 零次元列。
方針：評価成分を保つ MC 移送と元の直和包含・正規化射影を照合する。
規約：零 shift の単位を保持して比較する。
使われ方：指定 native 増大の零次元係数を回収する。
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

def dgBarZeroLayerIndex (s : I _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerIndex I 0 :=
  ⟨⟨⟨0, s⟩, by rw [SSet.nondegenerate_zero]; trivial⟩, rfl⟩

lemma dgBarZeroLayerInclusion_column_f (s : I _⦋0⦌) (x : D) (q : ℤ) :
    ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation R D x).map
      (Sigma.ι (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerFamily R D G 0) (dgBarZeroLayerIndex s) ≫
        _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarZeroLayerInclusion R D G)).f q =
      ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation R D x).map
        (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D G) ⟨0, s⟩ ≫
          _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedProjection R D G)).f q := by
  simp only [Functor.map_comp, HomologicalComplex.comp_f, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarZeroLayerInclusion_eval_f]
  rw [← HomologicalComplex.comp_f, ← Functor.map_comp,
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerInclusion_ι]
  erw [← HomologicalComplex.comp_f, ← Functor.map_comp,
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedProjection_ι R D G (dgBarZeroLayerIndex s).val]

lemma dgBarZeroLayerInclusion_nativeColumn (s : I _⦋0⦌) :
    (eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R)
      (ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D G ⟨0, s⟩))
      (Sigma.ι (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerFamily R D G 0) (dgBarZeroLayerIndex s) ≫
        _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarZeroLayerInclusion R D G)).f 0
      (moduleShiftInElement R D 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D G ⟨0, s⟩)) =
        _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeColumn R D G (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarMaurerCartan_unconditional R D G) ⟨0, s⟩ := by
  apply _root_.SerrePositivity.DifferentialGraded.moduleHomElement_ext R D
  intro x
  apply Cochain.ext
  intro q r hqr
  subst r
  dsimp only [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeColumn, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedShiftedInclusion,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarShiftedInclusion]
  simp only [Nat.cast_zero, Int.neg_zero, Int.negOnePow_zero, one_smul]
  erw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedTargetRebase_π]
  erw [_root_.SerrePositivity.DifferentialGraded.moduleHomWhiskerLeft_apply_π, _root_.SerrePositivity.DifferentialGraded.moduleHomWhiskerLeft_apply_π,
    _root_.SerrePositivity.DifferentialGraded.moduleHomWhiskerLeft_apply_π]
  simp only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v,
    dgBarZeroLayerInclusion_column_f, Functor.map_comp, HomologicalComplex.comp_f,
    Category.assoc]
  have he := dgBarZeroLayerInclusion_column_f R D G s x (q + 0)
  simp only [Functor.map_comp, HomologicalComplex.comp_f] at he
  erw [he]
  rfl

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
