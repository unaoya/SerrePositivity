module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StableHomotopyEquation
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.NormalizedHomotopyImage
/-!
概要：安定した累積ホモトピーは非退化因子への射影で零になる。
方針：退化作用素の像の消滅を有限累積へ伝え、各単体の安定値へ移す。
規約：全次数 Hom の閉零前後合成を使い、成分ごとの自然性を保持する。
使われ方：安定作用素と元の正規化射影の整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]

lemma dgCoherentBarHom_exchange {S M N P : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D}
    (i : S ⟶ M) (p : N ⟶ P) (q : ℤ)
    (z : (_root_.SerrePositivity.DifferentialGraded.moduleHom R D (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) M)
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) N)).X q) :
    (eHomWhiskerRight (_root_.SerrePositivity.DifferentialGraded.Complex R) i P).f q
      ((eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R) M p).f q z) =
    (eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R) S p).f q
      ((eHomWhiskerRight (_root_.SerrePositivity.DifferentialGraded.Complex R) i N).f q z) := by
  exact congrArg (fun f => f.f q z) (eHom_whisker_exchange (_root_.SerrePositivity.DifferentialGraded.Complex R) i p)

variable {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

lemma dgCoherentBarNormalizationAccumulatedHomotopyGraded_normalizedProjection (q : ℕ) :
    (eHomWhiskerLeft (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedProjection R D F)).f (-1)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizationAccumulatedHomotopyGraded R D F q) = 0 := by
  induction q with
  | zero => rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizationAccumulatedHomotopyGraded, map_zero]
  | succ q ih =>
    change (eHomWhiskerLeft (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedProjection R D F)).f (-1)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizationAccumulatedHomotopyGraded R D F q +
        _root_.SerrePositivity.DifferentialGraded.compose R (n := (-1))
          (x := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
          (y := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
          (z := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
          (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizationHomotopyGraded R D F q)
          (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizationStageGraded R D F q) rfl) = 0
    rw [map_add, ih, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarHom_postcompose_comp R D,
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizationHomotopyGraded_normalizedProjection,
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose, add_zero]

lemma dgCoherentBarNormalizationStableHomotopyGraded_normalizedProjection :
    (eHomWhiskerLeft (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedProjection R D F)).f (-1)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizationStableHomotopyGraded R D F) = 0 := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarHomEquiv R D F (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedGraded R D F) (-1)).injective
  funext s
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarHomEquiv_apply, map_zero]
  rw [dgCoherentBarHom_exchange R D,
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizationStableHomotopyGraded_restrict,
    ← dgCoherentBarHom_exchange R D,
    dgCoherentBarNormalizationAccumulatedHomotopyGraded_normalizedProjection,
    map_zero]
  rfl

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
