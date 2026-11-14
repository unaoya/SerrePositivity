module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.NormalizedTargetHom
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.CoherentBar.Columns.DGCoherentBarColumnAction
public import SerrePositivity.DifferentialGraded.Module.Hom.HomotopyAndOperations
/-!
概要：正規化実 bar を頂点とする native 余錐の全単体成分を構成する。
方針：元の符号付き shift 包含を正規化射影へ送り、同じ MC 標的へ成分を保って移す。
規約：退化ラベルでは零になる。余錐への貼り合わせと全 HA 方程式は後続で検証する。
使われ方：工程Bの native 余錐と、その後合成による全 Hom 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open CategoryTheory Limits DifferentialGraded SSet
open HomologicalComplex CochainComplex HomComplex
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

def dgCoherentBarNormalizedShiftedInclusion (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I) :
    (moduleHom R D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F s)
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedGraded R D F))).X
        (-(s.1 : ℤ)) :=
  (eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R)
    (ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F s))
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedProjection R D F)).f (-(s.1 : ℤ))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarShiftedInclusion R D F s)

lemma dgCoherentBarHom_postcompose_zero {M N P : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D} (q : ℤ)
    (z : (_root_.SerrePositivity.DifferentialGraded.moduleHom R D (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) M)
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) N)).X q) :
    (eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R) M (0 : N ⟶ P)).f q z = 0 := by
  apply _root_.SerrePositivity.DifferentialGraded.moduleHomElement_ext R D
    (M := ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) M) (N := ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) P)
  intro x
  rw [_root_.SerrePositivity.DifferentialGraded.moduleHomWhiskerLeft_apply_π, (_root_.SerrePositivity.DifferentialGraded.moduleEvaluation R D x).map_zero N P,
    Cochain.ofHom_zero, Cochain.comp_zero, map_zero]

lemma dgCoherentBarNormalizedShiftedInclusion_degenerate (s : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarDegenerateIndex I) :
    dgCoherentBarNormalizedShiftedInclusion R D F s.val = 0 := by
  unfold dgCoherentBarNormalizedShiftedInclusion _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarShiftedInclusion
  simp only [Units.smul_def, map_zsmul]
  have h := congrArg (fun f => f.f (-(s.val.1 : ℤ))
    (moduleShiftInElement R D (s.val.1 : ℤ) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F s.val)))
    (eHomWhiskerLeft_comp (_root_.SerrePositivity.DifferentialGraded.Complex R)
      (ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F s.val))
      (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) s.val)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedProjection R D F))
  change (eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R)
      (ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F s.val))
      (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) s.val ≫
        _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedProjection R D F)).f (-(s.val.1 : ℤ))
        (moduleShiftInElement R D (s.val.1 : ℤ) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F s.val)) =
    (eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R)
      (ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F s.val))
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedProjection R D F)).f (-(s.val.1 : ℤ))
      ((eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R)
        (ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F s.val))
        (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) s.val)).f (-(s.val.1 : ℤ))
          (moduleShiftInElement R D (s.val.1 : ℤ) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F s.val))) at h
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedProjection_ι_degenerate] at h
  rw [← h, dgCoherentBarHom_postcompose_zero R D, smul_zero]

lemma dgCoherentBarNormalizedShiftedInclusion_d (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I) :
    (moduleHom R D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F s)
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedGraded R D F))).d
      (-(s.1 : ℤ)) (-(s.1 : ℤ) + 1)
      (dgCoherentBarNormalizedShiftedInclusion R D F s) = 0 := by
  have h := ConcreteCategory.congr_hom
    ((eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R)
      (ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F s))
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedProjection R D F)).comm (-(s.1 : ℤ)) (-(s.1 : ℤ) + 1))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarShiftedInclusion R D F s)
  change _ = (eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R)
    (ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F s))
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedProjection R D F)).f (-(s.1 : ℤ) + 1)
      ((moduleHom R D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F s)
        (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))).d
        (-(s.1 : ℤ)) (-(s.1 : ℤ) + 1) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarShiftedInclusion R D F s)) at h
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarShiftedInclusion_d, map_zero] at h
  exact h

def dgCoherentBarNativeColumn (hMC : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarMaurerCartan R D F)
    (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I) :
    (moduleHom R D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F s)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC)).X (-(s.1 : ℤ)) :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedTargetRebase R D F hMC (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F s)
    (-(s.1 : ℤ)) (dgCoherentBarNormalizedShiftedInclusion R D F s)

lemma dgCoherentBarNativeColumn_degenerate (hMC : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarMaurerCartan R D F)
    (s : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarDegenerateIndex I) :
    dgCoherentBarNativeColumn R D F hMC s.val = 0 := by
  rw [dgCoherentBarNativeColumn, dgCoherentBarNormalizedShiftedInclusion_degenerate,
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedTargetRebase_zero]


lemma dgCoherentBarNativeColumn_d (hMC : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarMaurerCartan R D F)
    (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I) :
    (moduleHom R D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F s)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC)).d (-(s.1 : ℤ)) (-(s.1 : ℤ) + 1)
      (dgCoherentBarNativeColumn R D F hMC s) =
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedTargetRebase R D F hMC (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F s)
      (-(s.1 : ℤ) + 1)
      ((eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R)
        (ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F s))
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedProjection R D F)).f (-(s.1 : ℤ) + 1)
        (compose R (x := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F s)
          (y := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
          (z := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTheta R D F) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarShiftedInclusion R D F s) rfl)) := by
  rw [dgCoherentBarNativeColumn, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedTargetRebase_d,
    dgCoherentBarNormalizedShiftedInclusion_d, zero_add,
    dgCoherentBarNormalizedShiftedInclusion,
    _root_.SerrePositivity.DifferentialGraded.moduleHomClosedInsertion R D
      (S := ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F s))
      (M := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F) (N := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedGraded R D F)
      (P := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedGraded R D F),
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedTheta_projection, ← _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarHom_postcompose_comp R D
      (M := ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F s))
      (N := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F) (P := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)
      (Q := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedGraded R D F)]

lemma dgCoherentBarNativeColumn_vertex_closed (hMC : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarMaurerCartan R D F)
    (s : I _⦋0⦌) :
    (moduleHom R D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨0, s⟩)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC)).d 0 1
      (dgCoherentBarNativeColumn R D F hMC ⟨0, s⟩) = 0 := by
  have h := dgCoherentBarNativeColumn_d R D F hMC ⟨0, s⟩
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTheta_comp_shiftedInclusion R D F, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarColumn,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose, smul_zero, map_zero,
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedTargetRebase_zero] at h
  exact h

lemma dgCoherentBarNativeColumn_d_positive (hMC : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarMaurerCartan R D F)
    {n : ℕ} (s : I _⦋n + 1⦌) :
    (moduleHom R D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n + 1, s⟩)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC)).d
      (-((n + 1 : ℕ) : ℤ)) (-((n + 1 : ℕ) : ℤ) + 1)
      (dgCoherentBarNativeColumn R D F hMC ⟨n + 1, s⟩) =
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedTargetRebase R D F hMC (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n + 1, s⟩)
      (-((n + 1 : ℕ) : ℤ) + 1)
      ((eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R)
        (ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n + 1, s⟩))
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedProjection R D F)).f (-((n + 1 : ℕ) : ℤ) + 1)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarUnshiftedBoundary R D F s)) := by
  rw [dgCoherentBarNativeColumn_d, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTheta_comp_shiftedInclusion_positive R D F]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
