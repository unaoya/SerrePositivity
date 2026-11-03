module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.NormalizedTargetHom
public import SerrePositivity.InfinityCategories.Derived.DGCoherentBarColumnAction
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open HomologicalComplex CochainComplex HomComplex
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

def dgCoherentBarNormalizedShiftedInclusion (s : dgCoherentBarIndex I) :
    (moduleHom R D (dgCoherentBarSource R D F s)
      (ForgetEnrichment.to (Complex R) (dgCoherentBarNormalizedGraded R D F))).X
        (-(s.1 : ℤ)) :=
  (eHomWhiskerLeft (Complex R)
    (ForgetEnrichment.of (Complex R) (dgCoherentBarSource R D F s))
    (dgCoherentBarNormalizedProjection R D F)).f (-(s.1 : ℤ))
      (dgCoherentBarShiftedInclusion R D F s)

lemma dgCoherentBarHom_postcompose_zero {M N P : ModuleCategory R D} (q : ℤ)
    (z : (moduleHom R D (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) N)).X q) :
    (eHomWhiskerLeft (Complex R) M (0 : N ⟶ P)).f q z = 0 := by
  apply moduleHomElement_ext R D
    (M := ForgetEnrichment.to (Complex R) M) (N := ForgetEnrichment.to (Complex R) P)
  intro x
  rw [moduleHomWhiskerLeft_apply_π, (moduleEvaluation R D x).map_zero N P,
    Cochain.ofHom_zero, Cochain.comp_zero, map_zero]

lemma dgCoherentBarNormalizedShiftedInclusion_degenerate (s : dgCoherentBarDegenerateIndex I) :
    dgCoherentBarNormalizedShiftedInclusion R D F s.val = 0 := by
  unfold dgCoherentBarNormalizedShiftedInclusion dgCoherentBarShiftedInclusion
  simp only [Units.smul_def, map_zsmul]
  have h := congrArg (fun f => f.f (-(s.val.1 : ℤ))
    (moduleShiftInElement R D (s.val.1 : ℤ) (dgCoherentBarSource R D F s.val)))
    (eHomWhiskerLeft_comp (Complex R)
      (ForgetEnrichment.of (Complex R) (dgCoherentBarSource R D F s.val))
      (Sigma.ι (dgCoherentBarFamily R D F) s.val)
      (dgCoherentBarNormalizedProjection R D F))
  change (eHomWhiskerLeft (Complex R)
      (ForgetEnrichment.of (Complex R) (dgCoherentBarSource R D F s.val))
      (Sigma.ι (dgCoherentBarFamily R D F) s.val ≫
        dgCoherentBarNormalizedProjection R D F)).f (-(s.val.1 : ℤ))
        (moduleShiftInElement R D (s.val.1 : ℤ) (dgCoherentBarSource R D F s.val)) =
    (eHomWhiskerLeft (Complex R)
      (ForgetEnrichment.of (Complex R) (dgCoherentBarSource R D F s.val))
      (dgCoherentBarNormalizedProjection R D F)).f (-(s.val.1 : ℤ))
      ((eHomWhiskerLeft (Complex R)
        (ForgetEnrichment.of (Complex R) (dgCoherentBarSource R D F s.val))
        (Sigma.ι (dgCoherentBarFamily R D F) s.val)).f (-(s.val.1 : ℤ))
          (moduleShiftInElement R D (s.val.1 : ℤ) (dgCoherentBarSource R D F s.val))) at h
  rw [dgCoherentBarNormalizedProjection_ι_degenerate] at h
  rw [← h, dgCoherentBarHom_postcompose_zero R D, smul_zero]

lemma dgCoherentBarNormalizedShiftedInclusion_d (s : dgCoherentBarIndex I) :
    (moduleHom R D (dgCoherentBarSource R D F s)
      (ForgetEnrichment.to (Complex R) (dgCoherentBarNormalizedGraded R D F))).d
      (-(s.1 : ℤ)) (-(s.1 : ℤ) + 1)
      (dgCoherentBarNormalizedShiftedInclusion R D F s) = 0 := by
  have h := ConcreteCategory.congr_hom
    ((eHomWhiskerLeft (Complex R)
      (ForgetEnrichment.of (Complex R) (dgCoherentBarSource R D F s))
      (dgCoherentBarNormalizedProjection R D F)).comm (-(s.1 : ℤ)) (-(s.1 : ℤ) + 1))
    (dgCoherentBarShiftedInclusion R D F s)
  change _ = (eHomWhiskerLeft (Complex R)
    (ForgetEnrichment.of (Complex R) (dgCoherentBarSource R D F s))
    (dgCoherentBarNormalizedProjection R D F)).f (-(s.1 : ℤ) + 1)
      ((moduleHom R D (dgCoherentBarSource R D F s)
        (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))).d
        (-(s.1 : ℤ)) (-(s.1 : ℤ) + 1) (dgCoherentBarShiftedInclusion R D F s)) at h
  rw [dgCoherentBarShiftedInclusion_d, map_zero] at h
  exact h

def dgCoherentBarNativeColumn (hMC : dgCoherentBarMaurerCartan R D F)
    (s : dgCoherentBarIndex I) :
    (moduleHom R D (dgCoherentBarSource R D F s)
      (dgCoherentBarNormalizedModule R D F hMC)).X (-(s.1 : ℤ)) :=
  dgCoherentBarNormalizedTargetRebase R D F hMC (dgCoherentBarSource R D F s)
    (-(s.1 : ℤ)) (dgCoherentBarNormalizedShiftedInclusion R D F s)

lemma dgCoherentBarNativeColumn_degenerate (hMC : dgCoherentBarMaurerCartan R D F)
    (s : dgCoherentBarDegenerateIndex I) :
    dgCoherentBarNativeColumn R D F hMC s.val = 0 := by
  rw [dgCoherentBarNativeColumn, dgCoherentBarNormalizedShiftedInclusion_degenerate,
    dgCoherentBarNormalizedTargetRebase_zero]


lemma dgCoherentBarNativeColumn_d (hMC : dgCoherentBarMaurerCartan R D F)
    (s : dgCoherentBarIndex I) :
    (moduleHom R D (dgCoherentBarSource R D F s)
      (dgCoherentBarNormalizedModule R D F hMC)).d (-(s.1 : ℤ)) (-(s.1 : ℤ) + 1)
      (dgCoherentBarNativeColumn R D F hMC s) =
    dgCoherentBarNormalizedTargetRebase R D F hMC (dgCoherentBarSource R D F s)
      (-(s.1 : ℤ) + 1)
      ((eHomWhiskerLeft (Complex R)
        (ForgetEnrichment.of (Complex R) (dgCoherentBarSource R D F s))
        (dgCoherentBarNormalizedProjection R D F)).f (-(s.1 : ℤ) + 1)
        (compose R (x := dgCoherentBarSource R D F s)
          (y := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
          (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
          (dgCoherentBarTheta R D F) (dgCoherentBarShiftedInclusion R D F s) rfl)) := by
  rw [dgCoherentBarNativeColumn, dgCoherentBarNormalizedTargetRebase_d,
    dgCoherentBarNormalizedShiftedInclusion_d, zero_add,
    dgCoherentBarNormalizedShiftedInclusion,
    moduleHomClosedInsertion R D
      (S := ForgetEnrichment.of (Complex R) (dgCoherentBarSource R D F s))
      (M := dgCoherentBarGraded R D F) (N := dgCoherentBarNormalizedGraded R D F)
      (P := dgCoherentBarNormalizedGraded R D F),
    dgCoherentBarNormalizedTheta_projection, ← dgCoherentBarHom_postcompose_comp R D
      (M := ForgetEnrichment.of (Complex R) (dgCoherentBarSource R D F s))
      (N := dgCoherentBarGraded R D F) (P := dgCoherentBarGraded R D F)
      (Q := dgCoherentBarNormalizedGraded R D F)]

lemma dgCoherentBarNativeColumn_vertex_closed (hMC : dgCoherentBarMaurerCartan R D F)
    (s : I _⦋0⦌) :
    (moduleHom R D (dgCoherentBarSource R D F ⟨0, s⟩)
      (dgCoherentBarNormalizedModule R D F hMC)).d 0 1
      (dgCoherentBarNativeColumn R D F hMC ⟨0, s⟩) = 0 := by
  have h := dgCoherentBarNativeColumn_d R D F hMC ⟨0, s⟩
  rw [dgCoherentBarTheta_comp_shiftedInclusion R D F, dgCoherentBarColumn,
    DGNerve.zero_compose, smul_zero, map_zero,
    dgCoherentBarNormalizedTargetRebase_zero] at h
  exact h

lemma dgCoherentBarNativeColumn_d_positive (hMC : dgCoherentBarMaurerCartan R D F)
    {n : ℕ} (s : I _⦋n + 1⦌) :
    (moduleHom R D (dgCoherentBarSource R D F ⟨n + 1, s⟩)
      (dgCoherentBarNormalizedModule R D F hMC)).d
      (-((n + 1 : ℕ) : ℤ)) (-((n + 1 : ℕ) : ℤ) + 1)
      (dgCoherentBarNativeColumn R D F hMC ⟨n + 1, s⟩) =
    dgCoherentBarNormalizedTargetRebase R D F hMC (dgCoherentBarSource R D F ⟨n + 1, s⟩)
      (-((n + 1 : ℕ) : ℤ) + 1)
      ((eHomWhiskerLeft (Complex R)
        (ForgetEnrichment.of (Complex R) (dgCoherentBarSource R D F ⟨n + 1, s⟩))
        (dgCoherentBarNormalizedProjection R D F)).f (-((n + 1 : ℕ) : ℤ) + 1)
        (dgCoherentBarUnshiftedBoundary R D F s)) := by
  rw [dgCoherentBarNativeColumn_d, dgCoherentBarTheta_comp_shiftedInclusion_positive R D F]

end SerrePositivity.InfinityCategories
