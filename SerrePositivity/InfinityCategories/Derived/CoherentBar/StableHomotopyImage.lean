module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StableHomotopyEquation
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.NormalizedHomotopyImage
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

lemma dgCoherentBarHom_exchange {S M N P : ModuleCategory R D}
    (i : S ⟶ M) (p : N ⟶ P) (q : ℤ)
    (z : (moduleHom R D (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) N)).X q) :
    (eHomWhiskerRight (Complex R) i P).f q
      ((eHomWhiskerLeft (Complex R) M p).f q z) =
    (eHomWhiskerLeft (Complex R) S p).f q
      ((eHomWhiskerRight (Complex R) i N).f q z) := by
  exact congrArg (fun f => f.f q z) (eHom_whisker_exchange (Complex R) i p)

variable {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

lemma dgCoherentBarNormalizationAccumulatedHomotopyGraded_normalizedProjection (q : ℕ) :
    (eHomWhiskerLeft (Complex R) (dgCoherentBarGraded R D F)
      (dgCoherentBarNormalizedProjection R D F)).f (-1)
      (dgCoherentBarNormalizationAccumulatedHomotopyGraded R D F q) = 0 := by
  induction q with
  | zero => rw [dgCoherentBarNormalizationAccumulatedHomotopyGraded, map_zero]
  | succ q ih =>
    change (eHomWhiskerLeft (Complex R) (dgCoherentBarGraded R D F)
      (dgCoherentBarNormalizedProjection R D F)).f (-1)
      (dgCoherentBarNormalizationAccumulatedHomotopyGraded R D F q +
        compose R (n := (-1))
          (x := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
          (y := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
          (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
          (dgCoherentBarNormalizationHomotopyGraded R D F q)
          (dgCoherentBarNormalizationStageGraded R D F q) rfl) = 0
    rw [map_add, ih, dgCoherentBarHom_postcompose_comp R D,
      dgCoherentBarNormalizationHomotopyGraded_normalizedProjection,
      DGNerve.zero_compose, add_zero]

lemma dgCoherentBarNormalizationStableHomotopyGraded_normalizedProjection :
    (eHomWhiskerLeft (Complex R) (dgCoherentBarGraded R D F)
      (dgCoherentBarNormalizedProjection R D F)).f (-1)
      (dgCoherentBarNormalizationStableHomotopyGraded R D F) = 0 := by
  apply (dgCoherentBarHomEquiv R D F (dgCoherentBarNormalizedGraded R D F) (-1)).injective
  funext s
  rw [dgCoherentBarHomEquiv_apply, map_zero]
  rw [dgCoherentBarHom_exchange R D,
    dgCoherentBarNormalizationStableHomotopyGraded_restrict,
    ← dgCoherentBarHom_exchange R D,
    dgCoherentBarNormalizationAccumulatedHomotopyGraded_normalizedProjection,
    map_zero]
  rfl

end SerrePositivity.InfinityCategories
