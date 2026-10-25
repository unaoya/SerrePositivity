module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.GradedStages
/-!
概要：有限段階の正規化作用素は各単体上で安定する。
方針：段階の標的支持と、低い次数で境界が零になることを合成する。
規約：単体ごとの有限な安定値を全次数 Hom の直和普遍性で束ねる。
使われ方：元の theta に対する完成した正規化作用素の構成。
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
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

lemma dgCoherentBarNormalizationStageGraded_restrict_succ (q : ℕ)
    (s : dgCoherentBarIndex I) (hs : s.1 < q) :
    (eHomWhiskerRight (Complex R) (Sigma.ι (dgCoherentBarFamily R D F) s)
      (dgCoherentBarGraded R D F)).f 0 (dgCoherentBarNormalizationStageGraded R D F (q + 1)) =
    (eHomWhiskerRight (Complex R) (Sigma.ι (dgCoherentBarFamily R D F) s)
      (dgCoherentBarGraded R D F)).f 0 (dgCoherentBarNormalizationStageGraded R D F q) := by
  have hz := dgCoherentBarHomFiltration_postcompose_zero R D F
    (M := dgCoherentBarFamily R D F s) (n := s.1)
    ((eHomWhiskerRight (Complex R) (Sigma.ι (dgCoherentBarFamily R D F) s)
      (dgCoherentBarGraded R D F)).f 0 (dgCoherentBarNormalizationStageGraded R D F q))
    (dgCoherentBarNormalizationBoundaryGraded R D F q)
    (dgCoherentBarNormalizationStageGraded_mem_filtration R D F q s)
    (fun t ht => dgCoherentBarNormalizationBoundaryGraded_restrict_eq_zero R D F q t
      (lt_of_le_of_lt ht hs)) (show (0 : ℤ) + 0 = 0 from rfl)
  change (eHomWhiskerRight (Complex R) (Sigma.ι (dgCoherentBarFamily R D F) s)
    (dgCoherentBarGraded R D F)).f 0
      (compose R
        (x := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
        (y := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
        (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
        ((unitElement R
          (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))).val +
          dgCoherentBarNormalizationBoundaryGraded R D F q)
        (dgCoherentBarNormalizationStageGraded R D F q) rfl) = _
  rw [moduleHomRestriction_compose R D
    (Sigma.ι (dgCoherentBarFamily R D F) s)
    (dgCoherentBarNormalizationStageGraded R D F q),
    DGNerve.compose_add_left, unit_compose, hz, add_zero]

lemma dgCoherentBarNormalizationStageGraded_restrict_stable {q Q : ℕ}
    (s : dgCoherentBarIndex I) (hs : s.1 < q) (hQ : q ≤ Q) :
    (eHomWhiskerRight (Complex R) (Sigma.ι (dgCoherentBarFamily R D F) s)
      (dgCoherentBarGraded R D F)).f 0 (dgCoherentBarNormalizationStageGraded R D F Q) =
    (eHomWhiskerRight (Complex R) (Sigma.ι (dgCoherentBarFamily R D F) s)
      (dgCoherentBarGraded R D F)).f 0 (dgCoherentBarNormalizationStageGraded R D F q) := by
  induction Q, hQ using Nat.le_induction with
  | base => rfl
  | succ Q hQ ih =>
    rw [dgCoherentBarNormalizationStageGraded_restrict_succ R D F Q s (by omega), ih]

def dgCoherentBarNormalizationProjectorGraded :
    (moduleHom R D
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))).X 0 :=
  (dgCoherentBarHomEquiv R D F (dgCoherentBarGraded R D F) 0).symm
    (fun s => (eHomWhiskerRight (Complex R) (Sigma.ι (dgCoherentBarFamily R D F) s)
      (dgCoherentBarGraded R D F)).f 0
        (dgCoherentBarNormalizationStageGraded R D F (s.1 + 1)))

lemma dgCoherentBarNormalizationProjectorGraded_restrict (s : dgCoherentBarIndex I) :
    (eHomWhiskerRight (Complex R) (Sigma.ι (dgCoherentBarFamily R D F) s)
      (dgCoherentBarGraded R D F)).f 0 (dgCoherentBarNormalizationProjectorGraded R D F) =
    (eHomWhiskerRight (Complex R) (Sigma.ι (dgCoherentBarFamily R D F) s)
      (dgCoherentBarGraded R D F)).f 0
        (dgCoherentBarNormalizationStageGraded R D F (s.1 + 1)) := by
  rw [← dgCoherentBarHomEquiv_apply, dgCoherentBarNormalizationProjectorGraded,
    LinearEquiv.apply_symm_apply]

end SerrePositivity.InfinityCategories
