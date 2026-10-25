module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.GradedStabilization
/-!
概要：段階的正規化の累積次数マイナス一作用素を各単体上で安定化する。
方針：各段階の退化作用素を先行段階へ合成して足し、標的支持で増分を消す。
規約：無限和は使わず、単体ごとの有限な安定値を全 Hom 同値で貼り合わせる。
使われ方：安定した実正規化自己写像と恒等写像との鎖ホモトピー。
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

def dgCoherentBarNormalizationAccumulatedHomotopyGraded : ℕ →
    (moduleHom R D
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))).X (-1)
  | 0 => 0
  | q + 1 => dgCoherentBarNormalizationAccumulatedHomotopyGraded q +
      compose R (n := (-1))
        (x := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
        (y := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
        (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
        (dgCoherentBarNormalizationHomotopyGraded R D F q)
        (dgCoherentBarNormalizationStageGraded R D F q)
        (show (0 : ℤ) + -1 = -1 from rfl)

lemma dgCoherentBarNormalizationAccumulatedHomotopyGraded_restrict_succ (q : ℕ)
    (s : dgCoherentBarIndex I) (hs : s.1 < q) :
    (eHomWhiskerRight (Complex R) (Sigma.ι (dgCoherentBarFamily R D F) s)
      (dgCoherentBarGraded R D F)).f (-1)
        (dgCoherentBarNormalizationAccumulatedHomotopyGraded R D F (q + 1)) =
    (eHomWhiskerRight (Complex R) (Sigma.ι (dgCoherentBarFamily R D F) s)
      (dgCoherentBarGraded R D F)).f (-1)
        (dgCoherentBarNormalizationAccumulatedHomotopyGraded R D F q) := by
  have hz := dgCoherentBarHomFiltration_postcompose_zero R D F
    (M := dgCoherentBarFamily R D F s) (n := s.1)
    ((eHomWhiskerRight (Complex R) (Sigma.ι (dgCoherentBarFamily R D F) s)
      (dgCoherentBarGraded R D F)).f 0 (dgCoherentBarNormalizationStageGraded R D F q))
    (dgCoherentBarNormalizationHomotopyGraded R D F q)
    (dgCoherentBarNormalizationStageGraded_mem_filtration R D F q s)
    (fun t ht => by
      rw [dgCoherentBarNormalizationHomotopyGraded_restrict,
        dgCoherentBarNormalizationHomotopyColumn_eq_zero_of_lt R D F q t (by omega)])
    (show (0 : ℤ) + -1 = -1 from rfl)
  change (eHomWhiskerRight (Complex R) (Sigma.ι (dgCoherentBarFamily R D F) s)
    (dgCoherentBarGraded R D F)).f (-1)
      (dgCoherentBarNormalizationAccumulatedHomotopyGraded R D F q +
        compose R (n := (-1))
          (x := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
          (y := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
          (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
          (dgCoherentBarNormalizationHomotopyGraded R D F q)
          (dgCoherentBarNormalizationStageGraded R D F q) rfl) = _
  rw [map_add, moduleHomRestriction_compose R D, hz, add_zero]

lemma dgCoherentBarNormalizationAccumulatedHomotopyGraded_restrict_stable {q Q : ℕ}
    (s : dgCoherentBarIndex I) (hs : s.1 < q) (hQ : q ≤ Q) :
    (eHomWhiskerRight (Complex R) (Sigma.ι (dgCoherentBarFamily R D F) s)
      (dgCoherentBarGraded R D F)).f (-1)
        (dgCoherentBarNormalizationAccumulatedHomotopyGraded R D F Q) =
    (eHomWhiskerRight (Complex R) (Sigma.ι (dgCoherentBarFamily R D F) s)
      (dgCoherentBarGraded R D F)).f (-1)
        (dgCoherentBarNormalizationAccumulatedHomotopyGraded R D F q) := by
  induction Q, hQ using Nat.le_induction with
  | base => rfl
  | succ Q hQ ih =>
    rw [dgCoherentBarNormalizationAccumulatedHomotopyGraded_restrict_succ R D F Q s
      (by omega), ih]

def dgCoherentBarNormalizationStableHomotopyGraded :
    (moduleHom R D
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))).X (-1) :=
  (dgCoherentBarHomEquiv R D F (dgCoherentBarGraded R D F) (-1)).symm
    (fun s => (eHomWhiskerRight (Complex R) (Sigma.ι (dgCoherentBarFamily R D F) s)
      (dgCoherentBarGraded R D F)).f (-1)
        (dgCoherentBarNormalizationAccumulatedHomotopyGraded R D F (s.1 + 1)))

lemma dgCoherentBarNormalizationStableHomotopyGraded_restrict (s : dgCoherentBarIndex I) :
    (eHomWhiskerRight (Complex R) (Sigma.ι (dgCoherentBarFamily R D F) s)
      (dgCoherentBarGraded R D F)).f (-1)
        (dgCoherentBarNormalizationStableHomotopyGraded R D F) =
    (eHomWhiskerRight (Complex R) (Sigma.ι (dgCoherentBarFamily R D F) s)
      (dgCoherentBarGraded R D F)).f (-1)
        (dgCoherentBarNormalizationAccumulatedHomotopyGraded R D F (s.1 + 1)) := by
  rw [← dgCoherentBarHomEquiv_apply, dgCoherentBarNormalizationStableHomotopyGraded,
    LinearEquiv.apply_symm_apply]

end SerrePositivity.InfinityCategories
