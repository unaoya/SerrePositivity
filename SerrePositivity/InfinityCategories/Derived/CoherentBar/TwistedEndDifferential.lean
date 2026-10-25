module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StageComparison
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.EndRebaseInjective
/-!
概要：元の全 Hom 上で theta による twisted 自己 Hom 微分を扱う。
方針：実 MC Hom の微分公式と単射な graded 移送を用いる。
規約：内部微分と theta の両合成項を保持する。
使われ方：安定化した作用素の閉性と、同じ theta に対する鎖ホモトピー。
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

def dgCoherentBarTwistedEndDifferential (q : ℤ)
    (z : (moduleHom R D
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))).X q) :
    (moduleHom R D
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))).X (q + 1) :=
  (moduleHom R D
    (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
    (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))).d q (q + 1) z +
  compose R (x := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
    (y := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
    (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
    (dgCoherentBarTheta R D F) z rfl +
  (q + 1).negOnePow • compose R
    (x := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
    (y := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
    (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
    z (dgCoherentBarTheta R D F) (by omega)

lemma dgCoherentBarNormalizationStageGraded_twisted_closed
    (hMC : dgCoherentBarMaurerCartan R D F) (q : ℕ) :
    dgCoherentBarTwistedEndDifferential R D F 0
      (dgCoherentBarNormalizationStageGraded R D F q) = 0 := by
  apply dgCoherentBarEndRebase_injective R D F hMC 1
  rw [dgCoherentBarEndRebase_zero]
  change dgCoherentBarEndRebase R D F hMC (0 + 1) _ = 0
  unfold dgCoherentBarTwistedEndDifferential
  rw [← dgCoherentBarEndRebase_d, ← dgCoherentBarNormalizationStage_cycle]
  exact (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R)
    (dgCoherentBarNormalizationStage R D F hMC q))).property


lemma dgCoherentBarTwistedEndDifferential_restrict_congr (q : ℤ)
    (f g : (moduleHom R D
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))).X q)
    (s : dgCoherentBarIndex I)
    (hfg : ∀ t : dgCoherentBarIndex I, t.1 ≤ s.1 →
      (eHomWhiskerRight (Complex R) (Sigma.ι (dgCoherentBarFamily R D F) t)
        (dgCoherentBarGraded R D F)).f q f =
      (eHomWhiskerRight (Complex R) (Sigma.ι (dgCoherentBarFamily R D F) t)
        (dgCoherentBarGraded R D F)).f q g) :
    (eHomWhiskerRight (Complex R) (Sigma.ι (dgCoherentBarFamily R D F) s)
      (dgCoherentBarGraded R D F)).f (q + 1)
      (dgCoherentBarTwistedEndDifferential R D F q f) =
    (eHomWhiskerRight (Complex R) (Sigma.ι (dgCoherentBarFamily R D F) s)
      (dgCoherentBarGraded R D F)).f (q + 1)
      (dgCoherentBarTwistedEndDifferential R D F q g) := by
  have hd (z : (moduleHom R D
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))).X q) :=
    ConcreteCategory.congr_hom
      ((eHomWhiskerRight (Complex R) (Sigma.ι (dgCoherentBarFamily R D F) s)
        (dgCoherentBarGraded R D F)).comm q (q + 1)) z
  change ∀ z : (moduleHom R D
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))).X q,
    (moduleHom R D
      (ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F s))
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))).d q (q + 1)
      ((eHomWhiskerRight (Complex R) (Sigma.ι (dgCoherentBarFamily R D F) s)
        (dgCoherentBarGraded R D F)).f q z) =
    (eHomWhiskerRight (Complex R) (Sigma.ι (dgCoherentBarFamily R D F) s)
      (dgCoherentBarGraded R D F)).f (q + 1)
        ((moduleHom R D
          (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
          (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))).d q (q + 1) z) at hd
  have hc := dgCoherentBarHomFiltration_postcompose_congr R D F
    (M := dgCoherentBarFamily R D F s) (n := s.1 - 1)
    (dgCoherentBarColumn R D F s) f g (dgCoherentBarColumn_mem_filtration R D F s)
    (fun t ht => hfg t (by omega)) (show (1 : ℤ) + q = q + 1 by omega)
  simp only [dgCoherentBarTwistedEndDifferential, map_add, Units.smul_def, map_zsmul]
  rw [← hd f, ← hd g, hfg s le_rfl,
    moduleHomRestriction_compose R D, moduleHomRestriction_compose R D,
    moduleHomRestriction_compose R D, moduleHomRestriction_compose R D,
    hfg s le_rfl, dgCoherentBarTheta_restrict, hc]

end SerrePositivity.InfinityCategories
