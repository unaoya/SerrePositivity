module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.NativeColumns
/-!
概要：元の graded bar から正規化実 bar への次数零射の微分を計算する。
方針：元の正規化射影の閉零要素を標的 MC Hom に移し、後合成と theta の可換式を使う。
規約：この射は graded bar を始域とし、閉性の代わりに指定した twisting 式を持つ。
使われ方：Bianchi データの全末端部分集合の HA 方程式を実余錐へ移す。
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

lemma dgCoherentBarHom_precompose_cycle {M N P : ModuleCategory R D}
    (p : M ⟶ N) (q : ℤ)
    (g : (moduleHom R D (ForgetEnrichment.to (Complex R) N)
      (ForgetEnrichment.to (Complex R) P)).X q) :
    (eHomWhiskerRight (Complex R) p P).f q g =
    compose R (x := ForgetEnrichment.to (Complex R) M)
      (y := ForgetEnrichment.to (Complex R) N) (z := ForgetEnrichment.to (Complex R) P)
      g (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) p)).val (zero_add q) := by
  apply moduleHomElement_ext R D
    (M := ForgetEnrichment.to (Complex R) M) (N := ForgetEnrichment.to (Complex R) P)
  intro x
  rw [moduleHomWhiskerRight_apply_π, moduleHomCompose_π,
    ← moduleEvaluation_cochain R D x p]

variable {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))
  (hMC : dgCoherentBarMaurerCartan R D F)

def dgCoherentBarNormalizedTargetProjection :
    (moduleHom R D
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (dgCoherentBarNormalizedModule R D F hMC)).X 0 :=
  dgCoherentBarNormalizedTargetRebase R D F hMC
    (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F)) 0
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R)
      (dgCoherentBarNormalizedProjection R D F))).val

lemma dgCoherentBarNormalizedTargetProjection_compose (M : RightModule R D) (q : ℤ)
    (z : (moduleHom R D M
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))).X q) :
    compose R (x := M)
      (y := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (z := dgCoherentBarNormalizedModule R D F hMC)
      (dgCoherentBarNormalizedTargetProjection R D F hMC) z (add_zero q) =
    dgCoherentBarNormalizedTargetRebase R D F hMC M q
      ((eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) M)
        (dgCoherentBarNormalizedProjection R D F)).f q z) := by
  apply moduleHomElement_ext R D
    (M := M) (N := dgCoherentBarNormalizedModule R D F hMC)
  intro x
  have he := moduleHomWhiskerLeft_apply_π R D
    (T := ForgetEnrichment.of (Complex R) M) (M := dgCoherentBarGraded R D F)
    (N := dgCoherentBarNormalizedGraded R D F)
    (dgCoherentBarNormalizedProjection R D F) q z x
  change (moduleHomπ R D M
    (ForgetEnrichment.to (Complex R) (dgCoherentBarNormalizedGraded R D F)) x).f q
      ((eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) M)
        (dgCoherentBarNormalizedProjection R D F)).f q z) =
      ((moduleHomπ R D M
        (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F)) x).f q z).comp
        (Cochain.ofHom ((moduleEvaluation R D x).map
          (dgCoherentBarNormalizedProjection R D F))) (add_zero q) at he
  rw [moduleHomCompose_π]
  apply Cochain.ext
  intro i j hij
  rw [dgCoherentBarNormalizedTargetRebase_π, he,
    Cochain.comp_v _ _ _ i (i + q) j rfl (by omega)]
  rw [dgCoherentBarNormalizedTargetProjection,
    dgCoherentBarNormalizedTargetRebase_π,
    ← moduleEvaluation_cochain R D x (dgCoherentBarNormalizedProjection R D F),
    Cochain.comp_v _ _ _ i (i + q) j rfl (by omega)]

lemma dgCoherentBarNormalizedTargetProjection_d :
    (moduleHom R D
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (dgCoherentBarNormalizedModule R D F hMC)).d 0 1
      (dgCoherentBarNormalizedTargetProjection R D F hMC) =
    compose R
      (x := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (y := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (z := dgCoherentBarNormalizedModule R D F hMC)
      (dgCoherentBarNormalizedTargetProjection R D F hMC) (dgCoherentBarTheta R D F)
      (add_zero 1) := by
  have hp := (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R)
    (dgCoherentBarNormalizedProjection R D F))).property
  change (moduleHom R D
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (ForgetEnrichment.to (Complex R) (dgCoherentBarNormalizedGraded R D F))).d 0 1
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R)
        (dgCoherentBarNormalizedProjection R D F))).val = 0 at hp
  rw [dgCoherentBarNormalizedTargetProjection_compose]
  change (moduleHom R D
    (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
    (dgCoherentBarNormalizedModule R D F hMC)).d 0 (0 + 1)
      (dgCoherentBarNormalizedTargetRebase R D F hMC _ 0 _) = _
  rw [dgCoherentBarNormalizedTargetRebase_d]
  change dgCoherentBarNormalizedTargetRebase R D F hMC
    (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F)) 1
    ((moduleHom R D
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (ForgetEnrichment.to (Complex R) (dgCoherentBarNormalizedGraded R D F))).d 0 1
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R)
        (dgCoherentBarNormalizedProjection R D F))).val +
      compose R (n := 1)
        (x := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
        (y := ForgetEnrichment.to (Complex R) (dgCoherentBarNormalizedGraded R D F))
        (z := ForgetEnrichment.to (Complex R) (dgCoherentBarNormalizedGraded R D F))
        (dgCoherentBarNormalizedTheta R D F)
        (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R)
          (dgCoherentBarNormalizedProjection R D F))).val rfl) = _
  rw [hp, zero_add,
    ← dgCoherentBarHom_precompose_cycle R D
      (dgCoherentBarNormalizedProjection R D F) 1 (dgCoherentBarNormalizedTheta R D F),
    dgCoherentBarNormalizedTheta_projection]
  rfl

end SerrePositivity.InfinityCategories
