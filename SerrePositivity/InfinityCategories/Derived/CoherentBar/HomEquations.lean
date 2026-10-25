module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.HomDegrees
/-!
概要：実 bar からの閉斉次射を、元の全単体列上の twisted 微分方程式に同定する。
方針：Hom の次数同値と微分公式を全単体ラベルの直積へ送る。
規約：native 余錐の退化整合性と普遍性はこの代数的同値とは別に証明する。
使われ方：bar 余錐の構成と全 Hom 普遍性に必要な係数方程式の正本。
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
  (hMC : dgCoherentBarMaurerCartan R D F) (N : RightModule R D)

def dgCoherentBarHomColumnDifferential (q : ℤ)
    (a : ∀ s : dgCoherentBarIndex I,
      (moduleHom R D
        (ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F s)) N).X q) :
    ∀ s : dgCoherentBarIndex I,
      (moduleHom R D
        (ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F s)) N).X (q + 1) :=
  let z := (dgCoherentBarHomEquiv R D F (ForgetEnrichment.of (Complex R) N) q).symm a
  dgCoherentBarHomEquiv R D F (ForgetEnrichment.of (Complex R) N) (q + 1)
    ((moduleHom R D
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F)) N).d q (q + 1) z +
      (q + 1).negOnePow • compose R
        (x := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
        (y := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F)) (z := N)
        z (dgCoherentBarTheta R D F) (by omega : 1 + q = q + 1))

lemma dgCoherentBarHomColumnsEquiv_d (q : ℤ)
    (z : (moduleHom R D (dgCoherentBarModule R D F hMC) N).X q) :
    dgCoherentBarHomColumnsEquiv R D F hMC N (q + 1)
      ((moduleHom R D (dgCoherentBarModule R D F hMC) N).d q (q + 1) z) =
    dgCoherentBarHomColumnDifferential R D F N q
      (dgCoherentBarHomColumnsEquiv R D F hMC N q z) := by
  simp only [dgCoherentBarHomColumnsEquiv, LinearEquiv.trans_apply,
    dgCoherentBarHomColumnDifferential, dgCoherentBarHomDegreeEquiv_d]
  erw [(dgCoherentBarHomEquiv R D F (ForgetEnrichment.of (Complex R) N) q).symm_apply_apply
    (dgCoherentBarHomDegreeEquiv R D F hMC N q z)]
  rfl

lemma dgCoherentBarHomColumnsEquiv_closed_iff (q : ℤ)
    (z : (moduleHom R D (dgCoherentBarModule R D F hMC) N).X q) :
    (moduleHom R D (dgCoherentBarModule R D F hMC) N).d q (q + 1) z = 0 ↔
      dgCoherentBarHomColumnDifferential R D F N q
        (dgCoherentBarHomColumnsEquiv R D F hMC N q z) = 0 := by
  rw [← dgCoherentBarHomColumnsEquiv_d]
  exact (dgCoherentBarHomColumnsEquiv R D F hMC N (q + 1)).map_eq_zero_iff.symm

def dgCoherentBarClosedColumnsEquiv (q : ℤ) :
    {z : (moduleHom R D (dgCoherentBarModule R D F hMC) N).X q //
      (moduleHom R D (dgCoherentBarModule R D F hMC) N).d q (q + 1) z = 0} ≃
    {a : ∀ s : dgCoherentBarIndex I,
      (moduleHom R D
        (ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F s)) N).X q //
      dgCoherentBarHomColumnDifferential R D F N q a = 0} :=
  (dgCoherentBarHomColumnsEquiv R D F hMC N q).toEquiv.subtypeEquiv
    (dgCoherentBarHomColumnsEquiv_closed_iff R D F hMC N q)

end SerrePositivity.InfinityCategories
