module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.ShiftedHomCoordinates
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.NormalizedHomEquations
/-!
概要：正規化実 bar からの全 Hom を、native 余錐と同じ次数の非退化単体成分へ同定する。
方針：非退化直和の Hom 同値、始域シフトの両逆則、元の包含の符号を合成する。
規約：全ての整数次数を扱う。native 写像空間の普遍性は成分の照合後に結論する。
使われ方：余錐の後合成と全 Hom の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R]

def dgCoherentBarUnitsSMulEquiv (V : Type u) [AddCommGroup V] [Module R V] (c : ℤˣ) :
    V ≃ₗ[R] V where
  toFun z := c • z
  invFun z := c⁻¹ • z
  left_inv z := by simp only [smul_smul, inv_mul_cancel, one_smul]
  right_inv z := by simp only [smul_smul, mul_inv_cancel, one_smul]
  map_add' z w := smul_add _ _ _
  map_smul' a z := smul_comm _ _ _

variable (D : Type v) [DGCategory R D] [Small.{u} D] {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))
  (hMC : dgCoherentBarMaurerCartan R D F) (N : RightModule R D)

def dgCoherentBarNormalizedNativeHomColumnEquiv (q : ℤ) :
    (∀ s : dgCoherentBarNormalizedIndex I,
      (moduleHom R D
        (ForgetEnrichment.to (Complex R) (dgCoherentBarNormalizedFamily R D F s)) N).X q) ≃ₗ[R]
    (∀ s : dgCoherentBarNormalizedIndex I,
      (moduleHom R D (dgCoherentBarSource R D F s.val) N).X (q - (s.val.1 : ℤ))) :=
  LinearEquiv.piCongrRight (fun s =>
    (dgCoherentBarShiftedHomEquiv R D (s.val.1 : ℤ) q
      (dgCoherentBarSource R D F s.val) N).trans
      (dgCoherentBarUnitsSMulEquiv R _ (s.val.1 : ℤ).negOnePow))

def dgCoherentBarNormalizedNativeHomEquiv (q : ℤ) :
    (moduleHom R D (dgCoherentBarNormalizedModule R D F hMC) N).X q ≃ₗ[R]
    (∀ s : dgCoherentBarNormalizedIndex I,
      (moduleHom R D (dgCoherentBarSource R D F s.val) N).X (q - (s.val.1 : ℤ))) :=
  (dgCoherentBarNormalizedHomColumnsEquiv R D F hMC N q).trans
    (dgCoherentBarNormalizedNativeHomColumnEquiv R D F N q)

def dgCoherentBarNormalizedNativeHomDifferential (q : ℤ)
    (a : ∀ s : dgCoherentBarNormalizedIndex I,
      (moduleHom R D (dgCoherentBarSource R D F s.val) N).X (q - (s.val.1 : ℤ))) :
    ∀ s : dgCoherentBarNormalizedIndex I,
      (moduleHom R D (dgCoherentBarSource R D F s.val) N).X (q + 1 - (s.val.1 : ℤ)) :=
  dgCoherentBarNormalizedNativeHomColumnEquiv R D F N (q + 1)
    (dgCoherentBarNormalizedHomColumnDifferential R D F N q
      ((dgCoherentBarNormalizedNativeHomColumnEquiv R D F N q).symm a))

lemma dgCoherentBarNormalizedNativeHomEquiv_d (q : ℤ)
    (z : (moduleHom R D (dgCoherentBarNormalizedModule R D F hMC) N).X q) :
    dgCoherentBarNormalizedNativeHomEquiv R D F hMC N (q + 1)
      ((moduleHom R D (dgCoherentBarNormalizedModule R D F hMC) N).d q (q + 1) z) =
      dgCoherentBarNormalizedNativeHomDifferential R D F N q
        (dgCoherentBarNormalizedNativeHomEquiv R D F hMC N q z) := by
  simp only [dgCoherentBarNormalizedNativeHomEquiv, LinearEquiv.trans_apply,
    dgCoherentBarNormalizedNativeHomDifferential, LinearEquiv.symm_apply_apply,
    dgCoherentBarNormalizedHomColumnsEquiv_d]

end SerrePositivity.InfinityCategories
