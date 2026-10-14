module

public import SerrePositivity.CommutativeAlgebra.ModuleSupportHeight
public import SerrePositivity.KTheory.Adams.CupVanishing
public import SerrePositivity.PerfectComplex.TensorTorComparison

/-! # Intersection vanishing from a supported Adams family -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
namespace SerrePositivity
open TensorProduct IsLocalRing
variable {R : Type u} [CommRing R] [IsRegularLocalRing R]
variable {E : Type v} [Field E] [CharZero E] {p : ℕ}

/-- A proved family of supported Adams operators implies the integer-valued vanishing theorem. -/
theorem intersectionVanishing_of_adamsFamily (F : Adams.LocalizationAdamsFamily R E p)
    (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N]
    (hfin : Module.length R (M ⊗[R] N) ≠ ⊤)
    (hdim : Module.supportDim R M + Module.supportDim R N < ringKrullDim R) :
    chi R M N = 0 := by
  obtain ⟨cM, cN, hM, hN, hc⟩ := exists_supportHeight_sum_gt (R := R) M N hdim
  let FM := chosenPerfectModuleResolution (ModuleCat.of R M)
  let FN := chosenPerfectModuleResolution (ModuleCat.of R N)
  let x := FM.k0Class (finiteModuleClosedSupport R M) (support_subset_finiteModuleClosedSupport R M)
  let y := FN.k0Class (finiteModuleClosedSupport R N) (support_subset_finiteModuleClosedSupport R N)
  let h := finiteModuleClosedSupport_inf_le_maximal R M N hfin
  have hz := F.cup_enlarge_eq_zero (dimToNat (ringKrullDim R))
    (natCast_dimToNat_ringKrullDim R).symm
    (finiteModuleClosedSupport R M) (finiteModuleClosedSupport R N) cM cN hM hN hc h
    ((1 : E) ⊗ₜ[ℤ] x) ((1 : E) ⊗ₜ[ℤ] y)
  have he := congrArg (K0WithSupport.coefficientEuler E R) hz
  simp only [K0WithSupport.coefficientCup_tmul, one_mul,
    K0WithSupport.coefficientEnlarge_tmul, K0WithSupport.coefficientEuler_tmul,
    map_zero] at he
  have hi : K0WithSupport.integerEuler R
      (K0WithSupport.enlarge h (K0WithSupport.cup x y)) = 0 := by
    exact_mod_cast he
  exact (integerEuler_cup_resolutions_of_finiteTensor FM FN hfin).symm.trans hi

end SerrePositivity
