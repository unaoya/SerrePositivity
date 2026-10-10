module

public import SerrePositivity.LengthAlgebra.SerreQuotient

/-! # 有限な長さの商から全ての長さの商への完全関手 -/

@[expose] public section

universe u

namespace SerrePositivity.LengthAlgebra

open CategoryTheory CategoryTheory.Limits
open scoped ENNReal

variable {R : Type u} [CommRing R] {J : Ideal R} (lam : NormalizedLength R J)

/-- 有限な長さの冪ねじれ加群の、全ての冪ねじれ加群への包含。 -/
def finiteTorsionInclusion : FiniteLengthTorsion lam ⥤ PowTorsionModule J :=
  (powTorsionModule J).lift (finiteLengthTorsion lam).ι (fun M ↦ M.property.1)

noncomputable instance : PreservesFiniteLimits (finiteTorsionInclusion lam) := by
  let : PreservesFiniteLimits (finiteTorsionInclusion lam ⋙ (powTorsionModule J).ι) :=
    inferInstanceAs (PreservesFiniteLimits (finiteLengthTorsion lam).ι)
  exact preservesFiniteLimits_of_reflects_of_preserves _ (powTorsionModule J).ι

noncomputable instance : PreservesFiniteColimits (finiteTorsionInclusion lam) := by
  let : PreservesFiniteColimits (finiteTorsionInclusion lam ⋙ (powTorsionModule J).ι) :=
    inferInstanceAs (PreservesFiniteColimits (finiteLengthTorsion lam).ι)
  exact preservesFiniteColimits_of_reflects_of_preserves _ (powTorsionModule J).ι

/-- 小さい商で可逆になる射は、大きな商でも可逆になる。 -/
lemma finiteTorsionInclusion_inverts :
    (zeroAdditiveLength (finiteLength lam)).isoModSerre.IsInvertedBy
      (finiteTorsionInclusion lam ⋙ lengthQuotientFunctor lam) := by
  apply ((zeroAdditiveLength (finiteLength lam)).isoModSerre_isInvertedBy_iff _).mpr
  intro M hM
  apply (ObjectProperty.SerreClassLocalization.isZero_obj_iff
    (lengthQuotientFunctor lam) (zeroAdditiveLength (torsionLength lam)) _).mpr
  change lam.len M.obj = 0
  change (lam.len M.obj).toReal = 0 at hM
  exact ((ENNReal.toReal_eq_zero_iff _).mp hM).resolve_right M.property.2

/-- 二つの商を結ぶ関手。 -/
noncomputable def finiteQuotientInclusion : FiniteLengthQuotient lam ⥤ LengthQuotient lam :=
  Localization.lift (finiteTorsionInclusion lam ⋙ lengthQuotientFunctor lam)
    (finiteTorsionInclusion_inverts lam) (finiteLengthQuotientFunctor lam)

/-- 商関手との可換性を与える自然同型。 -/
noncomputable def finiteQuotientInclusionIso :
    finiteLengthQuotientFunctor lam ⋙ finiteQuotientInclusion lam ≅
      finiteTorsionInclusion lam ⋙ lengthQuotientFunctor lam :=
  Localization.fac _ (finiteTorsionInclusion_inverts lam) _

noncomputable instance : PreservesFiniteLimits (finiteQuotientInclusion lam) := by
  apply (ObjectProperty.SerreClassLocalization.preservesFiniteLimits_comp_iff
    (finiteLengthQuotientFunctor lam) (zeroAdditiveLength (finiteLength lam)) _).mp
  exact preservesFiniteLimits_of_natIso (finiteQuotientInclusionIso lam).symm

noncomputable instance : PreservesFiniteColimits (finiteQuotientInclusion lam) := by
  apply (ObjectProperty.SerreClassLocalization.preservesFiniteColimits_comp_iff
    (finiteLengthQuotientFunctor lam) (zeroAdditiveLength (finiteLength lam)) _).mp
  exact preservesFiniteColimits_of_natIso (finiteQuotientInclusionIso lam).symm

/-- 二つの商上の長さは、有限値を非負拡大実数に戻すと一致する。 -/
theorem finiteQuotientInclusion_length (X : FiniteLengthQuotient lam) :
    extendedQuotientLength lam ((finiteQuotientInclusion lam).obj X) =
      ENNReal.ofReal (quotientLength lam X) := by
  obtain ⟨M, rfl⟩ :=
    (Localization.Construction.objEquiv
      (zeroAdditiveLength (finiteLength lam)).isoModSerre).surjective X
  calc
    _ = lam.len M.obj := extendedQuotientLength_iso lam ((finiteQuotientInclusionIso lam).app M)
    _ = ENNReal.ofReal (lam.len M.obj).toReal := (ENNReal.ofReal_toReal M.property.2).symm

end SerrePositivity.LengthAlgebra
