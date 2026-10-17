module
public import SerrePositivity.DifferentialGraded.Endomorphism.IsoLocus
public import SerrePositivity.DifferentialGraded.Endomorphism.HomPreservesCoproducts
public import SerrePositivity.DifferentialGraded.Endomorphism.CompactUnitCounit
public import Mathlib.CategoryTheory.Adjunction.Limits

/-! # 実際の導来随伴の単位の全対象での可逆性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (S : Set D) (E : PerfectDGModuleOver A D S)
variable (compactToPerfect : ∀ P : DerivedModuleCategory A (EndomorphismObject E.val),
  moduleCompact A (EndomorphismObject E.val) P →
    modulePerfect A (EndomorphismObject E.val) P)
include compactToPerfect

lemma perfectEndomorphismHom_preservesCoproductsOfShape (J : Type u) :
    PreservesColimitsOfShape (Discrete J)
      (endomorphismDerivedHom A D E.val E.property.1) where
  preservesColimit {K} := by
    let := perfectEndomorphismHom_preservesCoproduct A D S E compactToPerfect
      (K.obj ∘ Discrete.mk)
    exact preservesColimit_of_iso_diagram _ Discrete.natIsoFunctor.symm

variable (hgen : endomorphismThickGeneratesPerfect A D S E)
include hgen

/-- 単位の同型性を、実際の標準解像度と余積保存で全End導来対象へ拡張する。 -/
lemma endomorphismDerivedUnit_isIso_all
    (N : DerivedModuleCategory A (EndomorphismObject E.val)) :
    IsIso ((endomorphismDerivedUnit A D E.val E.property.1).app N) := by
  let L := endomorphismDerivedTensor A D E.val
  let R := endomorphismDerivedHom A D E.val E.property.1
  let := endomorphismDerivedTensorCommShift A D E.val E.property.1
  let := endomorphismDerivedHomCommShift A D E.val E.property.1
  let := endomorphismDerivedTensorIsTriangulated A D E.val E.property.1
  let := endomorphismDerivedHomIsTriangulated A D E.val E.property.1
  let := endomorphismDerivedTensor_additive A D E.val E.property.1
  let := endomorphismDerivedHom_additive A D E.val E.property.1
  let := endomorphismDerivedUnit_commShift A D E.val E.property.1
  let P := derivedNatTransIsoLocus A (EndomorphismObject E.val) (L ⋙ R)
    (endomorphismDerivedUnit A D E.val E.property.1)
  change P N
  apply moduleLocalizing_all A (EndomorphismObject E.val) P
  · intro J F hF
    let := (endomorphismDerivedAdjunction A D E.val E.property.1).leftAdjoint_preservesColimits
    let := perfectEndomorphismHom_preservesCoproductsOfShape A D S E compactToPerfect J
    exact derivedNatTransIsoLocus_coproduct A (EndomorphismObject E.val) (L ⋙ R)
      (endomorphismDerivedUnit A D E.val E.property.1) F hF
  · intro X hX
    exact endomorphismDerivedUnit_isIso_onPerfect A D S E hgen ⟨X, hX⟩

end SerrePositivity.DifferentialGraded
