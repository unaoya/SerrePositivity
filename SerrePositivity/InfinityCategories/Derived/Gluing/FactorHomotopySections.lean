module
public import SerrePositivity.InfinityCategories.Derived.Gluing.FactorHomotopyEquivalences

/-! 因子の実 H⁰ 同値の逆から得る、元の二圏の gluing H⁰ への切断関手。 -/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
local notation "G" => DGGluingObject R C D M

def dgGluingCSectionHomotopy (hD : IsDGPretriangulated R D) :
    HomotopyCategory R C ⥤ HomotopyCategory R G :=
  (dgGluingCFactorHomotopyEquivalence R C D M hD).inverse ⋙
    (dgGluingCFactorInclusion R C D M).onHomotopy

def dgGluingDSectionHomotopy (hC : IsDGPretriangulated R C) :
    HomotopyCategory R D ⥤ HomotopyCategory R G :=
  (dgGluingDFactorHomotopyEquivalence R C D M hC).inverse ⋙
    (dgGluingDFactorInclusion R C D M).onHomotopy

lemma dgGluingCSectionHomotopy_right_zero (hD : IsDGPretriangulated R D)
    (Y : HomotopyCategory R C) :
    dgGluingFactorIsZero R D
      (ForgetEnrichment.to (Complex R) ((dgGluingCSectionHomotopy R C D M hD).obj Y).as).right := by
  let Z := (dgGluingCFactorHomotopyEquivalence R C D M hD).inverse.obj Y
  exact (ForgetEnrichment.to (Complex R) Z.as).property

omit [Small.{u} D] in
lemma dgGluingDSectionHomotopy_left_zero (hC : IsDGPretriangulated R C)
    (Y : HomotopyCategory R D) :
    dgGluingFactorIsZero R C
      (ForgetEnrichment.to (Complex R) ((dgGluingDSectionHomotopy R C D M hC).obj Y).as).left := by
  let Z := (dgGluingDFactorHomotopyEquivalence R C D M hC).inverse.obj Y
  exact (ForgetEnrichment.to (Complex R) Z.as).property

/-- C の同じ切断と左射影の合成は、因子同値の実余単位により恒等と同型。 -/
def dgGluingCSectionProjectionIso (hD : IsDGPretriangulated R D) :
    dgGluingCSectionHomotopy R C D M hD ⋙ (dgGluingLeft R C D M).onHomotopy ≅
      𝟭 (HomotopyCategory R C) := by
  let e := dgGluingCFactorHomotopyEquivalence R C D M hD
  have h : (dgGluingCFactorInclusion R C D M).onHomotopy ⋙
      (dgGluingLeft R C D M).onHomotopy = e.functor :=
    (DGFunctor.onHomotopy_comp (dgGluingCFactorInclusion R C D M)
      (dgGluingLeft R C D M)).symm
  exact (Functor.associator e.inverse _ _) ≪≫
    Functor.isoWhiskerLeft e.inverse (eqToIso h) ≪≫ e.counitIso

/-- D の同じ切断と右射影の合成も、因子同値の実余単位により恒等と同型。 -/
def dgGluingDSectionProjectionIso (hC : IsDGPretriangulated R C) :
    dgGluingDSectionHomotopy R C D M hC ⋙ (dgGluingRight R C D M).onHomotopy ≅
      𝟭 (HomotopyCategory R D) := by
  let e := dgGluingDFactorHomotopyEquivalence R C D M hC
  have h : (dgGluingDFactorInclusion R C D M).onHomotopy ⋙
      (dgGluingRight R C D M).onHomotopy = e.functor :=
    (DGFunctor.onHomotopy_comp (dgGluingDFactorInclusion R C D M)
      (dgGluingRight R C D M)).symm
  exact (Functor.associator e.inverse _ _) ≪≫
    Functor.isoWhiskerLeft e.inverse (eqToIso h) ≪≫ e.counitIso

end SerrePositivity.InfinityCategories
