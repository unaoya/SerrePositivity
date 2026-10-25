module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeHomSpaceIso
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationFiberReflection
public import SerrePositivity.InfinityCategories.Core.InitialEquivalence
public import SerrePositivity.InfinityCategories.Stable.IdentityCocone
/-!
概要：可変終点での coslice 比較から、指定した native 余錐の余極限性を反映する。
方針：left fibration の全 fiber の同値で全空間の同値を得て、恒等余錐の始対象性を移す。
規約：coslice 比較は明示入力であり、その存在を公理として追加しない。
使われ方：固定終点の同型から native 余極限性へ接続する設計追加の境界。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
attribute [local instance] vertexFiber_kanComplex_of_leftFibration
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))
  (hMC : dgCoherentBarMaurerCartan R D F)

local instance : Quasicategory (sliceUnder F) :=
  quasicategory_of_innerFibration (sliceUnderProjection F)

local instance : Quasicategory (sliceUnder
    ((SSet.yonedaEquiv (X := dgNerve R (RightModule R D))).symm
      (dgCoherentBarNativeApex R D F hMC))) :=
  quasicategory_of_innerFibration (sliceUnderProjection
    ((SSet.yonedaEquiv (X := dgNerve R (RightModule R D))).symm
      (dgCoherentBarNativeApex R D F hMC)))

lemma dgCoherentBarNormalizedNativeCocone_isColimit_of_cosliceComparison
    (C : sliceUnder ((SSet.yonedaEquiv (X := dgNerve R (RightModule R D))).symm
      (dgCoherentBarNativeApex R D F hMC)) ⟶ sliceUnder F)
    (hOver : C ≫ sliceUnderProjection F = sliceUnderProjection
      ((SSet.yonedaEquiv (X := dgNerve R (RightModule R D))).symm
        (dgCoherentBarNativeApex R D F hMC)))
    (hFib : ∀ y : (dgNerve R (RightModule R D)) _⦋0⦌,
      IsQCatEquivalence (vertexFiberMap (sliceUnderProjection
        ((SSet.yonedaEquiv (X := dgNerve R (RightModule R D))).symm
          (dgCoherentBarNativeApex R D F hMC))) (sliceUnderProjection F) C hOver y))
    (hVertex : C.app (Opposite.op ⦋0⦌)
      (cosliceIdentityCone (dgCoherentBarNativeApex R D F hMC)) =
        dgCoherentBarNormalizedNativeCocone R D F hMC) :
    IsColimitCone (dgCoherentBarNormalizedNativeCocone R D F hMC) := by
  have hC : IsQCatEquivalence C :=
    (leftFibration_isQCatEquivalence_iff_fibers (sliceUnderProjection
      ((SSet.yonedaEquiv (X := dgNerve R (RightModule R D))).symm
        (dgCoherentBarNativeApex R D F hMC))) (sliceUnderProjection F) C hOver).mpr hFib
  have hInitial := hC.choose.map_isInitialVertex
    (cosliceIdentityCone_isInitialVertex (dgCoherentBarNativeApex R D F hMC))
  change IsInitialVertex (C.app (Opposite.op ⦋0⦌)
    (cosliceIdentityCone (dgCoherentBarNativeApex R D F hMC))) at hInitial
  rw [hVertex] at hInitial
  exact hInitial

end SerrePositivity.InfinityCategories
