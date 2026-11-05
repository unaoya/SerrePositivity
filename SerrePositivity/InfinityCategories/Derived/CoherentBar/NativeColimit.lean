module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconePointFiberIso
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.PointHomFamilyFiberCriterion
/-!
概要：指定した正規化 bar の native 余錐は、実 dg nerve の余極限である。
方針：固定終点の実 fiber 同型で標準 Hom の族を同値とし、右 Hom 比較による判定へ渡す。
規約：MC 仮定付き API と D の公開 MC を代入した無条件版を併設する。
使われ方：DGKappaStrictFilteredColimitComparison の正規化 native 余極限の入力。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))
  (hMC : dgCoherentBarMaurerCartan R D F)

lemma dgCoherentBarNormalizedNativeCocone_pointHomFamily_homotopyEquivalence
    (y : (dgNerve R (RightModule R D)) _⦋0⦌) :
    IsSimplicialHomotopyEquivalence (HomotopyLimits.coconePointHomFamily
      (dgCoherentBarNormalizedNativeCocone R D F hMC) y) := by
  exact dgCoherentBarPointHomFamily_equivalence_of_fiberComparison
    (sliceUnderProjection F) (sliceUnderProjection
      ((SSet.yonedaEquiv (X := dgNerve R (RightModule R D))).symm
        (dgCoherentBarNativeApex R D F hMC)))
    (dgCoherentBarCoconePointComparison R D F hMC)
    (dgCoherentBarCoconePointComparison_projection R D F hMC)
    (dgCoherentBarNormalizedNativeCocone R D F hMC)
    (cosliceIdentityCone (dgCoherentBarNativeApex R D F hMC))
    (dgCoherentBarCoconePointComparison_native R D F hMC)
    (cosliceIdentityCone_isInitialVertex (dgCoherentBarNativeApex R D F hMC)) y
    (dgCoherentBarCoconePointFiber_homotopyEquivalence R D F hMC y).isQCatEquivalence

lemma dgCoherentBarNormalizedNativeCocone_pointHomComparison_homotopyEquivalence
    (y : (dgNerve R (RightModule R D)) _⦋0⦌) :
    IsSimplicialHomotopyEquivalence
      (HomotopyLimits.coconePointHomFamily (dgCoherentBarNormalizedNativeCocone R D F hMC) y ≫
        (dgCoherentBarCoconeHomSpaceIso R D F hMC y).hom) :=
  (dgCoherentBarNormalizedNativeCocone_pointHomFamily_homotopyEquivalence R D F hMC y).comp
    (dgCoherentBarCoconeHomSpaceComparison_homotopyEquivalence R D F hMC y)

lemma dgCoherentBarNormalizedNativeCocone_isColimit :
    IsColimitCone (dgCoherentBarNormalizedNativeCocone R D F hMC) :=
  dgCoherentBarNormalizedNativeCocone_isColimit_of_pointHomComparison R D F hMC
    (fun y => dgCoherentBarNormalizedNativeCocone_pointHomComparison_homotopyEquivalence
      R D F hMC y)

lemma dgCoherentBarNormalizedNativeCoconeUnconditional_isColimit :
    IsColimitCone (dgCoherentBarNormalizedNativeCoconeUnconditional R D F) :=
  dgCoherentBarNormalizedNativeCocone_isColimit R D F (dgCoherentBarTheta_maurerCartan R D F)

lemma dgCoherentBarNormalizedNativeCoconeUnconditional_pointHomComparison_homotopyEquivalence
    (y : (dgNerve R (RightModule R D)) _⦋0⦌) :
    IsSimplicialHomotopyEquivalence
      (HomotopyLimits.coconePointHomFamily
        (dgCoherentBarNormalizedNativeCoconeUnconditional R D F) y ≫
        (dgCoherentBarCoconeHomSpaceIsoUnconditional R D F y).hom) :=
  dgCoherentBarNormalizedNativeCocone_pointHomComparison_homotopyEquivalence R D F
    (dgCoherentBarTheta_maurerCartan R D F) y

end SerrePositivity.InfinityCategories
