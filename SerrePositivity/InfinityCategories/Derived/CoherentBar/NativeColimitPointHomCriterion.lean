module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeHomSpaceEquivalence
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoconePointHomInitiality
/-!
概要：指定 native 余錐の標準 Hom の族を、既存の右 pinched Hom 同型で検査する。
方針：全終点で合成が同値という入力を既存の余極限反映判定へ渡す。
規約：合成の同値性は明示入力とし、公開 MC を代入する版も併設する。
使われ方：工程Bの固定終点経路の最終接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))
  (hMC : dgCoherentBarMaurerCartan R D F)

lemma dgCoherentBarNormalizedNativeCocone_isColimit_of_pointHomComparison
    (h : ∀ y : (dgNerve R (RightModule R D)) _⦋0⦌,
      IsSimplicialHomotopyEquivalence
        (HomotopyLimits.coconePointHomFamily
          (dgCoherentBarNormalizedNativeCocone R D F hMC) y ≫
          (dgCoherentBarCoconeHomSpaceIso R D F hMC y).hom)) :
    IsColimitCone (dgCoherentBarNormalizedNativeCocone R D F hMC) := by
  apply HomotopyLimits.isColimitCone_of_pointHomFamily_comparison
    (dgCoherentBarNormalizedNativeCocone R D F hMC)
    (fun y => DGNerve.pinchedHom R (RightModule R D)
      (dgCoherentBarNormalizedModule R D F hMC)
      (dgNerve.vertexEquiv R (RightModule R D) y))
    (fun y => (dgCoherentBarCoconeHomSpaceIso R D F hMC y).hom)
    (fun y => dgCoherentBarCoconeHomSpaceComparison_homotopyEquivalence R D F hMC y)
  exact h

lemma dgCoherentBarNormalizedNativeCoconeUnconditional_isColimit_of_pointHomComparison
    (h : ∀ y : (dgNerve R (RightModule R D)) _⦋0⦌,
      IsSimplicialHomotopyEquivalence
        (HomotopyLimits.coconePointHomFamily
          (dgCoherentBarNormalizedNativeCoconeUnconditional R D F) y ≫
          (dgCoherentBarCoconeHomSpaceIsoUnconditional R D F y).hom)) :
    IsColimitCone (dgCoherentBarNormalizedNativeCoconeUnconditional R D F) :=
  dgCoherentBarNormalizedNativeCocone_isColimit_of_pointHomComparison R D F
    (dgCoherentBarTheta_maurerCartan R D F) h

end SerrePositivity.InfinityCategories
