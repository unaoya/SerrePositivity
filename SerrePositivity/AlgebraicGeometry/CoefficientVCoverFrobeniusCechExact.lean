module

public import SerrePositivity.AlgebraicGeometry.NoetherianAffineVCoverFrobeniusCechExact
public import SerrePositivity.AlgebraicGeometry.CoefficientVCoverModelPrimeCast
public import SerrePositivity.AlgebraicGeometry.CoefficientVCoverModelFinal
public import SerrePositivity.AlgebraicGeometry.FrobeniusArrowFamilyColimit

/-!
概要：係数環上の被覆模型の完全構造層のČech完全性を元の被覆へ戻す。
方針：同じ有限段のNoetherなv被覆、二変数のFrobenius余極限比較、B1を合成する。
規約：元の両端の環と元の射を保持する。
使われ方：有限型素体への帰着の出口（承認済み計画E16）。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u
set_option backward.isDefEq.respectTransparency false

/-- 同じ被覆模型のfiltered colimitにより得る、元のFrobenius係数のČech完全性。 -/
theorem coefficientVCover_frobeniusCechExact
    (k : Type u) [CommRing k] [IsNoetherianRing k]
    {R S : Type u} [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    (g : R →ₐ[k] S) (hv : IsAffineVCover g.toRingHom)
    (p : ℕ) (hp : p.Prime) (hK : (p : k) = 0) (hR : (p : R) = 0) :
    SerrePositivity.Cech.AugmentedRingCechExact
      (frobeniusAugmentedRingCoefficients (Arrow.mk (CommRingCat.ofHom g.toRingHom)) p hp hR) := by
  let D := coefficientVCoverModelSmallArrowDiagram k g
  let c := coefficientVCoverModelSmallArrowCocone k g
  let hL := fun j ↦ (coefficientVCoverModel_primeCast k g p hK j).1
  let hS := fun j ↦ (coefficientVCoverModel_primeCast k g p hK j).2
  have hT : (p : S) = 0 := by rw [← map_natCast g.toRingHom, hR, map_zero]
  haveI := isFiltered_coefficientVCoverModelIndex k g hv
  have hd (j) : SerrePositivity.Cech.IsCechExact (Arrow.mk (CommRingCat.ofHom
      (frobeniusDirectLimitMap p hp (hL j) (hS j) (D.obj j).hom.hom))) :=
    (frobeniusAugmentedRingCoefficients_exact_iff (D.obj j) p hp (hL j) (hS j)).mp
      (noetherianAffineVCover_frobeniusCechExact (D.obj j).hom.hom
        (coefficientVCoverModelSmallArrow_finitePresentation k g j)
        (coefficientVCoverModelSmallArrow_vCover k g j) p hp (hL j))
  exact (frobeniusAugmentedRingCoefficients_exact_iff
    (Arrow.mk (CommRingCat.ofHom g.toRingHom)) p hp hR hT).mpr
      (frobeniusCechExact_of_filtered_arrow_models D p hp hL hS c hR hT
        (coefficientVCoverModelSmallArrowCoconeIsColimit k g hv) hd)

end SerrePositivity.AlgebraicGeometry
