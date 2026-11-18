module

public import SerrePositivity.AlgebraicGeometry.CoefficientVCoverFrobeniusCechExact
public import SerrePositivity.AlgebraicGeometry.PrimeFieldRingHom
public import Mathlib.RingTheory.Noetherian.Basic

/-!
概要：任意のaffine v被覆の完全構造層のČech完全性を素体の模型から得る。
方針：持ち上げたZMod pからの係数構造を同じ元の環写像に沿って選ぶ。
規約：非零性もCharP R pも仮定せず、零環を含める。
使われ方：BS17 Thm 4.1(i)への出口（承認済み計画E18）。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false

/-- 任意の元のaffine v被覆のFrobenius係数の増大Čech完全性。 -/
theorem affineVCover_frobeniusCechExact
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hv : IsAffineVCover f) (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) :
    SerrePositivity.Cech.AugmentedRingCechExact
      (frobeniusAugmentedRingCoefficients (CategoryTheory.Arrow.mk (CommRingCat.ofHom f)) p hp hR) := by
  letI : Fact p.Prime := ⟨hp⟩
  let K := ULift.{u} (ZMod p)
  let e : K ≃+* ZMod p := ULift.ringEquiv
  letI : IsNoetherianRing K := isNoetherianRing_of_ringEquiv (ZMod p) e.symm
  let a : K →+* R := primeFieldRingHom R p hR
  letI : Algebra K R := a.toAlgebra
  letI : Algebra K S := (f.comp a).toAlgebra
  let g : R →ₐ[K] S := { __ := f, commutes' := fun _ ↦ rfl }
  have hK : (p : K) = 0 :=
    congrArg (ULift.up : ZMod p → K) (ZMod.natCast_self p)
  exact coefficientVCover_frobeniusCechExact K g hv p hp hK hR

end SerrePositivity.AlgebraicGeometry
