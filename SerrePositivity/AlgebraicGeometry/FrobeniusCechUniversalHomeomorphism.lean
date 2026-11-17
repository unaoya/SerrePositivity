module

public import SerrePositivity.AlgebraicGeometry.FrobeniusDirectLimitInvariance
public import SerrePositivity.AlgebraicGeometry.FrobeniusArrowNaturality
public import SerrePositivity.AlgebraicGeometry.FrobeniusAugmentedRingCoefficients

/-!
概要：両端が普遍同相の同じ四角形は、増大Frobenius係数の同型を与える。
方針：既存の両端の環同型と元の可換性を、同じArrow・conerveの関手へ渡す。
規約：元の増大・全正次数を保持し、H⁰だけの移送に弱めない。
使われ方：Noether帰納の実際のnil閉厚化のアフィン係数の移送。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable {f g : Arrow CommRingCat.{u}} (F : f ⟶ g) (p : ℕ) (hp : p.Prime)
variable (hA : (p : f.left) = 0) (hB : (p : f.right) = 0)
variable (hC : (p : g.left) = 0) (hD : (p : g.right) = 0)
variable (hL : SerrePositivity.CommutativeAlgebra.IsUniversalHomeomorphism F.left.hom)
variable (hR : SerrePositivity.CommutativeAlgebra.IsUniversalHomeomorphism F.right.hom)

set_option backward.isDefEq.respectTransparency false in
/-- 同じ普遍同相の四角形から得る、元の実際のFrobenius矢印の同型。 -/
def frobeniusDirectLimitArrowIsoOfUniversalHomeomorphisms :
    Arrow.mk (CommRingCat.ofHom (frobeniusDirectLimitMap p hp hA hB f.hom.hom)) ≅
      Arrow.mk (CommRingCat.ofHom (frobeniusDirectLimitMap p hp hC hD g.hom.hom)) :=
  Arrow.isoMk
    (frobeniusDirectLimitUniversalHomeomorphismEquiv p hp hA hC F.left.hom hL).toCommRingCatIso
    (frobeniusDirectLimitUniversalHomeomorphismEquiv p hp hB hD F.right.hom hR).toCommRingCatIso
    (frobeniusDirectLimitArrowMap F p hp hA hB hC hD).w

/-- 同じ両端の普遍同相は、元の増大Frobenius係数の環図式全体の同型を与える。 -/
def frobeniusAugmentedRingCoefficientsIsoOfUniversalHomeomorphisms :
    frobeniusAugmentedRingCoefficients f p hp hA ≅ frobeniusAugmentedRingCoefficients g p hp hC :=
  frobeniusAugmentedRingCoefficientsIso f p hp hA hB ≪≫
    CosimplicialObject.augmentedCechConerve.mapIso
      (frobeniusDirectLimitArrowIsoOfUniversalHomeomorphisms F p hp hA hB hC hD hL hR) ≪≫
        (frobeniusAugmentedRingCoefficientsIso g p hp hC hD).symm

include F hB hD hL hR in
/-- 同じ普遍同相による係数移送で、元の増大・全正次数の完全性は同値。 -/
theorem frobeniusAugmentedRingCoefficients_exact_iff_of_universalHomeomorphisms :
    SerrePositivity.Cech.AugmentedRingCechExact (frobeniusAugmentedRingCoefficients f p hp hA) ↔
      SerrePositivity.Cech.AugmentedRingCechExact (frobeniusAugmentedRingCoefficients g p hp hC) :=
  SerrePositivity.Cech.ringCechExact_iff_of_iso
    (frobeniusAugmentedRingCoefficientsIsoOfUniversalHomeomorphisms F p hp hA hB hC hD hL hR)

end SerrePositivity.AlgebraicGeometry
