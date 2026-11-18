module

public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechGlobalAugmentedTotal
public import SerrePositivity.AlgebraicGeometry.AffineScalarPerfectCech
public import SerrePositivity.AlgebraicGeometry.CechRingIntegerCoefficients

/-!
概要：元の環の増大conerveと同じアフィンタプルČechのtotalの比較。
方針：既存のΓ–Specの自然同型と増大の式を同じFrobenius係数でまとめる。
規約：元の基底環の増大と最終のAugmentedRingCechExactの型を保つČech版。
使われ方：Noether基底上の幾何的降下から元の環の降下への出口。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Opposite
universe u
local notation "up" => ComplexShape.up ℕ
variable {R : Type u} [CommRing R] (Y : Scheme.{u})
variable (f : Y ⟶ Spec (CommRingCat.of R)) [IsAffine Y]
variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0)

set_option backward.isDefEq.respectTransparency false in
/-- 元の基底で恒等の、環の増大conerveと同じΓの増大係数の自然同型。 -/
def affineScalarPerfectAugmentedIso :
    ((CosimplicialObject.Augmented.whiskeringObj _ _ ringToCechIntegerModule).obj
      (frobeniusAugmentedRingCoefficients
        (Arrow.mk (CommRingCat.ofHom (schemeScalarHom Y f))) p hp hR)) ≅
      schemePerfectCechGlobalAugmented f p hp hR :=
  Comma.isoMk (Iso.refl _) (affineScalarPerfectCechIso Y f p hp hR) (by
    apply NatTrans.ext
    funext n
    change 𝟙 _ ≫ schemePerfectCechGlobalScalar f p hp hR n = _
    rw [Category.id_comp]
    exact (affineScalarPerfectCechIso_augmentation Y f p hp hR n).symm)

variable {ι : Type} [Fintype ι] [DecidableEq ι] (U : ι → Y.Opens)

set_option backward.isDefEq.respectTransparency false in
/-- 元の環の増大conerveの完全性は、同じアフィンタプルtotalの完全性と同値のČech版。
BS17 Theorem 4.1(i) のアフィン環の出口に使う。
分離的なスキームの準連接層ではアフィン被覆のČechと一致する
（Stacks 30.2.6）が、この比較は形式化しない。 -/
theorem affineScalarPerfectCech_exact_iff_tuple_total_acyclic
    (hU : ∀ i, IsAffineOpen (U i)) (hcU : (⨆ i, U i) = ⊤) :
    SerrePositivity.Cech.AugmentedRingCechExact
      (frobeniusAugmentedRingCoefficients
        (Arrow.mk (CommRingCat.ofHom (schemeScalarHom Y f))) p hp hR) ↔
      (HomologicalComplex₂.total (C := ModuleCat.{u} ℤ)
        (schemePerfectCechTupleDouble f U p hp hR) up).Acyclic := by
  rw [ringCechExact_iff_integer_acyclic]
  let e := SerrePositivity.Cech.augmentedCochain.mapIso
    (affineScalarPerfectAugmentedIso Y f p hp hR)
  have he : (SerrePositivity.Cech.augmentedCochain.obj
      ((CosimplicialObject.Augmented.whiskeringObj _ _ ringToCechIntegerModule).obj
        (frobeniusAugmentedRingCoefficients
          (Arrow.mk (CommRingCat.ofHom (schemeScalarHom Y f))) p hp hR))).Acyclic ↔
      (SerrePositivity.Cech.augmentedCochain.obj
        (schemePerfectCechGlobalAugmented f p hp hR)).Acyclic := by
    constructor
    · intro h n
      exact (h n).of_iso e
    · intro h n
      exact (h n).of_iso e.symm
  exact he.trans (affineCechNerveTupleAugmentedGlobal_acyclic_iff f U p hp hR hU hcU).symm

end SerrePositivity.AlgebraicGeometry
