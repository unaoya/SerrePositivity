module

public import SerrePositivity.AlgebraicGeometry.AffineScalarPerfectTupleTotal
public import SerrePositivity.AlgebraicGeometry.FrobeniusDirectLimitRingIso

/-!
概要：任意の元の環準同型のČech完全性を、同じSpec.mapのタプルtotalへ戻す。
方針：ΓSpecの自然性を同じFrobeniusの矢印と増大conerveへ移す。
規約：元のR・Sとρ、基底の増大、最終のAugmentedRingCechExactを保つ。
使われ方：幾何的なNoether帰納の結論を元の環の主張へ戻す出口。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Opposite
universe u
variable {R S : Type u} [CommRing R] [CommRing S] (ρ : R →+* S)
variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0)

set_option backward.isDefEq.respectTransparency false in
/-- 元の環準同型と、同じSpec.mapの大域スカラーのFrobeniusの矢印の同型。 -/
def specScalarFrobeniusArrowIso (hS : (p : S) = 0) :
    Arrow.mk (CommRingCat.ofHom (frobeniusDirectLimitMap p hp hR hS ρ)) ≅
      Arrow.mk (CommRingCat.ofHom (frobeniusDirectLimitMap p hp hR
        (schemeScalarPresheaf_primeCast (Spec (CommRingCat.of S))
          (Spec.map (CommRingCat.ofHom ρ)) p hR (op ⊤))
        (schemeScalarHom (Spec (CommRingCat.of S)) (Spec.map (CommRingCat.ofHom ρ))))) := by
  let hΓ := schemeScalarPresheaf_primeCast (Spec (CommRingCat.of S))
    (Spec.map (CommRingCat.ofHom ρ)) p hR (op ⊤)
  let e := (frobeniusDirectLimitRingIso p hp hS hΓ
    (Scheme.ΓSpecIso (CommRingCat.of S)).symm).toCommRingCatIso
  refine Arrow.isoMk (Iso.refl _) e ?_
  apply CommRingCat.hom_ext
  apply DirectLimit.Ring.hom_ext
  intro n
  apply RingHom.ext
  intro x
  change frobeniusDirectLimitOf _ p hp hΓ n
      (schemeScalarHom (Spec (CommRingCat.of S)) (Spec.map (CommRingCat.ofHom ρ)) x) =
    frobeniusDirectLimitOf _ p hp hΓ n ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (ρ x))
  exact congrArg (frobeniusDirectLimitOf _ p hp hΓ n)
    (congrArg (fun k ↦ k.hom x) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ρ))).symm

/-- 元の環準同型の増大Frobenius係数と、同じ大域スカラーの増大係数の同型。 -/
def specScalarFrobeniusAugmentedIso (hS : (p : S) = 0) :
    frobeniusAugmentedRingCoefficients (Arrow.mk (CommRingCat.ofHom ρ)) p hp hR ≅
      frobeniusAugmentedRingCoefficients
        (Arrow.mk (CommRingCat.ofHom (schemeScalarHom (Spec (CommRingCat.of S))
          (Spec.map (CommRingCat.ofHom ρ))))) p hp hR := by
  let hΓ := schemeScalarPresheaf_primeCast (Spec (CommRingCat.of S))
    (Spec.map (CommRingCat.ofHom ρ)) p hR (op ⊤)
  let e₁ := frobeniusAugmentedRingCoefficientsIso (Arrow.mk (CommRingCat.ofHom ρ)) p hp hR hS
  let e₂ := CosimplicialObject.augmentedCechConerve.mapIso
    (specScalarFrobeniusArrowIso ρ p hp hR hS)
  let e₃ := frobeniusAugmentedRingCoefficientsIso
    (Arrow.mk (CommRingCat.ofHom (schemeScalarHom (Spec (CommRingCat.of S))
      (Spec.map (CommRingCat.ofHom ρ))))) p hp hR hΓ
  exact e₁ ≪≫ e₂ ≪≫ e₃.symm

variable {ι : Type} [Fintype ι] [DecidableEq ι] (U : ι → (Spec (CommRingCat.of S)).Opens)

/-- 元の環準同型のČech完全性と同じSpec.mapのタプルtotalの完全性の同値のČech版。
BS17 Theorem 4.1(i) の元の環の出口。分離的なスキームの準連接層では
アフィン被覆のČechとHは一致する（Stacks 30.2.6）が、この比較は形式化しない。 -/
theorem ringFrobeniusCech_exact_iff_spec_tuple_total_acyclic
    (hU : ∀ i, IsAffineOpen (U i)) (hcU : (⨆ i, U i) = ⊤) :
    SerrePositivity.Cech.AugmentedRingCechExact
      (frobeniusAugmentedRingCoefficients (Arrow.mk (CommRingCat.ofHom ρ)) p hp hR) ↔
      (HomologicalComplex₂.total (C := ModuleCat.{u} ℤ)
        (schemePerfectCechTupleDouble (Spec.map (CommRingCat.ofHom ρ)) U p hp hR)
          (.up ℕ)).Acyclic := by
  have hS : (p : S) = 0 := by
    simpa only [map_natCast, map_zero] using congrArg ρ hR
  exact (SerrePositivity.Cech.ringCechExact_iff_of_iso
    (specScalarFrobeniusAugmentedIso ρ p hp hR hS)).trans
      (affineScalarPerfectCech_exact_iff_tuple_total_acyclic (Spec (CommRingCat.of S))
        (Spec.map (CommRingCat.ofHom ρ)) p hp hR U hU hcU)

end SerrePositivity.AlgebraicGeometry
