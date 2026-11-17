module

public import SerrePositivity.AlgebraicGeometry.AffineGammaCechNaturality
public import SerrePositivity.AlgebraicGeometry.SchemeScalarMorphism

/-!
概要：同じアフィン nerve の Γ の比較を、元の基底環の実際のスカラーへ戻す。
方針：ΓSpec の標準同型と、同じ矢印の conerve の自然性を使う。
規約：元の基底環を Γ(Spec R) と黙って同一視せず、同じ増大の合成を保つ。
使われ方：実際の環の conerve と同じアフィンの係数の比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
universe u
variable {R : Type u} [CommRing R] (Y : Scheme.{u})
variable (f : Y ⟶ Spec (CommRingCat.of R))

set_option backward.isDefEq.respectTransparency false in
/-- 元のスカラーの矢印と Γ(f) の矢印の、元の ΓSpec 同型による標準同型。 -/
def schemeScalarArrowGammaIso :
    Arrow.mk (CommRingCat.ofHom (schemeScalarHom Y f)) ≅ Arrow.mk (Scheme.Γ.map f.op) :=
  Arrow.isoMk (Scheme.ΓSpecIso (CommRingCat.of R)).symm (Iso.refl _) (by
    change (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ Scheme.Γ.map f.op =
      CommRingCat.ofHom (schemeScalarHom Y f) ≫ 𝟙 _
    rw [Category.comp_id, Scheme.Γ_map_op]
    rfl)

variable [IsAffine Y]

/-- 元の基底環の実際のスカラーの conerve と、同じ幾何的 nerve の Γ の標準自然同型。 -/
def affineScalarCechConerveIso :
    (Arrow.mk (CommRingCat.ofHom (schemeScalarHom Y f))).cechConerve ≅
      (Arrow.mk f).cechNerve.rightOp ⋙ Scheme.Γ :=
  CosimplicialObject.cechConerve.mapIso (schemeScalarArrowGammaIso Y f) ≪≫
    affineGammaCechConerveIso f

set_option backward.isDefEq.respectTransparency false in
/-- 元の基底環からの同じ増大写像は、ΓSpec の逆と同じ幾何的増大の Γ の合成へ移る。 -/
theorem affineScalarCechConerveIso_augmentation (n : SimplexCategory) :
    (Arrow.mk (CommRingCat.ofHom (schemeScalarHom Y f))).augmentedCechConerve.hom.app n ≫
        (affineScalarCechConerveIso Y f).hom.app n =
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
        Scheme.Γ.map ((Arrow.mk f).augmentedCechNerve.hom.app (op n)).op := by
  let e := schemeScalarArrowGammaIso Y f
  have h := CosimplicialObject.Augmented.w_app
    (η := Arrow.mapAugmentedCechConerve e.hom) (n := n)
  change (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
      (Arrow.mk (Scheme.Γ.map f.op)).augmentedCechConerve.hom.app n =
    (Arrow.mk (CommRingCat.ofHom (schemeScalarHom Y f))).augmentedCechConerve.hom.app n ≫
      (Arrow.mapCechConerve e.hom).app n at h
  change (Arrow.mk (CommRingCat.ofHom (schemeScalarHom Y f))).augmentedCechConerve.hom.app n ≫
      ((Arrow.mapCechConerve e.hom).app n ≫ (affineGammaCechConerveIso f).hom.app n) = _
  rw [← Category.assoc, ← h, Category.assoc, affineGammaCechConerveIso_augmentation]

end SerrePositivity.AlgebraicGeometry
