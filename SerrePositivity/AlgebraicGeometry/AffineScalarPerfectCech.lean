module

public import SerrePositivity.AlgebraicGeometry.AffineScalarCechConerve
public import SerrePositivity.AlgebraicGeometry.FrobeniusRingDiagram
public import SerrePositivity.AlgebraicGeometry.FrobeniusAugmentedRingCoefficients

/-!
概要：同じアフィン nerve の標準比較を実際の Frobenius 係数へ移す。
方針：元の環から標数を移し、既存の係数図式の自然な移送を使う。
規約：基底の増大は元の R の順極限からの同じ写像で照合する。
使われ方：忠実平坦な環の conerve と同じアフィンの係数の接続。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
universe u
variable {R : Type u} [CommRing R] (Y : Scheme.{u})
variable (f : Y ⟶ Spec (CommRingCat.of R)) [IsAffine Y]
variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0)

/-- 元の基底環の標数条件は同じ幾何的 nerve の実際の大域切断環へ移る。 -/
theorem affineScalarCech_primeCast (hR : (p : R) = 0) (n : SimplexCategory) :
    (p : ((Arrow.mk f).cechNerve.rightOp ⋙ Scheme.Γ).obj n) = 0 := by
  have h := congrArg ((affineScalarCechConerveIso Y f).hom.app n).hom
    (frobeniusConerve_primeCast
      (Arrow.mk (CommRingCat.ofHom (schemeScalarHom Y f))) p hR n)
  simpa only [map_natCast, map_zero] using h

/-- 同じアフィン nerve の標準自然同型を実際の Frobenius 係数図式へ移した自然同型。 -/
def affineScalarPerfectCechIso :
    frobeniusRingDiagram
        (Arrow.mk (CommRingCat.ofHom (schemeScalarHom Y f))).cechConerve p hp
        (frobeniusConerve_primeCast
          (Arrow.mk (CommRingCat.ofHom (schemeScalarHom Y f))) p hR) ≅
      frobeniusRingDiagram ((Arrow.mk f).cechNerve.rightOp ⋙ Scheme.Γ) p hp
        (affineScalarCech_primeCast Y f p hR) :=
  frobeniusRingDiagramIso p hp
    (frobeniusConerve_primeCast
      (Arrow.mk (CommRingCat.ofHom (schemeScalarHom Y f))) p hR)
    (affineScalarCechConerveIso Y f)

set_option backward.isDefEq.respectTransparency false in
/-- 同じ Frobenius 係数の標準比較は元の基底環からの増大写像を保つ。 -/
theorem affineScalarPerfectCechIso_augmentation (n : SimplexCategory) :
    ModuleCat.ofHom (frobeniusDirectLimitMap p hp hR
        (frobeniusConerve_primeCast
          (Arrow.mk (CommRingCat.ofHom (schemeScalarHom Y f))) p hR n)
        ((Arrow.mk (CommRingCat.ofHom (schemeScalarHom Y f))).augmentedCechConerve.hom.app n).hom
        |>.toAddMonoidHom.toIntLinearMap) ≫
        (affineScalarPerfectCechIso Y f p hp hR).hom.app n =
      ModuleCat.ofHom (frobeniusDirectLimitMap p hp hR
        (affineScalarCech_primeCast Y f p hR n)
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
          Scheme.Γ.map ((Arrow.mk f).augmentedCechNerve.hom.app (op n)).op).hom
        |>.toAddMonoidHom.toIntLinearMap) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨k, x, rfl⟩ := DirectLimit.exists_eq_mk (frobeniusDirectSystemMap R p hp hR) x
  change frobeniusDirectLimitOf
      (((Arrow.mk f).cechNerve.rightOp ⋙ Scheme.Γ).obj n) p hp
      (affineScalarCech_primeCast Y f p hR n) k
      (((affineScalarCechConerveIso Y f).hom.app n).hom
        (((Arrow.mk (CommRingCat.ofHom (schemeScalarHom Y f))).augmentedCechConerve.hom.app n).hom x)) =
    frobeniusDirectLimitOf
      (((Arrow.mk f).cechNerve.rightOp ⋙ Scheme.Γ).obj n) p hp
      (affineScalarCech_primeCast Y f p hR n) k
      (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
        Scheme.Γ.map ((Arrow.mk f).augmentedCechNerve.hom.app (op n)).op).hom x)
  exact congrArg (frobeniusDirectLimitOf _ p hp
    (affineScalarCech_primeCast Y f p hR n) k)
    (congrArg (fun k ↦ k.hom x) (affineScalarCechConerveIso_augmentation Y f n))

end SerrePositivity.AlgebraicGeometry
