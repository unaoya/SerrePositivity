module

public import SerrePositivity.AlgebraicGeometry.FrobeniusArrowCocone

/-!
概要：忠実平坦なアフィン射の、実際の Frobenius 順極限の増大 Čech 完全性。
方針：同じ矢印の標準余極限同型を増大 conerve 関手で写し、B1 を移す。
規約：Čech 版の完全性を用い、元の環準同型と Frobenius の標準写像を保つ。
使われ方：同じアフィン conerve から G4・G5 の既存の Čech 判定へ渡す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u

/-- 忠実平坦なアフィン射の実際の Frobenius 順極限の Čech 完全性。
これは同じ矢印の filtered colimit の Čech 版を標準同型で移した形。 -/
theorem isCechExact_frobeniusDirectLimit_of_faithfullyFlat {A : CommRingCat.{u}}
    (B : Under A) [Module.FaithfullyFlat A B.right] (p : ℕ) (hp : p.Prime)
    (hA : (p : A) = 0) :
    SerrePositivity.Cech.IsCechExact (Arrow.mk (CommRingCat.ofHom
      (frobeniusDirectLimitMap p hp hA (underPrimeCast_eq_zero B p hA) B.hom.hom))) := by
  let e := frobeniusArrowSmallColimitIso (Arrow.mk B.hom) p hp hA
    (underPrimeCast_eq_zero B p hA)
  let G : Arrow CommRingCat.{u} ⥤ CosimplicialObject.Augmented CommRingCat.{u} :=
    CosimplicialObject.augmentedCechConerve
  exact (SerrePositivity.Cech.ringCechExact_iff_of_iso (G.mapIso e)).mpr
    (isCechExact_frobeniusArrowColimit_of_faithfullyFlat B p hp hA)

/-- 元の忠実平坦な射の任意の底変換に対する、実際の Frobenius 順極限の Čech 版。 -/
theorem isCechExact_frobeniusDirectLimit_baseChange_of_faithfullyFlat
    {A : CommRingCat.{u}} (B : Under A) [Module.FaithfullyFlat A B.right]
    (D : CommRingCat.{u}) [Algebra A D] (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0) :
    let hD : (p : D) = 0 := by rw [← map_natCast (algebraMap A D), hA, map_zero]
    SerrePositivity.Cech.IsCechExact (Arrow.mk (CommRingCat.ofHom
      (frobeniusDirectLimitMap p hp hD
        (underPrimeCast_eq_zero ((CommRingCat.tensorProd A D).obj B) p hD)
        ((CommRingCat.tensorProd A D).obj B).hom.hom))) := by
  have : Module.FaithfullyFlat D (D ⊗[A] B.right) := inferInstance
  have : Module.FaithfullyFlat D ((CommRingCat.tensorProd A D).obj B) :=
    faithfullyFlat_mkUnder (R := D) (S := D ⊗[A] B.right)
  exact isCechExact_frobeniusDirectLimit_of_faithfullyFlat
    ((CommRingCat.tensorProd A D).obj B) p hp
      (by rw [← map_natCast (algebraMap A D), hA, map_zero])

end SerrePositivity.AlgebraicGeometry
