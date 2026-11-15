module

public import SerrePositivity.AlgebraicGeometry.CoefficientVCoverModelObjects

/-!
概要：係数に関して可換な実際の環の正方形を、有限型被覆模型として登録する。
方針：指定した k 構造写像から代数構造を作り、同じ環の射を代数写像にする。
規約：両環の実際の型と全ての構造射を保つ。
使われ方：B03・B04 の係数 pushout の後段を被覆模型の圏へ登録する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable {k R C : Type u} [CommRing k] [CommRing R] [CommRing C]
  [Algebra k R] [Algebra k C]

/-- 実際の k 構造写像を持つ有限型環の可換な正方形は、被覆模型を与える。 -/
def coefficientVCoverModelObjOfRingHoms (g : R →ₐ[k] C)
    {A D : Type u} [CommRing A] [CommRing D]
    (κA : k →+* A) (κD : k →+* D) (hA : κA.FiniteType) (hD : κD.FiniteType)
    (t : A →+* D) (a : A →+* R) (d : D →+* C)
    (hκt : t.comp κA = κD) (hκa : a.comp κA = algebraMap k R)
    (hκd : d.comp κD = algebraMap k C)
    (hsq : d.comp t = g.toRingHom.comp a) (ht : IsAffineVCover t) :
    CoefficientVCoverModelCategory k g := by
  letI : Algebra k A := κA.toAlgebra
  letI : Algebra k D := κD.toAlgebra
  letI : Algebra.FiniteType k A := hA
  letI : Algebra.FiniteType k D := hD
  let t' : A →ₐ[k] D := { __ := t, commutes' := fun x ↦ DFunLike.congr_fun hκt x }
  let a' : A →ₐ[k] R := { __ := a, commutes' := fun x ↦ DFunLike.congr_fun hκa x }
  let d' : D →ₐ[k] C := { __ := d, commutes' := fun x ↦ DFunLike.congr_fun hκd x }
  exact coefficientVCoverModelObj g t' a' d' (AlgHom.toRingHom_injective hsq) ht

end SerrePositivity.AlgebraicGeometry
