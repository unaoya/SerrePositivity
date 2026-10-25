module
public import SerrePositivity.DifferentialGraded.Module.FreeSphereClosedCoefficient
public import SerrePositivity.DifferentialGraded.Complexes.CycleTransport
/-!
概要：任意シフト自由 sphere 間の閉射を、元の Hom の閉斉次係数と線形に同定する。
方針：自由 sphere の cycle 表示、tensor shift、shift cycle の符号除去を合成する。
規約：次数 n-m の元の係数を保持し、同じ閉射を逆構成で回収する。
使われ方：c′ のκ係数コードから自由行列閉射を持ち上げる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

def freeSphereClosedCoefficientCycleEquiv (x y : D) (n m : ℤ) :
    (freeSphere R D x n ⟶ freeSphere R D y m) ≃ₗ[R]
      complexCycles R (homObject R D x y) (n - m) :=
  (freeSphereClosedCycleLinearEquiv R D x n (freeSphere R D y m)).trans
    ((complexCycleIso R (complexSphereTensorShiftIso R m (homObject R D x y)) n).trans
      (complexShiftCycleIso R (homObject R D x y) (-m) n))

lemma freeSphereClosedCoefficientCycleEquiv_val (x y : D) (n m : ℤ)
    (f : freeSphere R D x n ⟶ freeSphere R D y m) :
    (freeSphereClosedCoefficientCycleEquiv R D x y n m f).val =
      freeSphereClosedCoefficient R D x y n m f := rfl

lemma freeSphereClosedCoefficient_closed (x y : D) (n m : ℤ)
    (f : freeSphere R D x n ⟶ freeSphere R D y m) :
    (homObject R D x y).d (n - m) (n - m + 1)
      (freeSphereClosedCoefficient R D x y n m f) = 0 :=
  (freeSphereClosedCoefficientCycleEquiv R D x y n m f).property

def freeSphereClosedCoefficientPreimage (x y : D) (n m : ℤ)
    (z : complexCycles R (homObject R D x y) (n - m)) :
    freeSphere R D x n ⟶ freeSphere R D y m :=
  (freeSphereClosedCoefficientCycleEquiv R D x y n m).symm z

lemma freeSphereClosedCoefficientPreimage_coefficient (x y : D) (n m : ℤ)
    (z : complexCycles R (homObject R D x y) (n - m)) :
    freeSphereClosedCoefficient R D x y n m
      (freeSphereClosedCoefficientPreimage R D x y n m z) = z.val :=
  congrArg Subtype.val ((freeSphereClosedCoefficientCycleEquiv R D x y n m).apply_symm_apply z)

end SerrePositivity.DifferentialGraded
