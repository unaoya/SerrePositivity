module
public import SerrePositivity.DifferentialGraded.Module.FreeSphereClosedLinear
public import SerrePositivity.DifferentialGraded.Complexes.SphereTensorShift
/-!
概要：二つの任意整数次数の自由 sphere 間閉射を、元の dg Hom の斉次係数で検出する。
方針：自由 sphere の cycle 評価と sphere tensor shift 同型を合成する。
規約：次数 n から次数 m の自由生成元への閉射は Hom の次数 n-m で読む。
使われ方：c′ の行有限自由閉射行列を元の dg 圏のκ係数へ戻す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

def freeSphereClosedCoefficient (x y : D) (n m : ℤ)
    (f : freeSphere R D x n ⟶ freeSphere R D y m) : GradedHom R x y (n - m) :=
  (complexSphereTensorShiftIso R m (homObject R D x y)).hom.f n
    (freeSphereHomEquiv R D x n (freeSphere R D y m) f).val

lemma freeSphereClosedCoefficient_injective (x y : D) (n m : ℤ) :
    Function.Injective (freeSphereClosedCoefficient R D x y n m) := by
  intro f g h
  apply (freeSphereHomEquiv R D x n (freeSphere R D y m)).injective
  apply Subtype.ext
  exact (ModuleCat.mono_iff_injective
    ((complexSphereTensorShiftIso R m (homObject R D x y)).hom.f n)).mp inferInstance h

def freeSphereClosedCoefficientLinearMap (x y : D) (n m : ℤ) :
    (freeSphere R D x n ⟶ freeSphere R D y m) →ₗ[R] GradedHom R x y (n - m) :=
  ((complexSphereTensorShiftIso R m (homObject R D x y)).hom.f n).hom.comp
    (((complexCycles R ((moduleEvaluation R D x).obj (freeSphere R D y m)) n).subtype).comp
      (freeSphereClosedCycleLinearEquiv R D x n (freeSphere R D y m)).toLinearMap)

end SerrePositivity.DifferentialGraded
