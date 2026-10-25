module
public import SerrePositivity.DifferentialGraded.Module.ExtensionFreeNaturality
public import SerrePositivity.DifferentialGraded.Module.FreeSphereClosedCoefficientCycles
public import SerrePositivity.DifferentialGraded.Complexes.SphereTensorShiftNaturality
/-!
概要：自由 sphere 閉射への実 dg 関手作用の係数は、元の Hom 鎖写像の作用と一致する。
方針：自由評価の自然性と sphere tensor shift 比較の自然性を同じ cycle に適用する。
規約：全整数次数と元の実閉射を保つ。
使われ方：c′ のコード内閉射と、実延長で写した元の閉射の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (E : Type w) [DGCategory R E] [Small.{u} E] (F : DGFunctor R D E)

lemma dgFreeClosedArrowImage_sphere_coefficient (x y : D) (n m : ℤ)
    (g : freeSphere R D x n ⟶ freeSphere R D y m) :
    freeSphereClosedCoefficient R E (F.obj x) (F.obj y) n m
      (dgFreeClosedArrowImage R D E F x y (complexSphere R n) (complexSphere R m) g) =
      (F.map x y).f (n - m) (freeSphereClosedCoefficient R D x y n m g) := by
  have hz : (freeSphereHomEquiv R E (F.obj x) n (freeSphere R E (F.obj y) m)
      (dgFreeClosedArrowImage R D E F x y (complexSphere R n) (complexSphere R m) g)).val =
      (𝟙 (complexSphere R m) ⊗ₘ F.map x y).f n
        (freeSphereHomEquiv R D x n (freeSphere R D y m) g).val := by
    change (complexSphereHomEquiv R _ n
      (freeHomEquiv R E (F.obj x) (complexSphere R n) (freeSphere R E (F.obj y) m)
        (dgFreeClosedArrowImage R D E F x y (complexSphere R n) (complexSphere R m) g))).val = _
    rw [dgFreeClosedArrowImage, Equiv.apply_symm_apply]
    exact complexSphereHomEquiv_naturality_val R n _ _
  change (complexSphereTensorShiftIso R m (homObject R E (F.obj x) (F.obj y))).hom.f n _ = _
  rw [hz]
  exact congrArg (fun φ => φ.f n (freeSphereHomEquiv R D x n (freeSphere R D y m) g).val)
    (complexSphereTensorShiftIso_naturality R m (F.map x y))

end SerrePositivity.DifferentialGraded
