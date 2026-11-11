module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.RingTheory.Finiteness.Basic

/-!
概要：係数制限した加群との R 線形同値から、元の係数環の作用と有限性を移す。
方針：Mathlib の AddEquiv.module と LinearEquiv.isScalarTower を使う。
規約：移した作用の次数付き性は、この補題では仮定も結論もしない。
使われ方：Rees の Čech コホモロジーとの比較に沿って、直和へ Rees 作用を移す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory

universe u
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
variable {X : Type u} [AddCommGroup X] [Module R X]
variable (Y : ModuleCat.{u} B)

local instance projectiveScalarTransportTargetModule :
    Module B ((ModuleCat.restrictScalars (algebraMap R B)).obj Y) :=
  inferInstanceAs (Module B Y)
local instance projectiveScalarTransportTargetTower :
    IsScalarTower R B ((ModuleCat.restrictScalars (algebraMap R B)).obj Y) :=
  IsScalarTower.of_compHom R B Y

variable (e : X ≃ₗ[R] (ModuleCat.restrictScalars (algebraMap R B)).obj Y)

/-- 係数制限した B 加群との R 線形同値に沿って、X に B の作用を移す。 -/
@[instance_reducible]
def projectiveScalarRestrictionTransportModule : Module B X :=
  e.toAddEquiv.module B

/-- 移した B 作用は、もとの R 作用と両立する。 -/
theorem projectiveScalarRestrictionTransport_scalarTower :
    letI := projectiveScalarRestrictionTransportModule Y e
    IsScalarTower R B X := by
  exact e.isScalarTower B

/-- 移した作用を持つ加群との B 線形同値。 -/
def projectiveScalarRestrictionTransportLinearEquiv :
    letI := projectiveScalarRestrictionTransportModule Y e
    X ≃ₗ[B] Y :=
  e.toAddEquiv.linearEquiv B

/-- 作用を移す前後で、比較同値の元への値は変わらない。 -/
theorem projectiveScalarRestrictionTransportLinearEquiv_apply (x : X) :
    projectiveScalarRestrictionTransportLinearEquiv Y e x = e x := rfl

/-- B 上有限な加群との比較に沿って移した作用について、X も B 上有限となる。 -/
theorem projectiveScalarRestrictionTransport_finite [Module.Finite B Y] :
    letI := projectiveScalarRestrictionTransportModule Y e
    Module.Finite B X := by
  letI := projectiveScalarRestrictionTransportModule Y e
  let a := projectiveScalarRestrictionTransportLinearEquiv Y e
  exact Module.Finite.of_surjective a.symm.toLinearMap a.symm.surjective

section Iso
variable {Z : ModuleCat.{u} R}

/-- 係数制限した加群からの同型を用いて、終域の R 加群へ B 作用を移す。 -/
@[instance_reducible]
def projectiveScalarRestrictionTransportModuleOfIso
    (a : (ModuleCat.restrictScalars (algebraMap R B)).obj Y ≅ Z) : Module B Z :=
  projectiveScalarRestrictionTransportModule Y a.symm.toLinearEquiv

/-- 同型を用いて移した B 作用は、終域の既存の R 作用と両立する。 -/
theorem projectiveScalarRestrictionTransportOfIso_scalarTower
    (a : (ModuleCat.restrictScalars (algebraMap R B)).obj Y ≅ Z) :
    letI := projectiveScalarRestrictionTransportModuleOfIso Y a
    IsScalarTower R B Z :=
  projectiveScalarRestrictionTransport_scalarTower Y a.symm.toLinearEquiv

/-- 同型を用いて移した作用に関する、B 線形な比較。 -/
def projectiveScalarRestrictionTransportLinearEquivOfIso
    (a : (ModuleCat.restrictScalars (algebraMap R B)).obj Y ≅ Z) :
    letI := projectiveScalarRestrictionTransportModuleOfIso Y a
    Z ≃ₗ[B] Y :=
  projectiveScalarRestrictionTransportLinearEquiv Y a.symm.toLinearEquiv

/-- 係数制限した有限 B 加群との同型から、移した作用に関する有限性を得る。 -/
theorem projectiveScalarRestrictionTransportOfIso_finite [Module.Finite B Y]
    (a : (ModuleCat.restrictScalars (algebraMap R B)).obj Y ≅ Z) :
    letI := projectiveScalarRestrictionTransportModuleOfIso Y a
    Module.Finite B Z :=
  projectiveScalarRestrictionTransport_finite Y a.symm.toLinearEquiv

end Iso
end SerrePositivity.AlgebraicGeometry
