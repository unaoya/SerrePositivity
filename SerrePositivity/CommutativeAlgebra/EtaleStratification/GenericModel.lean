module

public import SerrePositivity.CommutativeAlgebra.UniversalHomeomorphism.Reduction
public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Tower

/-!
# 局所化後の部分代数の有限モデル

## 概要
局所化後の部分代数を、元の有限代数に逆像を取ってモデル化する。

## 方針
Noetherian 環上の有限加群の部分加群は有限。
逆像を再び局所化すると元の部分代数に戻ることは、局所化と部分加群の対応から従う。

## 規約
モデルは元の代数の部分代数とし、局所化への射も明示する。

## 使われ方
一般点で取り出した分離部分を、基底上の有限代数へ延ばす。
-/

@[expose] public section
noncomputable section
universe u

namespace SerrePositivity.CommutativeAlgebra

variable {R K A B : Type u} [CommRing R] [CommRing K] [CommRing A] [CommRing B]
  [Algebra R K] [Algebra R A] [Algebra R B] [Algebra K B] [IsScalarTower R K B]

/-- 局所化後の部分代数の逆像。 -/
def genericSubalgebraModel (f : A →ₐ[R] B) (C : Subalgebra K B) : Subalgebra R A :=
  (C.restrictScalars R).comap f

/-- 逆像から局所化後の部分代数への射。 -/
def genericSubalgebraModelMap (f : A →ₐ[R] B) (C : Subalgebra K B) :
    genericSubalgebraModel f C →ₐ[R] C :=
  (f.comp (genericSubalgebraModel f C).val).codRestrict (C.restrictScalars R)
    (fun x ↦ x.property)

/-- 有限代数の中に取ったモデルは noetherian 基底上で有限。 -/
theorem genericSubalgebraModel_finite [IsNoetherianRing R] [Module.Finite R A]
    (f : A →ₐ[R] B) (C : Subalgebra K B) : Module.Finite R (genericSubalgebraModel f C) :=
  Module.Finite.of_injective (genericSubalgebraModel f C).val.toLinearMap Subtype.val_injective

/-- 逆像のモデルを局所化すると元の部分代数に戻る。 -/
theorem genericSubalgebraModel_isLocalizedModule (M : Submonoid R) [IsLocalization M K]
    (f : A →ₐ[R] B) [IsLocalizedModule M f.toLinearMap] (C : Subalgebra K B) :
    IsLocalizedModule M (genericSubalgebraModelMap f C).toLinearMap := by
  let T := genericSubalgebraModel f C
  have he : T.toSubmodule.localized' K M f.toLinearMap = C.toSubmodule :=
    (Submodule.localized'gi K M f.toLinearMap).l_u_eq C.toSubmodule
  let e := (LinearEquiv.ofEq _ _ he).restrictScalars R
  have hmap : e.toLinearMap.comp (T.toSubmodule.toLocalized' K M f.toLinearMap) =
      (genericSubalgebraModelMap f C).toLinearMap := by
    ext x
    rfl
  rw [← hmap]
  exact IsLocalizedModule.of_linearEquiv M _ e

end SerrePositivity.CommutativeAlgebra
