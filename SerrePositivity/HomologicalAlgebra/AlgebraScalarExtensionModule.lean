module

public import SerrePositivity.HomologicalAlgebra.AlgebraRestrictionSingle
public import Mathlib.RingTheory.TensorProduct.Maps

/-! # 環代数の係数拡大と通常 tensor の係数を保つ比較 -/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
open CategoryTheory
open scoped TensorProduct ChangeOfRings
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]

/-- 係数拡大の内部の制限スカラーを正規化し、元の B 作用を保つ。 -/
def algebraScalarExtensionModuleIso (M : ModuleCat.{u} R) :
    (ModuleCat.extendScalars (algebraMap R B)).obj M ≅ ModuleCat.of B (B ⊗[R] M) := by
  let e := TensorProduct.congr (algebraSelfRestrictionIso R B).toLinearEquiv
    (LinearEquiv.refl R M)
  exact (show ((ModuleCat.extendScalars (algebraMap R B)).obj M) ≃ₗ[B] (B ⊗[R] M) from
    { e.toAddEquiv with
      map_smul' := by
        intro b x
        induction x using TensorProduct.inductionOn with
        | tmul c m => rfl
        | add x y hx hy =>
          change e (b • (x + y)) = b • e (x + y)
          rw [smul_add, e.map_add, e.map_add, smul_add]
          exact congrArg₂ (· + ·) hx hy
    }).toModuleIso

/-- 通常 tensor への正規化は各純 tensor の元を保つ。 -/
theorem algebraScalarExtensionModuleIso_tmul (M : ModuleCat.{u} R) (b : B) (m : M) :
    (algebraScalarExtensionModuleIso R B M).hom
      (b ⊗ₜ[R,algebraMap R B] m) = b ⊗ₜ[R] m := rfl

/-- 元の代数写像の係数拡大は、通常の環 tensor の標準写像と各元で一致する。 -/
theorem algebraScalarExtensionModuleIso_algMap_apply
    {S T : Type u} [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (f : S →ₐ[R] T)
    (x : (ModuleCat.extendScalars (algebraMap R B)).obj (ModuleCat.of R S)) :
    (algebraScalarExtensionModuleIso R B (ModuleCat.of R T)).hom
        ((ModuleCat.extendScalars (algebraMap R B)).map (ModuleCat.ofHom f.toLinearMap) x) =
      Algebra.TensorProduct.map (AlgHom.id R B) f
        ((algebraScalarExtensionModuleIso R B (ModuleCat.of R S)).hom x) := by
  induction x using TensorProduct.inductionOn with
  | tmul b s =>
    change (algebraScalarExtensionModuleIso R B (ModuleCat.of R T)).hom
      (b ⊗ₜ[R,algebraMap R B] f s) = _
    rw [algebraScalarExtensionModuleIso_tmul, algebraScalarExtensionModuleIso_tmul,
      Algebra.TensorProduct.map_tmul]
    rfl
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

end SerrePositivity
