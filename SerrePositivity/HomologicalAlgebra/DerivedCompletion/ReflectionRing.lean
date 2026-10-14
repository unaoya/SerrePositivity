module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleHomComplete

/-! # 完備加群の普遍的な元からの可換環構造

環の構造を仮定せず、指定された元での評価が完備加群への線形写像を一意に決めるなら、
その元を単位元とする可換環構造を復元する。
Koszul完備化のH⁰への適用には、この加群の普遍性を別途証明する必要がある。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
variable (R : Type u) [CommRing R]

/-- 指定された座標について完備な加群への線形写像を、単位候補での評価が一意に決める条件。
環構造や環準同型の普遍性を仮定するものではない。 -/
structure IsCompleteModuleReflection {k : ℕ} (a : Fin k → R)
    (B : ModuleCat.{u} R) (e : B) : Prop where
  isComplete : ∀ j, IsModuleComplete R (a j) B
  universal : ∀ (N : ModuleCat.{u} R), (∀ j, IsModuleComplete R (a j) N) →
    Function.Bijective (fun g : B →ₗ[R] N ↦ g e)

namespace IsCompleteModuleReflection
variable {R} {k : ℕ} {a : Fin k → R} {B : ModuleCat.{u} R} {e : B}
    (h : IsCompleteModuleReflection R a B e)
include h

/-- 自己準同型加群も各座標で導来完備。 -/
theorem end_isComplete (j : Fin k) :
    IsModuleComplete R (a j) (ModuleCat.of R (Module.End R B)) :=
  isModuleComplete_linearMap R (a j) B B (h.isComplete j)

/-- 単位候補を恒等自己準同型へ送る、唯一の線形写像。 -/
def leftMultiplication : B →ₗ[R] Module.End R B :=
  ((h.universal (ModuleCat.of R (Module.End R B)) h.end_isComplete).surjective LinearMap.id).choose

@[simp] theorem leftMultiplication_unit : h.leftMultiplication e = LinearMap.id :=
  ((h.universal (ModuleCat.of R (Module.End R B)) h.end_isComplete).surjective
    LinearMap.id).choose_spec

/-- 普遍性から定まる積。 -/
def mul (x y : B) : B := h.leftMultiplication x y

@[simp] theorem unit_mul (x : B) : h.mul e x = x := by
  simp [mul]

@[simp] theorem mul_unit (x : B) : h.mul x e = x := by
  have he : (LinearMap.applyₗ e).comp h.leftMultiplication = LinearMap.id :=
    (h.universal B h.isComplete).injective (by
      change h.mul e e = e
      exact h.unit_mul e)
  exact LinearMap.congr_fun he x

/-- 積は可換。二つの線形写像が単位候補で一致することを使う。 -/
theorem mul_comm (x y : B) : h.mul x y = h.mul y x := by
  have he : (LinearMap.applyₗ y).comp h.leftMultiplication = h.leftMultiplication y :=
    (h.universal B h.isComplete).injective (by
      change h.mul e y = h.mul y e
      rw [h.unit_mul, h.mul_unit])
  exact LinearMap.congr_fun he x

/-- 積は結合的。固定した二つの元に対する線形写像を単位候補で比較する。 -/
theorem mul_assoc (x y z : B) : h.mul (h.mul x y) z = h.mul x (h.mul y z) := by
  have he : ((LinearMap.applyₗ z).comp h.leftMultiplication).comp
      ((LinearMap.applyₗ y).comp h.leftMultiplication) =
      (LinearMap.applyₗ (h.mul y z)).comp h.leftMultiplication :=
    (h.universal B h.isComplete).injective (by
      change h.mul (h.mul e y) z = h.mul e (h.mul y z)
      rw [h.unit_mul, h.unit_mul])
  exact LinearMap.congr_fun he x

@[simp] theorem zero_mul (x : B) : h.mul 0 x = 0 := by simp [mul]
@[simp] theorem mul_zero (x : B) : h.mul x 0 = 0 := by simp [mul]

theorem mul_add (x y z : B) : h.mul x (y + z) = h.mul x y + h.mul x z :=
  (h.leftMultiplication x).map_add y z

theorem add_mul (x y z : B) : h.mul (x + y) z = h.mul x z + h.mul y z := by
  exact congrArg (fun g : Module.End R B ↦ g z) (h.leftMultiplication.map_add x y)

/-- 既存の加法群とR加群の上に、普遍的な元を単位とする可換環構造を構成する。 -/
@[instance_reducible] def commRing : CommRing B where
  toAddCommGroup := inferInstance
  one := e
  mul := h.mul
  mul_assoc := h.mul_assoc
  one_mul := h.unit_mul
  mul_one := h.mul_unit
  mul_zero := h.mul_zero
  zero_mul := h.zero_mul
  left_distrib := h.mul_add
  right_distrib := h.add_mul
  mul_comm := h.mul_comm

/-- 構成した積は、元のR加群のスカラー作用を保つ。 -/
theorem mul_scalar_unit (r : R) (x : B) : h.mul (r • e) x = r • x := by
  simp [mul, map_smul]

/-- 元の環から、復元した可換環への標準準同型。 -/
def unitRingHom : letI := h.commRing; R →+* B := by
  letI := h.commRing
  exact
    { toFun := fun r ↦ r • e
      map_one' := one_smul R e
      map_mul' := fun r s ↦ by
        change (r * s) • e = h.mul (r • e) (s • e)
        rw [h.mul_scalar_unit, mul_smul]
      map_zero' := zero_smul R e
      map_add' := fun r s ↦ add_smul r s e }

@[simp] theorem unitRingHom_apply (r : R) : h.unitRingHom r = r • e := rfl

/-- 復元した可換環を、元のスカラー作用と両立するR代数にする。 -/
@[instance_reducible] def algebra : letI := h.commRing; Algebra R B := by
  letI := h.commRing
  exact Algebra.ofModule
    (fun r x y ↦ by
      change h.mul (r • x) y = r • h.mul x y
      simp [mul, map_smul])
    (fun r x y ↦ by
      change h.mul x (r • y) = r • h.mul x y
      exact (h.leftMultiplication x).map_smul r y)

/-- 単位候補を1へ送る線形写像は、自動的に積を保つ。 -/
theorem linearMap_map_mul (T : Type u) [CommRing T] [Algebra R T]
    (hT : ∀ j, IsModuleComplete R (a j) (ModuleCat.of R T))
    (g : B →ₗ[R] T) (hg : g e = 1) (x y : B) : g (h.mul x y) = g x * g y := by
  have he : g.comp ((LinearMap.applyₗ y).comp h.leftMultiplication) =
      (LinearMap.mulRight R (g y)).comp g :=
    (h.universal (ModuleCat.of R T) hT).injective (by
      change g (h.mul e y) = g e * g y
      rw [h.unit_mul, hg, one_mul])
  exact LinearMap.congr_fun he x

/-- 完備R代数への標準延長。加群の普遍性から構成する。 -/
def liftAlgHom (T : Type u) [CommRing T] [Algebra R T]
    (hT : ∀ j, IsModuleComplete R (a j) (ModuleCat.of R T)) :
    letI := h.commRing; letI := h.algebra; B →ₐ[R] T := by
  letI := h.commRing
  letI := h.algebra
  let g : B →ₗ[R] T := ((h.universal (ModuleCat.of R T) hT).surjective 1).choose
  have hg : g e = 1 := ((h.universal (ModuleCat.of R T) hT).surjective 1).choose_spec
  exact
    { toFun := g
      map_one' := hg
      map_mul' := h.linearMap_map_mul T hT g hg
      map_zero' := g.map_zero
      map_add' := g.map_add
      commutes' := fun r ↦ by
        change g (r • e) = algebraMap R T r
        rw [map_smul, hg, Algebra.smul_def, mul_one] }

/-- 完備R代数への延長は一意。 -/
theorem liftAlgHom_unique (T : Type u) [CommRing T] [Algebra R T]
    (hT : ∀ j, IsModuleComplete R (a j) (ModuleCat.of R T)) :
    let _ := h.commRing; letI := h.algebra;
    ∀ g : B →ₐ[R] T, g = h.liftAlgHom T hT := by
  let _ := h.commRing
  let _ := h.algebra
  dsimp only
  intro g
  have he : g.toLinearMap = (h.liftAlgHom T hT).toLinearMap :=
    (h.universal (ModuleCat.of R T) hT).injective (by
      change g (1 : B) = (h.liftAlgHom T hT) (1 : B)
      rw [map_one, map_one])
  ext x
  exact LinearMap.congr_fun he x

/-- 加群の普遍性が、完備R代数への唯一の代数準同型を与える。 -/
theorem existsUnique_algHom (T : Type u) [CommRing T] [Algebra R T]
    (hT : ∀ j, IsModuleComplete R (a j) (ModuleCat.of R T)) :
    let _ := h.commRing; letI := h.algebra; ∃! _g : B →ₐ[R] T, True := by
  let _ := h.commRing
  let _ := h.algebra
  dsimp only
  exact ⟨h.liftAlgHom T hT, trivial, fun g _ ↦ h.liftAlgHom_unique T hT g⟩

/-- 標準準同型は、単位候補を1の像とする元の線形写像に一致する。 -/
theorem unitRingHom_eq_linearMap (u : R →ₗ[R] B) (hu : u 1 = e) (r : R) :
    h.unitRingHom r = u r := by
  rw [unitRingHom_apply, ← hu, ← map_smul, smul_eq_mul, mul_one]

/-- 復元した代数構造の標準写像と、構成した環準同型は一致する。 -/
@[simp] theorem algebraMap_eq_unitRingHom (r : R) :
    letI := h.commRing; letI := h.algebra; algebraMap R B r = h.unitRingHom r := rfl

end IsCompleteModuleReflection
end SerrePositivity.DerivedCompletion
