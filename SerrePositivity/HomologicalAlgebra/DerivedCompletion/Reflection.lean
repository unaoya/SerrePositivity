module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleComplete.Closure
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Koszul.Complete

/-! # 完備加群への反映と環構造の復元

## 概要

指定した元での評価が完備加群への線形写像を一意に決める（`IsCompleteModuleReflection`）なら、その元を単位元とする可換環の構造が復元できる（`commRing`・`unitRingHom`）。一つの座標の完備化を列の商 `PrincipalReflectionModule`（右シフト − f 倍の像で割る）で表し、漸化式の一意な解から完備加群への写像を作り、対角の有限和で商の完備性を示す。標準元を保つ線形同型で反映を移す。

## 方針

環の構造を仮定せず、加群の普遍性だけから乗法を作る。

## 規約

Koszul の完備化の H⁰ との同定は `Principal/KoszulModel`。一般的な名前 `sequenceShiftRight`・`diagonalSequence` などは将来 private か名前空間へ（refactor-plan §3.5.4）。旧 `ReflectionRing`・`ReflectionTransport`・`PrincipalReflectionPresentation`・`PrincipalReflectionComplete`。

## 使われ方

`Principal/*`・`Pair/*`、`ModuleComplete/Presentation`。
-/

@[expose] public noncomputable section

universe u

section PrincipalReflectionPresentationPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
variable (R : Type u) [CommRing R]

/-- 列を一つ右へずらし、最初に零を入れる。 -/
def sequenceShiftRight : (ℕ → R) →ₗ[R] (ℕ → R) where
  toFun x n := Nat.casesOn n 0 x
  map_add' x y := by funext n; cases n <;> simp
  map_smul' r x := by funext n; cases n <;> simp

@[simp] theorem sequenceShiftRight_zero (x : ℕ → R) : sequenceShiftRight R x 0 = 0 := rfl
@[simp] theorem sequenceShiftRight_succ (x : ℕ → R) (n : ℕ) :
    sequenceShiftRight R x (n + 1) = x n := rfl

/-- 最初の項を除いた列。 -/
def sequenceTail : (ℕ → R) →ₗ[R] (ℕ → R) where
  toFun x n := x (n + 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- 最初の項だけを指定した列。 -/
def sequenceHead : R →ₗ[R] (ℕ → R) where
  toFun r n := Nat.casesOn n r (fun _ ↦ 0)
  map_add' r s := by funext n; cases n <;> simp
  map_smul' r s := by funext n; cases n <;> simp

/-- 列による主元完備化の関係写像。 -/
def principalReflectionRelation (f : R) : (ℕ → R) →ₗ[R] (ℕ → R) :=
  sequenceShiftRight R - f • LinearMap.id

/-- 主元完備化の加群の候補表示。まだKoszulのH⁰とは同一視しない。 -/
abbrev PrincipalReflectionModule (f : R) :=
  (ℕ → R) ⧸ (principalReflectionRelation R f).range

/-- 候補表示への商写像。 -/
def principalReflectionMk (f : R) : (ℕ → R) →ₗ[R] PrincipalReflectionModule R f :=
  (principalReflectionRelation R f).range.mkQ

/-- 1に対応する標準元。 -/
def principalReflectionUnit (f : R) : PrincipalReflectionModule R f :=
  principalReflectionMk R f (sequenceHead R 1)

/-- 商では、右シフトがf倍に等しくなる。 -/
theorem principalReflectionMk_shift (f : R) (x : ℕ → R) :
    principalReflectionMk R f (sequenceShiftRight R x) =
      f • principalReflectionMk R f x := by
  apply sub_eq_zero.mp
  rw [← map_smul, ← map_sub]
  exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨x, rfl⟩

/-- 商の各列は、最初の係数とf倍した残りの列に分かれる。 -/
theorem principalReflectionMk_decomposition (f : R) (x : ℕ → R) :
    principalReflectionMk R f x =
      x 0 • principalReflectionUnit R f + f • principalReflectionMk R f (sequenceTail R x) := by
  have hx : x = x 0 • sequenceHead R 1 + sequenceShiftRight R (sequenceTail R x) := by
    funext n
    cases n <;> simp [sequenceHead, sequenceTail, smul_eq_mul]
  conv_lhs => rw [hx]
  rw [map_add, map_smul, principalReflectionMk_shift]
  rfl

/-- 完備性判定の列作用を線形同型として使う。 -/
def adicRecurrenceEquiv (f : R) (N : ModuleCat.{u} R) (hN : IsModuleComplete R f N) :
    (ℕ → N) ≃ₗ[R] (ℕ → N) :=
  LinearEquiv.ofBijective (adicRecurrenceMap f)
    ((isModuleComplete_iff_recurrence_bijective R f N).mp hN)

/-- 列の係数を、指定した元のスカラー倍の列へ送る。 -/
def sequenceScalarMap (N : ModuleCat.{u} R) (t : N) : (ℕ → R) →ₗ[R] (ℕ → N) where
  toFun x n := x n • t
  map_add' x y := by funext n; exact add_smul _ _ _
  map_smul' r x := by funext n; exact mul_smul _ _ _

/-- 列の関係を、漸化式の零始値の列へ移す。 -/
theorem sequenceScalarMap_relation (f : R) (N : ModuleCat.{u} R) (t : N) (x : ℕ → R) :
    sequenceScalarMap R N t (principalReflectionRelation R f x) =
      adicRecurrenceMap f (fun n ↦ Nat.casesOn n 0 (fun k ↦ x k • t)) := by
  funext n
  cases n with
  | zero => simp [sequenceScalarMap, principalReflectionRelation, adicRecurrenceMap, smul_smul]
  | succ n => simp [sequenceScalarMap, principalReflectionRelation, adicRecurrenceMap,
      sub_smul, smul_smul]

/-- 指定した元への延長を、漸化式の一意解の最初の項で構成する。 -/
def principalReflectionLift (f : R) (N : ModuleCat.{u} R) (hN : IsModuleComplete R f N)
    (t : N) : PrincipalReflectionModule R f →ₗ[R] N :=
  (principalReflectionRelation R f).range.liftQ
    ((LinearMap.proj 0).comp ((adicRecurrenceEquiv R f N hN).symm.toLinearMap.comp
      (sequenceScalarMap R N t))) (by
        rintro y ⟨x, rfl⟩
        change (adicRecurrenceEquiv R f N hN).symm
          (sequenceScalarMap R N t (principalReflectionRelation R f x)) 0 = 0
        rw [sequenceScalarMap_relation]
        exact congrFun ((adicRecurrenceEquiv R f N hN).symm_apply_apply _) 0)

@[simp] theorem principalReflectionLift_mk (f : R) (N : ModuleCat.{u} R)
    (hN : IsModuleComplete R f N) (t : N) (x : ℕ → R) :
    principalReflectionLift R f N hN t (principalReflectionMk R f x) =
      (adicRecurrenceEquiv R f N hN).symm (sequenceScalarMap R N t x) 0 := rfl

/-- 延長は標準元を指定された元へ送る。 -/
@[simp] theorem principalReflectionLift_unit (f : R) (N : ModuleCat.{u} R)
    (hN : IsModuleComplete R f N) (t : N) :
    principalReflectionLift R f N hN t (principalReflectionUnit R f) = t := by
  rw [principalReflectionUnit, principalReflectionLift_mk]
  let x : ℕ → N := fun n ↦ Nat.casesOn n t (fun _ ↦ 0)
  have hx : adicRecurrenceEquiv R f N hN x = sequenceScalarMap R N t (sequenceHead R 1) := by
    funext n
    cases n <;> simp [adicRecurrenceEquiv, adicRecurrenceMap, x, sequenceScalarMap, sequenceHead]
  rw [← hx, LinearEquiv.symm_apply_apply]
  rfl

/-- 標準元の像が零なら、完備加群への線形写像は零。 -/
theorem principalReflectionHom_eq_zero (f : R) (N : ModuleCat.{u} R)
    (hN : IsModuleComplete R f N) (g : PrincipalReflectionModule R f →ₗ[R] N)
    (hg : g (principalReflectionUnit R f) = 0) : g = 0 := by
  apply LinearMap.ext
  intro z
  obtain ⟨x, rfl⟩ := (principalReflectionRelation R f).range.mkQ_surjective z
  let y : ℕ → N := fun n ↦ g (principalReflectionMk R f (fun k ↦ x (n + k)))
  have hy : adicRecurrenceMap f y = 0 := by
    funext n
    have hd := congrArg g (principalReflectionMk_decomposition R f (fun k ↦ x (n + k)))
    have ht : sequenceTail R (fun k ↦ x (n + k)) = (fun k ↦ x ((n + 1) + k)) := by
      funext k
      change x (n + (k + 1)) = x ((n + 1) + k)
      congr 1
      omega
    rw [ht, map_add, map_smul, map_smul, hg, smul_zero, zero_add] at hd
    change y n - f • y (n + 1) = 0
    exact sub_eq_zero.mpr hd
  have he := ((isModuleComplete_iff_recurrence_bijective R f N).mp hN).injective
    (hy.trans (map_zero _).symm)
  change g (principalReflectionMk R f x) = 0
  simpa [y] using congrFun he 0

/-- この具体的な商から完備加群への線形写像は、標準元での評価と全単射に対応する。 -/
theorem principalReflection_evaluation_bijective (f : R) (N : ModuleCat.{u} R)
    (hN : IsModuleComplete R f N) :
    Function.Bijective (fun g : PrincipalReflectionModule R f →ₗ[R] N ↦
      g (principalReflectionUnit R f)) := by
  constructor
  · intro g h he
    apply sub_eq_zero.mp
    exact principalReflectionHom_eq_zero R f N hN (g - h) (sub_eq_zero.mpr he)
  · intro t
    exact ⟨principalReflectionLift R f N hN t, principalReflectionLift_unit R f N hN t⟩

end SerrePositivity.DerivedCompletion

end PrincipalReflectionPresentationPart

section ReflectionRingPart

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
  Function.surjInv (h.universal (ModuleCat.of R (Module.End R B)) h.end_isComplete).surjective
    LinearMap.id

@[simp] theorem leftMultiplication_unit : h.leftMultiplication e = LinearMap.id :=
  Function.surjInv_eq (h.universal (ModuleCat.of R (Module.End R B)) h.end_isComplete).surjective
    LinearMap.id

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
  let g : B →ₗ[R] T := Function.surjInv (h.universal (ModuleCat.of R T) hT).surjective 1
  have hg : g e = 1 := Function.surjInv_eq (h.universal (ModuleCat.of R T) hT).surjective 1
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

end ReflectionRingPart

section PrincipalReflectionCompletePart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
variable (R : Type u) [CommRing R]

/-- 二重列の対角線に沿った有限和。 -/
def diagonalSequence (x : ℕ → ℕ → R) : ℕ → R
  | 0 => x 0 0
  | n + 1 => x 0 (n + 1) + diagonalSequence (fun i ↦ x (i + 1)) n

/-- 対角和の線形写像。 -/
def sequenceDiagonal : (ℕ → ℕ → R) →ₗ[R] (ℕ → R) where
  toFun := diagonalSequence R
  map_add' x y := by
    funext n
    induction n generalizing x y with
    | zero => rfl
    | succ n ih =>
      change (x 0 (n + 1) + y 0 (n + 1)) +
        diagonalSequence R ((fun i ↦ x (i + 1)) + (fun i ↦ y (i + 1))) n = _
      rw [ih]
      change _ = (x 0 (n + 1) + diagonalSequence R (fun i ↦ x (i + 1)) n) +
        (y 0 (n + 1) + diagonalSequence R (fun i ↦ y (i + 1)) n)
      simp only [Pi.add_apply]
      abel
  map_smul' r x := by
    funext n
    induction n generalizing x with
    | zero => rfl
    | succ n ih =>
      change r • x 0 (n + 1) + diagonalSequence R (r • (fun i ↦ x (i + 1))) n = _
      rw [ih]
      exact (smul_add r _ _).symm

/-- 各行の右シフトは、対角和全体の右シフトになる。 -/
theorem sequenceDiagonal_shift (x : ℕ → ℕ → R) :
    sequenceDiagonal R (fun i ↦ sequenceShiftRight R (x i)) =
      sequenceShiftRight R (sequenceDiagonal R x) := by
  funext n
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    change x 0 n + sequenceDiagonal R (fun i ↦ sequenceShiftRight R (x (i + 1))) n =
      sequenceDiagonal R x n
    rw [ih (fun i ↦ x (i + 1))]
    cases n <;> simp [sequenceDiagonal, diagonalSequence]

/-- 各行の関係式の対角和も、同じ関係式の像に入る。 -/
theorem sequenceDiagonal_relation (f : R) (x : ℕ → ℕ → R) :
    sequenceDiagonal R (fun i ↦ principalReflectionRelation R f (x i)) =
      principalReflectionRelation R f (sequenceDiagonal R x) := by
  change sequenceDiagonal R ((fun i ↦ sequenceShiftRight R (x i)) - f • x) = _
  rw [map_sub, map_smul, sequenceDiagonal_shift]
  rfl

/-- 各行の商での値が同じなら、対角和の商での値も同じ。 -/
theorem principalReflection_diagonal_congr (f : R) (x y : ℕ → ℕ → R)
    (h : ∀ n, principalReflectionMk R f (x n) = principalReflectionMk R f (y n)) :
    principalReflectionMk R f (sequenceDiagonal R x) =
      principalReflectionMk R f (sequenceDiagonal R y) := by
  have hz : ∀ n, ∃ z, principalReflectionRelation R f z = x n - y n := by
    intro n
    change x n - y n ∈ (principalReflectionRelation R f).range
    apply (Submodule.Quotient.mk_eq_zero _).mp
    change principalReflectionMk R f (x n - y n) = 0
    rw [map_sub, h n, sub_self]
  choose z hz using hz
  apply sub_eq_zero.mp
  rw [← map_sub, ← map_sub]
  have he : x - y = fun n ↦ principalReflectionRelation R f (z n) := by
    funext n
    exact (hz n).symm
  rw [he, sequenceDiagonal_relation]
  exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨sequenceDiagonal R z, rfl⟩

/-- 商の元の列を、代表元の対角和で足す。 -/
def principalReflectionSum (f : R) (x : ℕ → PrincipalReflectionModule R f) :
    PrincipalReflectionModule R f :=
  principalReflectionMk R f (sequenceDiagonal R
    (fun n ↦ Function.surjInv (principalReflectionRelation R f).range.mkQ_surjective (x n)))

/-- 任意の代表列で対角和を計算できる。 -/
theorem principalReflectionSum_mk (f : R) (x : ℕ → ℕ → R) :
    principalReflectionSum R f (fun n ↦ principalReflectionMk R f (x n)) =
      principalReflectionMk R f (sequenceDiagonal R x) := by
  apply principalReflection_diagonal_congr
  intro n
  exact Function.surjInv_eq (principalReflectionRelation R f).range.mkQ_surjective
    (principalReflectionMk R f (x n))

/-- 対角和は、最初の行と残りの行の右シフトに分かれる。 -/
theorem sequenceDiagonal_decomposition (x : ℕ → ℕ → R) :
    sequenceDiagonal R x = x 0 + sequenceShiftRight R
      (sequenceDiagonal R (fun n ↦ x (n + 1))) := by
  funext n
  cases n <;> simp [sequenceDiagonal, diagonalSequence]

/-- 漸化式の逆候補。 -/
def principalReflectionRecurrenceInverse (f : R) (x : ℕ → PrincipalReflectionModule R f) :
    ℕ → PrincipalReflectionModule R f :=
  fun n ↦ principalReflectionSum R f (fun i ↦ x (n + i))

/-- 逆候補は漸化式の右逆。 -/
theorem principalReflectionRecurrence_rightInverse (f : R) :
    Function.RightInverse (principalReflectionRecurrenceInverse R f) (adicRecurrenceMap f) := by
  intro x
  choose z hz using fun n ↦ (principalReflectionRelation R f).range.mkQ_surjective (x n)
  funext n
  have he : x = fun n ↦ principalReflectionMk R f (z n) := by
    funext n
    exact (hz n).symm
  rw [he]
  change principalReflectionSum R f (fun i ↦ principalReflectionMk R f (z (n + i))) -
    f • principalReflectionSum R f (fun i ↦ principalReflectionMk R f (z ((n + 1) + i))) =
    principalReflectionMk R f (z n)
  rw [principalReflectionSum_mk, principalReflectionSum_mk]
  have hd := congrArg (principalReflectionMk R f)
    (sequenceDiagonal_decomposition R (fun i ↦ z (n + i)))
  simp only [map_add, principalReflectionMk_shift] at hd
  have ht : (fun i ↦ z (n + (i + 1))) = (fun i ↦ z ((n + 1) + i)) := by
    funext i
    congr 1
    omega
  rw [ht] at hd
  exact sub_eq_iff_eq_add.mpr (by simpa [add_comm] using hd)

/-- 逆候補は漸化式の左逆。 -/
theorem principalReflectionRecurrence_leftInverse (f : R) :
    Function.LeftInverse (principalReflectionRecurrenceInverse R f) (adicRecurrenceMap f) := by
  intro x
  choose z hz using fun n ↦ (principalReflectionRelation R f).range.mkQ_surjective (x n)
  funext n
  have he : x = fun n ↦ principalReflectionMk R f (z n) := by
    funext n
    exact (hz n).symm
  rw [he]
  change principalReflectionSum R f (fun i ↦ principalReflectionMk R f (z (n + i)) -
    f • principalReflectionMk R f (z (n + i + 1))) = principalReflectionMk R f (z n)
  have hs : (fun i ↦ principalReflectionMk R f (z (n + i)) -
      f • principalReflectionMk R f (z (n + i + 1))) =
      fun i ↦ principalReflectionMk R f (z (n + i) - f • z (n + i + 1)) := by
    funext i
    rw [map_sub, map_smul]
  rw [hs, principalReflectionSum_mk]
  change principalReflectionMk R f (sequenceDiagonal R
    ((fun i ↦ z (n + i)) - f • (fun i ↦ z (n + i + 1)))) = _
  rw [map_sub, map_smul, map_sub, map_smul]
  have hd := congrArg (principalReflectionMk R f)
    (sequenceDiagonal_decomposition R (fun i ↦ z (n + i)))
  simp only [map_add, principalReflectionMk_shift] at hd
  exact sub_eq_iff_eq_add.mpr (by simpa [add_comm, Nat.add_assoc] using hd)

/-- 列による商表示そのものが導来完備。Noether性やtorsion条件は要らない。 -/
theorem principalReflection_isModuleComplete (f : R) :
    IsModuleComplete R f (ModuleCat.of R (PrincipalReflectionModule R f)) := by
  apply (isModuleComplete_iff_recurrence_bijective R f _).mpr
  exact ⟨(principalReflectionRecurrence_leftInverse R f).injective,
    (principalReflectionRecurrence_rightInverse R f).surjective⟩

/-- この商表示は、主元に関する完備加群への反映の条件を実際に満たす。 -/
theorem principalReflection_isCompleteModuleReflection (f : R) :
    IsCompleteModuleReflection R (fun _ : Fin 1 ↦ f)
      (ModuleCat.of R (PrincipalReflectionModule R f)) (principalReflectionUnit R f) where
  isComplete _ := principalReflection_isModuleComplete R f
  universal N hN := principalReflection_evaluation_bijective R f N (hN 0)

end SerrePositivity.DerivedCompletion

end PrincipalReflectionCompletePart

section ReflectionTransportPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R]

/-- 線形同型は加群の導来完備性を保つ。 -/
theorem isModuleComplete_of_linearEquiv (f : R) (M N : ModuleCat.{u} R)
    (e : M ≃ₗ[R] N) (hM : IsModuleComplete R f M) : IsModuleComplete R f N :=
  isComplete_of_iso R f ((moduleObjectFunctor R).mapIso e.toModuleIso) hM

/-- 標準元を保つ線形同型は、完備性と加群の一意延長をまとめて移す。 -/
theorem IsCompleteModuleReflection.of_linearEquiv {k : ℕ} {a : Fin k → R}
    {B D : ModuleCat.{u} R} {b : B} {d : D}
    (h : IsCompleteModuleReflection R a B b) (e : B ≃ₗ[R] D) (he : e b = d) :
    IsCompleteModuleReflection R a D d where
  isComplete j := isModuleComplete_of_linearEquiv R (a j) B D e (h.isComplete j)
  universal N hN := by
    constructor
    · intro g q hg
      have hcomp : g.comp e.toLinearMap = q.comp e.toLinearMap :=
        (h.universal N hN).injective (by change g (e b) = q (e b); rw [he]; exact hg)
      ext x
      have hx := LinearMap.congr_fun hcomp (e.symm x)
      change g (e (e.symm x)) = q (e (e.symm x)) at hx
      simpa only [LinearEquiv.apply_symm_apply] using hx
    · intro t
      obtain ⟨g, hg⟩ := (h.universal N hN).surjective t
      refine ⟨g.comp e.symm.toLinearMap, ?_⟩
      change g (e.symm d) = t
      rw [← he, LinearEquiv.symm_apply_apply]
      exact hg

end SerrePositivity.DerivedCompletion

end ReflectionTransportPart
