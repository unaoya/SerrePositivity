module

public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # 加群の可算逆系の差分写像

## 概要

直積の上の「恒等 − 遷移」の差分写像とその核としての両立する列（`moduleTowerLimit`）を作り、遷移が全射なら差分も全射であることを示す。両立する段ごとの同型が差分の核と余核（lim と lim¹）を保つことを与える。

## 方針

ホモトピー逆極限の計算に使う代数的な部分だけを置く。

## 規約

旧 `ModuleTower`・`ModuleTowerEquiv`。

## 使われ方

Tower/Milnor、`Koszul/Milnor`。
-/

@[expose] public noncomputable section

universe u v

section ModuleTowerPart

namespace SerrePositivity.DerivedCompletion
variable (R : Type u) [CommRing R] (M : ℕ → Type v)
    [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
    (t : ∀ n, M (n + 1) →ₗ[R] M n)

/-- 逆系の直積上の差分写像。 -/
def moduleTowerDifference : (∀ n, M n) →ₗ[R] (∀ n, M n) where
  toFun x n := x n - t n (x (n + 1))
  map_add' x y := by ext n; simp only [Pi.add_apply, map_add]; exact add_sub_add_comm _ _ _ _
  map_smul' r x := by ext n; simp only [Pi.smul_apply, map_smul, smul_sub, RingHom.id_apply]

@[simp] theorem moduleTowerDifference_apply (x : ∀ n, M n) (n : ℕ) :
    moduleTowerDifference R M t x n = x n - t n (x (n + 1)) := rfl

/-- 両立する列の加群。 -/
def moduleTowerLimit : Submodule R (∀ n, M n) := (moduleTowerDifference R M t).ker

/-- 差分写像の核に入ることは、隣接段の両立性と同値。 -/
theorem mem_moduleTowerLimit_iff (x : ∀ n, M n) :
    x ∈ moduleTowerLimit R M t ↔ ∀ n, t n (x (n + 1)) = x n := by
  change moduleTowerDifference R M t x = 0 ↔ _
  simp only [funext_iff, moduleTowerDifference_apply, Pi.zero_apply, sub_eq_zero]
  exact forall_congr' (fun n ↦ eq_comm)

/-- 遷移写像が全射なら、直積上の差分写像も全射。 -/
theorem moduleTowerDifference_surjective (ht : ∀ n, Function.Surjective (t n)) :
    Function.Surjective (moduleTowerDifference R M t) := by
  intro y
  let x : ∀ n, M n := fun n ↦ Nat.rec (motive := fun k ↦ M k) 0
    (fun k a ↦ Classical.choose (ht k (a - y k))) n
  refine ⟨x, ?_⟩
  ext n
  have hx : t n (x (n + 1)) = x n - y n := by
    exact Classical.choose_spec (ht n (x n - y n))
  rw [moduleTowerDifference_apply, hx, sub_sub_cancel]

/-- 両立する列の第n成分への射影。 -/
def moduleTowerProjection (n : ℕ) : moduleTowerLimit R M t →ₗ[R] M n :=
  (LinearMap.proj n).comp (moduleTowerLimit R M t).subtype

/-- 射影と遷移写像は可換。 -/
theorem moduleTowerProjection_compatible (n : ℕ) :
    (t n).comp (moduleTowerProjection R M t (n + 1)) = moduleTowerProjection R M t n := by
  ext x
  exact (mem_moduleTowerLimit_iff R M t x.val).mp x.property n

/-- 両立する写像の族から逆極限への線形写像を構成する。 -/
def moduleTowerLimitLift (N : Type*) [AddCommGroup N] [Module R N]
    (g : ∀ n, N →ₗ[R] M n) (hg : ∀ n, (t n).comp (g (n + 1)) = g n) :
    N →ₗ[R] moduleTowerLimit R M t where
  toFun x := ⟨fun n ↦ g n x, (mem_moduleTowerLimit_iff R M t _).mpr
    (fun n ↦ LinearMap.congr_fun (hg n) x)⟩
  map_add' x y := by apply Subtype.ext; ext n; exact (g n).map_add x y
  map_smul' r x := by apply Subtype.ext; ext n; exact (g n).map_smul r x

@[simp] theorem moduleTowerProjection_comp_lift (N : Type*) [AddCommGroup N] [Module R N]
    (g : ∀ n, N →ₗ[R] M n) (hg : ∀ n, (t n).comp (g (n + 1)) = g n) (n : ℕ) :
    (moduleTowerProjection R M t n).comp (moduleTowerLimitLift R M t N g hg) = g n := rfl

/-- すべての射影を指定すれば、逆極限への写像は一意。 -/
theorem moduleTowerLimitLift_unique (N : Type*) [AddCommGroup N] [Module R N]
    (g : ∀ n, N →ₗ[R] M n) (hg : ∀ n, (t n).comp (g (n + 1)) = g n)
    (f : N →ₗ[R] moduleTowerLimit R M t)
    (hf : ∀ n, (moduleTowerProjection R M t n).comp f = g n) :
    f = moduleTowerLimitLift R M t N g hg := by
  ext x n
  exact LinearMap.congr_fun (hf n) x

end SerrePositivity.DerivedCompletion

end ModuleTowerPart

section ModuleTowerEquivPart

namespace SerrePositivity.DerivedCompletion
variable (R : Type u) [CommRing R] {M N : ℕ → Type v}
  [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  [∀ n, AddCommGroup (N n)] [∀ n, Module R (N n)]
  (t : ∀ n, M (n + 1) →ₗ[R] M n) (s : ∀ n, N (n + 1) →ₗ[R] N n)
  (e : ∀ n, M n ≃ₗ[R] N n)
  (he : ∀ n x, e n (t n x) = s n (e (n + 1) x))

include he in
lemma moduleTowerDifference_equiv (x : ∀ n, M n) :
    (LinearEquiv.piCongrRight e) (moduleTowerDifference R M t x) =
      moduleTowerDifference R N s ((LinearEquiv.piCongrRight e) x) := by
  ext n
  simp only [LinearEquiv.piCongrRight_apply, moduleTowerDifference_apply, map_sub, he]

/-- The map of inverse limits keeps every original component. -/
def moduleTowerLimitEquiv : moduleTowerLimit R M t ≃ₗ[R] moduleTowerLimit R N s where
  toFun x := ⟨(LinearEquiv.piCongrRight e) x.val, by
    change moduleTowerDifference R N s ((LinearEquiv.piCongrRight e) x.val) = 0
    rw [← moduleTowerDifference_equiv R t s e he, show moduleTowerDifference R M t x.val = 0
      from x.property, map_zero]⟩
  invFun y := ⟨(LinearEquiv.piCongrRight e).symm y.val, by
    change moduleTowerDifference R M t ((LinearEquiv.piCongrRight e).symm y.val) = 0
    apply (LinearEquiv.piCongrRight e).injective
    rw [moduleTowerDifference_equiv R t s e he, LinearEquiv.apply_symm_apply, map_zero]
    exact y.property⟩
  left_inv x := Subtype.ext ((LinearEquiv.piCongrRight e).symm_apply_apply x.val)
  right_inv y := Subtype.ext ((LinearEquiv.piCongrRight e).apply_symm_apply y.val)
  map_add' x y := Subtype.ext ((LinearEquiv.piCongrRight e).map_add x.val y.val)
  map_smul' r x := Subtype.ext ((LinearEquiv.piCongrRight e).map_smul r x.val)

@[simp] lemma moduleTowerLimitEquiv_apply (x : moduleTowerLimit R M t) (n : ℕ) :
    (moduleTowerLimitEquiv R t s e he x).val n = e n (x.val n) := rfl

include he in
lemma moduleTowerDifference_range_equiv :
    (moduleTowerDifference R M t).range.map (LinearEquiv.piCongrRight e).toLinearMap =
      (moduleTowerDifference R N s).range := by
  ext y
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨(LinearEquiv.piCongrRight e) x, (moduleTowerDifference_equiv R t s e he x).symm⟩
  · rintro ⟨x, rfl⟩
    refine ⟨moduleTowerDifference R M t ((LinearEquiv.piCongrRight e).symm x),
      ⟨_, rfl⟩, ?_⟩
    change (LinearEquiv.piCongrRight e)
      (moduleTowerDifference R M t ((LinearEquiv.piCongrRight e).symm x)) = _
    rw [moduleTowerDifference_equiv R t s e he, LinearEquiv.apply_symm_apply]

/-- The original difference cokernel, retaining rather than discarding lim¹. -/
def moduleTowerLimOneEquiv :
    ((∀ n, M n) ⧸ (moduleTowerDifference R M t).range) ≃ₗ[R]
      ((∀ n, N n) ⧸ (moduleTowerDifference R N s).range) :=
  Submodule.Quotient.equiv _ _ (LinearEquiv.piCongrRight e)
    (moduleTowerDifference_range_equiv R t s e he)

@[simp] lemma moduleTowerLimOneEquiv_mk (x : ∀ n, M n) :
    moduleTowerLimOneEquiv R t s e he (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ((LinearEquiv.piCongrRight e) x) := rfl

section Restrict
open CategoryTheory
variable {S : Type u} [CommRing S] [Algebra R S]
  (P : ℕ → ModuleCat.{u} S) (v : ∀ n, P (n + 1) ⟶ P n)

/-- Coefficient restriction preserves the original compatible sequences. -/
def moduleTowerLimitRestrictScalarsEquiv :
    moduleTowerLimit R
      (fun n => (ModuleCat.restrictScalars (algebraMap R S)).obj (P n))
      (fun n => ((ModuleCat.restrictScalars (algebraMap R S)).map (v n)).hom) ≃ₗ[R]
      (ModuleCat.restrictScalars (algebraMap R S)).obj
        (ModuleCat.of S (moduleTowerLimit S (fun n => P n) (fun n => (v n).hom))) where
  toFun x := ⟨x.val, x.property⟩
  invFun y := ⟨y.val, y.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Coefficient restriction preserves the actual difference cokernel, including its scalar action. -/
def moduleTowerLimOneRestrictScalarsEquiv :
    ((∀ n, (ModuleCat.restrictScalars (algebraMap R S)).obj (P n)) ⧸
      (moduleTowerDifference R
        (fun n => (ModuleCat.restrictScalars (algebraMap R S)).obj (P n))
        (fun n => ((ModuleCat.restrictScalars (algebraMap R S)).map (v n)).hom)).range) ≃ₗ[R]
      (ModuleCat.restrictScalars (algebraMap R S)).obj
        (ModuleCat.of S ((∀ n, P n) ⧸
          (moduleTowerDifference S (fun n => P n) (fun n => (v n).hom)).range)) := by
  letI : ∀ n, Module R (P n) := fun n => Module.compHom (P n) (algebraMap R S)
  letI : IsScalarTower R S (∀ n, P n) := IsScalarTower.of_algebraMap_smul fun r x => rfl
  exact Submodule.Quotient.restrictScalarsEquiv R
    (moduleTowerDifference S (fun n => P n) (fun n => (v n).hom)).range

end Restrict
end SerrePositivity.DerivedCompletion

end ModuleTowerEquivPart
