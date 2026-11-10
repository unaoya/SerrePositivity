module

public import SerrePositivity.HomologicalAlgebra.Cosimplicial.CohomologyZero
public import SerrePositivity.HomologicalAlgebra.Cosimplicial.CupCommutativity
public import Mathlib.Algebra.DirectSum.Algebra
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.CohomologyZero
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.CupProduct

/-!
# 余単体的可換環のコホモロジーの次数付き環

## 概要
Alexander–Whitney 積と零次の単位からコホモロジーの次数付き環を構成する。

## 方針
余輪体の代表元に戻って積の各公理を確認する。

## 規約
斉次元の積の順序は前面・後面。

## 使われ方
Bockstein を微分とする次数付き代数。
-/

public noncomputable section

open CategoryTheory
open scoped Simplicial

universe u

namespace SerrePositivity.Cosimplicial

variable (X : CosimplicialObject CommRingCat.{u})

/-- コホモロジーの cup 積は左の和に分配的。 -/
theorem cohomologyCup_add_left {i j : ℕ} (x y : cohomology X i) (z : cohomology X j) :
    cohomologyCup X (x+y) z = cohomologyCup X x z + cohomologyCup X y z := by
  obtain ⟨x, rfl⟩ := cohomologyClass_surjective X i x
  obtain ⟨y, rfl⟩ := cohomologyClass_surjective X i y
  obtain ⟨z, rfl⟩ := cohomologyClass_surjective X j z
  rw [← map_add, cohomologyCup_class, cohomologyCup_class, cohomologyCup_class, ← map_add]
  congr 1
  apply Subtype.ext
  let x' : X.obj ⦋i⦌ := x.1
  let y' : X.obj ⦋i⦌ := y.1
  let z' : X.obj ⦋j⦌ := z.1
  change cup X (x' + y') z' = cup X x' z' + cup X y' z'
  unfold cup
  rw [map_add, add_mul]

/-- コホモロジーの cup 積は右の和に分配的。 -/
theorem cohomologyCup_add_right {i j : ℕ} (x : cohomology X i) (y z : cohomology X j) :
    cohomologyCup X x (y+z) = cohomologyCup X x y + cohomologyCup X x z := by
  obtain ⟨x, rfl⟩ := cohomologyClass_surjective X i x
  obtain ⟨y, rfl⟩ := cohomologyClass_surjective X j y
  obtain ⟨z, rfl⟩ := cohomologyClass_surjective X j z
  rw [← map_add, cohomologyCup_class, cohomologyCup_class, cohomologyCup_class, ← map_add]
  congr 1
  apply Subtype.ext
  let x' : X.obj ⦋i⦌ := x.1
  let y' : X.obj ⦋j⦌ := y.1
  let z' : X.obj ⦋j⦌ := z.1
  change cup X x' (y' + z') = cup X x' y' + cup X x' z'
  unfold cup
  rw [map_add, mul_add]

private theorem class_cast {i j : ℕ} (h : i = j) (z : Cocycles X i) :
    cast (congrArg (cohomology X) h) (cohomologyClass X i z) =
      cohomologyClass X j (cast (congrArg (fun n => ↥(Cocycles X n)) h) z) := by
  subst j
  rfl

private theorem val_cast {i j : ℕ} (h : i = j) (z : Cocycles X i) :
    (cast (congrArg (fun n => ↥(Cocycles X n)) h) z).1 =
      cast (congrArg (fun n => (X.obj ⦋n⦌ : Type u)) h) z.1 := by
  subst j
  rfl

/-- コホモロジーの cup 積の結合律。 -/
theorem cohomologyCup_assoc {i j k : ℕ} (x : cohomology X i) (y : cohomology X j)
    (z : cohomology X k) :
    cast (congrArg (cohomology X) (Nat.add_assoc i j k)) (cohomologyCup X (cohomologyCup X x y) z) =
      cohomologyCup X x (cohomologyCup X y z) := by
  obtain ⟨x, rfl⟩ := cohomologyClass_surjective X i x
  obtain ⟨y, rfl⟩ := cohomologyClass_surjective X j y
  obtain ⟨z, rfl⟩ := cohomologyClass_surjective X k z
  simp only [cohomologyCup_class]
  erw [class_cast X (Nat.add_assoc i j k)]
  congr 1
  apply Subtype.ext
  rw [val_cast]
  exact cup_assoc X x.1 y.1 z.1
  all_goals exact Nat.add_assoc i j k

private theorem cup_one_left {n : ℕ} (z : X.obj ⦋n⦌) :
    cast (congrArg (fun n => (X.obj ⦋n⦌ : Type u)) (Nat.zero_add n))
      (cup X (1 : X.obj ⦋0⦌) z) = z := by
  rw [cast_obj, cup, map_one, one_mul]
  have h : backFace 0 n ≫ eqToHom (congrArg SimplexCategory.mk (Nat.zero_add n)) = 𝟙 ⦋n⦌ := by
    ext i
    simp [backFace]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp, h]
  · exact ConcreteCategory.congr_hom (X.map_id ⦋n⦌) z
  · exact Nat.zero_add n

/-- 零次コホモロジーの 1 は cup 積の左単位。 -/
theorem cohomologyCup_one_left {n : ℕ} (z : cohomology X n) :
    cast (congrArg (cohomology X) (Nat.zero_add n))
      (cohomologyCup X (1 : cohomology X 0) z) = z := by
  obtain ⟨z, rfl⟩ := cohomologyClass_surjective X n z
  change cast _ (cohomologyCup X (cohomologyClass X 0 (zeroCocyclesEquiv X 1))
    (cohomologyClass X n z)) = cohomologyClass X n z
  rw [cohomologyCup_class, class_cast]
  congr 1
  apply Subtype.ext
  rw [val_cast]
  exact cup_one_left X z.1
  all_goals exact Nat.zero_add n

/-- 零次コホモロジーの 1 は cup 積の右単位。 -/
theorem cohomologyCup_one_right {n : ℕ} (z : cohomology X n) :
    cohomologyCup X z (1 : cohomology X 0) = z := by
  have h := cohomologyCup_comm X (1 : cohomology X 0) z
  simpa only [Nat.zero_mul, pow_zero, one_zsmul, cohomologyCup_one_left] using h.symm

private theorem heq_of_cast {i j : ℕ} (h : i = j)
    {x : cohomology X i} {y : cohomology X j} (hxy : cast (congrArg (cohomology X) h) x = y) :
    HEq x y := by
  subst j
  exact heq_of_eq hxy

local instance : GradedMonoid.GOne (cohomology X) where one := 1
local instance : GradedMonoid.GMul (cohomology X) where mul := cohomologyCup X

/-- 余単体的可換環のコホモロジー上の斉次 cup 積の環構造。 -/
@[instance_reducible] def cohomologyCupGradedRing : DirectSum.GRing (cohomology X) where
  one := 1
  mul := cohomologyCup X
  mul_zero {i j} a := by
    have h := cohomologyCup_add_right X a (0 : cohomology X j) 0
    rw [zero_add] at h
    exact add_left_cancel (h.symm.trans (add_zero _).symm)
  zero_mul {i j} b := by
    have h := cohomologyCup_add_left X (0 : cohomology X i) 0 b
    rw [zero_add] at h
    exact add_left_cancel (h.symm.trans (add_zero _).symm)
  mul_add := cohomologyCup_add_right X
  add_mul := cohomologyCup_add_left X
  one_mul a := Sigma.ext (Nat.zero_add _) (heq_of_cast X (Nat.zero_add _) (cohomologyCup_one_left X a.2))
  mul_one a := Sigma.ext rfl (heq_of_eq (cohomologyCup_one_right X a.2))
  mul_assoc a b c := Sigma.ext (Nat.add_assoc _ _ _)
    (heq_of_cast X (Nat.add_assoc _ _ _) (cohomologyCup_assoc X a.2 b.2 c.2))
  gnpow := GradedMonoid.GMonoid.gnpowRec
  gnpow_zero' := GradedMonoid.GMonoid.gnpowRec_zero
  gnpow_succ' := GradedMonoid.GMonoid.gnpowRec_succ
  natCast := Nat.cast
  natCast_zero := Nat.cast_zero
  natCast_succ := Nat.cast_succ
  intCast := Int.cast
  intCast_ofNat := Int.cast_natCast
  intCast_negSucc_ofNat := Int.cast_negSucc

end SerrePositivity.Cosimplicial
