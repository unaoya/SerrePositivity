module

public import SerrePositivity.CommutativeAlgebra.EtaleStratification.StratumLift
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# 被約テンソル積の射の構成

## 概要
基底上で一致する環準同型の組からテンソル積の射を作り、被約終域への射を被約化に降ろす。

## 方針
終域の基底代数構造を射から指定して、テンソル積と商の普遍性を使う。

## 規約
射の計算規則を元と純テンソルで記述する。

## 使われ方
底変換した層の標準同型を、双方向の射から構成する。
-/

@[expose] public section
noncomputable section
universe u

namespace SerrePositivity.CommutativeAlgebra

open scoped TensorProduct

/-- 基底で一致する二つの環準同型をテンソル積からの射に延ばす。 -/
def tensorRingLift {R A B C : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] (f : A →+* C) (g : B →+* C)
    (h : f.comp (algebraMap R A) = g.comp (algebraMap R B)) : A ⊗[R] B →+* C := by
  let : Algebra R C := (f.comp (algebraMap R A)).toAlgebra
  let f' : A →ₐ[R] C := { __ := f, commutes' := fun _ ↦ rfl }
  let g' : B →ₐ[R] C := { __ := g, commutes' := fun r ↦ (RingHom.congr_fun h r).symm }
  exact (Algebra.TensorProduct.lift f' g' fun _ _ ↦ Commute.all _ _).toRingHom

@[simp]
theorem tensorRingLift_tmul {R A B C : Type u}
    [CommRing R] [CommRing A] [CommRing B] [CommRing C] [Algebra R A] [Algebra R B]
    (f : A →+* C) (g : B →+* C) (h) (a : A) (b : B) :
    tensorRingLift f g h (a ⊗ₜ[R] b) = f a * g b := by
  simp only [tensorRingLift, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.lift_tmul]
  rfl

/-- 被約環への射を始域の被約化に降ろす。 -/
def reductionLift {A B : Type u} [CommRing A] [CommRing B] [IsReduced B]
    (f : A →+* B) : A ⧸ nilradical A →+* B :=
  Ideal.Quotient.lift _ f fun _ hx ↦ ((mem_nilradical.mp hx).map f).eq_zero

@[simp]
theorem reductionLift_mk {A B : Type u} [CommRing A] [CommRing B] [IsReduced B]
    (f : A →+* B) (x : A) : reductionLift f (Ideal.Quotient.mk (nilradical A) x) = f x := rfl

/-- 被約化は被約。 -/
theorem isReduced_reduction (A : Type u) [CommRing A] : IsReduced (A ⧸ nilradical A) :=
  (Ideal.isRadical_iff_quotient_reduced (nilradical A)).mp (Ideal.radical_isRadical _)

end SerrePositivity.CommutativeAlgebra
