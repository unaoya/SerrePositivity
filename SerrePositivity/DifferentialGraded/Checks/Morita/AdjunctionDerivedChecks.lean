module
public import SerrePositivity.DifferentialGraded.Morita.AdjunctionDerived
public import Mathlib.Data.ZMod.Basic

/-! # 任意kernelの実際の導来右随伴とunit/counitの監査

## 概要
任意可換環・独立対象宇宙で、全kernelの実際の随伴と三角恒等式を検査する。

## 方針
全入力のHom表現から構成した随伴を直接使い、標数2でも追加平坦性なしの型を確認する。

## 規約と注意
恒等・結合の作用coherenceとU16全体の受入は別の検証を要する。

## 使われ方
U16a公開契約の一般右随伴とunit/counitの再現入口。
-/
@[expose] public section
noncomputable section
universe u v w
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.Morita
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]

example (K : Kernel A D E) : kernelDerivedTensor A D E K ⊣ kernelDerivedHom A D E K :=
  kernelDerivedAdjunction A D E K

example (K : Kernel A D E) (X : DerivedModuleCategory A D) :
    (kernelDerivedTensor A D E K).map ((kernelDerivedUnit A D E K).app X) ≫
      (kernelDerivedCounit A D E K).app ((kernelDerivedTensor A D E K).obj X) = 𝟙 _ :=
  kernelDerived_left_triangle A D E K X

example (K : Kernel A D E) (Y : DerivedModuleCategory A E) :
    (kernelDerivedUnit A D E K).app ((kernelDerivedHom A D E K).obj Y) ≫
      (kernelDerivedHom A D E K).map ((kernelDerivedCounit A D E K).app Y) = 𝟙 _ :=
  kernelDerived_right_triangle A D E K Y

example (K : Kernel A D E) {Y Y' : DerivedModuleCategory A E} (f : Y ⟶ Y') :
    (kernelDerivedTensor A D E K).map ((kernelDerivedHom A D E K).map f) ≫
        (kernelDerivedCounit A D E K).app Y' =
      (kernelDerivedCounit A D E K).app Y ≫ f :=
  (kernelDerivedCounit A D E K).naturality f

example (D : Type v) [DGCategory (ZMod 2) D] [Small.{0} D]
    (E : Type w) [DGCategory (ZMod 2) E] [Small.{0} E] (K : Kernel (ZMod 2) D E) :
    kernelDerivedTensor (ZMod 2) D E K ⊣ kernelDerivedHom (ZMod 2) D E K :=
  kernelDerivedAdjunction (ZMod 2) D E K

#print axioms brownHomComparison
#print axioms brownHomComparison_kernel_zero
#print axioms brownHomComparison_triangle
#print axioms brownHomComparison_retract
#print axioms brownHomComparison_iso
#print axioms brownHomComparison_isZero
#print axioms brownHomComparison_coproduct
#print axioms brownHomProperty
#print axioms brownHomProperty_shift
#print axioms brownHomPropertyIsClosedUnderIsomorphisms
#print axioms brownHomPropertyIsStableUnderRetracts
#print axioms brownHomPropertyIsTriangulated
#print axioms brownHomProperty_coproduct
#print axioms brownHomComparison_all
#print axioms kernelBrownTelescope_hom_bijective
#print axioms kernelBrownTelescopeHomEquiv
#print axioms kernelDerivedHomEquiv
#print axioms kernelDerivedHomEquiv_naturality
#print axioms kernelDerivedHomEquiv_symm_apply
#print axioms kernelDerivedHom
#print axioms kernelDerivedAdjunction
#print axioms kernelDerivedUnit
#print axioms kernelDerivedCounit
#print axioms kernelDerivedHom_obj
#print axioms kernelDerivedCounit_model
#print axioms kernelDerived_left_triangle
#print axioms kernelDerived_right_triangle
