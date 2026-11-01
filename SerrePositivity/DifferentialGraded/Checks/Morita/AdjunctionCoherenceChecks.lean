module
public import SerrePositivity.DifferentialGraded.Morita.Adjunction.Coherence
public import Mathlib.Data.ZMod.Basic

/-! # 一般右随伴の恒等・合成計算の監査

## 概要
恒等・合成kernelの実際の右随伴とunit/counitの計算を監査する。

## 方針
独立対象宇宙・標数2で検査し、kernelのMorita性や列の射影性を仮定しない。

## 規約と注意
恒等比較に局所Hom条件は不要。合成は始域DのlocalHomKFlatだけを保持する。

## 使われ方
U16の一般右随伴による合成計算と、Morita逆関手の比較の再現入口。
-/
@[expose] public section
noncomputable section
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensor
open SerrePositivity.DifferentialGraded.Morita
universe u v w z
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (F : Type z) [DGCategory A F] [Small.{u} F]

example : kernelDerivedHom A D D (kernelIdentity A D) ≅ 𝟭 (DerivedModuleCategory A D) :=
  kernelDerivedHomIdentityIso A D

example (hD : localHomKFlat A D) (P : Kernel A D E) (Q : Kernel A E F) :
    kernelDerivedHom A D F (kernelCompose A D E F hD P Q) ≅
      kernelDerivedHom A E F Q ⋙ kernelDerivedHom A D E P :=
  kernelDerivedHomCompositionIso A D E F hD P Q

example (D : Type v) [DGCategory (ZMod 2) D] [Small.{0} D]
    (E : Type w) [DGCategory (ZMod 2) E] [Small.{0} E]
    (F : Type z) [DGCategory (ZMod 2) F] [Small.{0} F]
    (hD : localHomKFlat (ZMod 2) D) (P : Kernel (ZMod 2) D E) (Q : Kernel (ZMod 2) E F) :
    kernelDerivedHom (ZMod 2) D F (kernelCompose (ZMod 2) D E F hD P Q) ≅
      kernelDerivedHom (ZMod 2) E F Q ⋙ kernelDerivedHom (ZMod 2) D E P :=
  kernelDerivedHomCompositionIso (ZMod 2) D E F hD P Q

#print axioms kernelIdentityRightAdjunction
#print axioms kernelDerivedHomIdentityIso
#print axioms kernelDerivedHomIdentityIso_unit
#print axioms kernelDerivedHomIdentityIso_counit
#print axioms kernelCompositionRightAdjunction
#print axioms kernelCompositionRightAdjunction_unit_app
#print axioms kernelCompositionRightAdjunction_counit_app
#print axioms kernelDerivedHomCompositionIso
#print axioms kernelDerivedHomCompositionIso_unit
#print axioms kernelDerivedHomCompositionIso_counit
