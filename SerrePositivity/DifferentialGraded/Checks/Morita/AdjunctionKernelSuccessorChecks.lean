module
public import SerrePositivity.DifferentialGraded.Morita.AdjunctionKernelSuccessor
public import Mathlib.Data.ZMod.Basic

/-! # 実際の主導来kernel作用の初期被覆と関係除去の監査

## 概要
任意の主導来kernelに追加の射影性・平坦性を課さず、初期被覆と後続操作を検査する。

## 方針
独立宇宙・任意可換環・標数2と、後続操作の延長式・関係消去を直接確認する。

## 規約と注意
一般右随伴の存在そのものは未完。可算列とtelescopeでの表現可能性を後続で証明する。

## 使われ方
U16aの一般右随伴構成の初期値と後続値の再現入口。
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

example (K : Kernel A D E) (Y : DerivedModuleCategory A E) (p : D × ℤ)
    (f : (kernelDerivedTensor A D E K).obj (moduleCompactGenerators A D p) ⟶ Y) :
    ∃ g : moduleCompactGenerators A D p ⟶
        brownSeed A D E (kernelDerivedTensor A D E K) Y,
      (kernelDerivedTensor A D E K).map g ≫ kernelBrownSeedMap A D E K Y = f :=
  kernelBrownSeedMap_generator_surjective A D E K Y p f

example (K : Kernel A D E) {X : DerivedModuleCategory A D} {Y : DerivedModuleCategory A E}
    (r : (kernelDerivedTensor A D E K).obj X ⟶ Y) :
    (kernelDerivedTensor A D E K).map (kernelBrownSuccessor A D E K r).map ≫
      (kernelBrownSuccessor A D E K r).target = r :=
  kernelBrownSuccessor_fac A D E K r

example (K : Kernel A D E) {X : DerivedModuleCategory A D} {Y : DerivedModuleCategory A E}
    (r : (kernelDerivedTensor A D E K).obj X ⟶ Y) (p : D × ℤ)
    (f : moduleCompactGenerators A D p ⟶ X)
    (hf : (kernelDerivedTensor A D E K).map f ≫ r = 0) :
    f ≫ (kernelBrownSuccessor A D E K r).map = 0 :=
  kernelBrownSuccessor_kills A D E K r p f hf

example (D : Type v) [DGCategory (ZMod 2) D] [Small.{0} D]
    (E : Type w) [DGCategory (ZMod 2) E] [Small.{0} E] (K : Kernel (ZMod 2) D E)
    {X : DerivedModuleCategory (ZMod 2) D} {Y : DerivedModuleCategory (ZMod 2) E}
    (r : (kernelDerivedTensor (ZMod 2) D E K).obj X ⟶ Y) :
    BrownSuccessor (ZMod 2) D E (kernelDerivedTensor (ZMod 2) D E K) r :=
  kernelBrownSuccessor (ZMod 2) D E K r

#print axioms brownRelationRawIndex
#print axioms brownRelationRawIndexSmall
#print axioms brownRelationIndex
#print axioms brownRelationFamily
#print axioms brownRelationArrow
#print axioms brownRelationArrow_condition
#print axioms brownRelationObject
#print axioms brownRelationMap
#print axioms brownRelationMap_ι
#print axioms brownRelationMap_image_zero
#print axioms brownRelationMap_kills
#print axioms BrownSuccessor
#print axioms brownSuccessor_nonempty
#print axioms brownSuccessor
#print axioms brownSuccessor_fac
#print axioms brownSuccessor_kills
#print axioms kernelBrownSeedMap
#print axioms kernelBrownSeedMap_generator_surjective
#print axioms kernelBrownSuccessor
#print axioms kernelBrownSuccessor_fac
#print axioms kernelBrownSuccessor_kills
