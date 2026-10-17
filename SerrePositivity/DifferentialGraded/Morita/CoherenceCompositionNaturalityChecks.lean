module
public import SerrePositivity.DifferentialGraded.Morita.CoherenceCompositionNaturality
public import SerrePositivity.DifferentialGraded.Morita.CoherenceComposition

/-! # kernel射による計算と通常作用合成の自然性の監査

## 概要
任意のkernel射について計算同型・増大・通常合成が同じ図式で整合することを検査する。

## 方針
独立宇宙と任意解像度族でkernel変数の自然性を確認し、追加全宣言を直接公理監査する。

## 規約と注意
局所Hom条件なしの通常比較であり、全導来kernelの合成比較の自然性とは区別する。

## 使われ方
U16aの主導来kernelへの自然性降下を進める前の再現入口。
-/
@[expose] public section
noncomputable section
universe u v w z
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.Morita
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (F : Type z) [DGCategory A F] [Small.{u} F]

example {P P' : BimoduleCategory A E D} {Q Q' : BimoduleCategory A F E}
    (f : P ⟶ P') (g : Q ⟶ Q') :
    NatTrans.hcomp (kernelTensorMap A D E f) (kernelTensorMap A E F g) ≫
        (kernelTensorCompositionClosedIso A D E F
          (BimoduleCategory.underlying A E D P') (BimoduleCategory.underlying A F E Q')).hom =
      (kernelTensorCompositionClosedIso A D E F
          (BimoduleCategory.underlying A E D P) (BimoduleCategory.underlying A F E Q)).hom ≫
        kernelTensorMap A D F (BimoduleTensor.composeMap A F E D g f) :=
  kernelTensorCompositionClosedIso_kernel_naturality A D E F f g

example {P P' : BimoduleCategory A E D} (f : P ⟶ P')
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    Functor.whiskerLeft (moduleToDerived A D) (kernelResolutionDerivedTensorMap A D E R f) ≫
        (kernelResolutionTensorModelIso A D E (BimoduleCategory.underlying A E D P') R).hom =
      (kernelResolutionTensorModelIso A D E (BimoduleCategory.underlying A E D P) R).hom ≫
        kernelResolutionTensorModelMap A D E f R :=
  kernelResolutionTensorModelIso_kernel_naturality A D E f R

#print axioms kernelTensorHomotopyComputation_kernel_naturality
#print axioms kernelResolutionDerivedTensorComputation_kernel_naturality
#print axioms kernelDerivedTensorAugmentation_kernel_naturality
#print axioms kernelResolutionTensorModelMap
#print axioms kernelResolutionTensorModelIso_kernel_naturality
#print axioms kernelTensorCompositionClosedIso_hom_app
#print axioms kernelTensorCompositionMap_app
#print axioms kernelTensorCompositionClosedIso_kernel_naturality
#print axioms kernelCompositionIso
