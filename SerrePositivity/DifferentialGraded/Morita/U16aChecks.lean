module
public import SerrePositivity.DifferentialGraded.Morita.U16a
public import SerrePositivity.DifferentialGraded.Morita.AdjunctionDerivedChecks
public import SerrePositivity.DifferentialGraded.Morita.CoherenceAssociatorMainChecks
public import SerrePositivity.DifferentialGraded.Morita.CoherenceUnitChecks
public import SerrePositivity.DifferentialGraded.Morita.CoherenceCompositionCanonicalChecks
public import Mathlib.Data.ZMod.Basic

/-! # U16aの独立統合監査

## 概要
主導来作用・任意kernel随伴と両単位・結合coherenceを同時に検証する。

## 方針
既存主要Checksを同時importし、新規左単位図式を独立宇宙と標数2で型検査する。

## 規約と注意
U16c・dと一般分解経路の受入を意味しない。共有ルートをimportしない。

## 使われ方
U16a受入の再現入口。
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Functor
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensor
open SerrePositivity.DifferentialGraded.Morita
universe u v w
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]

example (hD : localHomKFlat A D) (hE : localHomKFlat A E) (P : Kernel A D E) :
    (kernelCompositionIso A D E E hD P (kernelIdentity A E)).hom ≫
      (kernelDerivedTensorFunctor A D E).map ((derivedBimoduleLeftUnitIso A E D hD).hom.app P) =
    whiskerLeft (kernelDerivedTensor A D E P) (kernelIdentityIso A E).hom ≫
      (Functor.rightUnitor (kernelDerivedTensor A D E P)).hom :=
  kernelCompositionIso_leftUnit A D E hD hE P

example (D : Type v) [DGCategory (ZMod 2) D] [Small.{0} D]
    (E : Type w) [DGCategory (ZMod 2) E] [Small.{0} E]
    (hD : localHomKFlat (ZMod 2) D) (hE : localHomKFlat (ZMod 2) E)
    (P : Kernel (ZMod 2) D E) :
    (kernelCompositionIso (ZMod 2) D E E hD P (kernelIdentity (ZMod 2) E)).hom ≫
      (kernelDerivedTensorFunctor (ZMod 2) D E).map
        ((derivedBimoduleLeftUnitIso (ZMod 2) E D hD).hom.app P) =
    whiskerLeft (kernelDerivedTensor (ZMod 2) D E P) (kernelIdentityIso (ZMod 2) E).hom ≫
      (Functor.rightUnitor (kernelDerivedTensor (ZMod 2) D E P)).hom :=
  kernelCompositionIso_leftUnit (ZMod 2) D E hD hE P

#print axioms kernelAssociatorIso_identity_triangle
#print axioms kernelCompositionIso_leftUnit

#print axioms kernelDerivedTensorFunctor
#print axioms kernelDerivedTensorComputation
#print axioms kernelDerivedHom
#print axioms kernelDerivedAdjunction
#print axioms kernelDerivedUnit
#print axioms kernelDerivedCounit
#print axioms kernelDerived_left_triangle
#print axioms kernelDerived_right_triangle
#print axioms kernelIdentityIso
#print axioms kernelCompositionIso
#print axioms kernelCompositionIso_naturality
#print axioms kernelCompositionIso_rightUnit
#print axioms kernelCompositionIso_associator
