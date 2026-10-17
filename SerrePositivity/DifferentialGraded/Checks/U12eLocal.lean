module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleLocal
public import Mathlib.Data.ZMod.Basic

/-! # U12e-localの独立受入検査

## 概要
全導来合成・任意指定解像度の計算・自然性・単位・結合・三角・五角を同じ入口から監査する。

## 方針
独立宇宙の任意可換環と標数2で型を確認し、公開契約の公理を直接出力する。

## 規約と注意
局所Hom条件なしのdg圏分解経路の受入ではない。共有ルートをimportしない。

## 使われ方
formalization-plans/dg-theory.mdのU12e-local受入表からビルド・監査を再現する。
-/
@[expose] public section
noncomputable section
universe u v w z t x
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]

example (hE : localHomKFlat A E) : DerivedBimoduleCategory A C E ⥤
    (DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A B E) :=
  derivedBimoduleComposeFunctor A B C E hE

example (hE : localHomKFlat A E) (Q : BimoduleCategory A C E)
    (R : RightKFlatBimoduleCategory A C E) (q : R.obj ⟶ Q)
    (hq : BimoduleCategory.quasiIso A C E q) :
    (derivedBimoduleComposeFunctor A B C E hE).obj ((bimoduleToDerived A C E).obj Q) ≅
      derivedComposeWith A B C E R.obj R.property :=
  derivedBimoduleComposeResolutionComputation A B C E hE Q R q hq

example (B : Type v) (C : Type w) [DGCategory (ZMod 2) B] [DGCategory (ZMod 2) C]
    [Small.{0} B] [Small.{0} C] (hC : localHomKFlat (ZMod 2) C) :
    DerivedRightKFlatBimoduleCategory (ZMod 2) B C ≌ DerivedBimoduleCategory (ZMod 2) B C :=
  rightKFlatDerivedEquivalence (ZMod 2) B C hC

#print axioms exists_rightRelativeKFlat_bimodule_resolution
#print axioms rightKFlatDerivedEquivalence
#print axioms derivedBimoduleComposeFunctor
#print axioms derivedBimoduleComposeKFlatIso
#print axioms derivedBimoduleComposeKFlatValueIso
#print axioms derivedBimoduleComposeKFlatIso_naturality
#print axioms derivedBimoduleComposeKFlatValueIso_naturality
#print axioms derivedBimoduleComposeResolutionComputation
#print axioms derivedBimoduleComposeResolutionComputation_fac
#print axioms derivedBimoduleComposeResolutionComputation_self
#print axioms derivedBimoduleComposeResolutionComputation_naturality
#print axioms derivedBimoduleLeftUnitIso
#print axioms derivedBimoduleLeftUnitIso_resolution_app
#print axioms derivedBimoduleRightUnitIso
#print axioms derivedBimoduleAssociatorIso
#print axioms derivedBimoduleAssociator
#print axioms derivedBimoduleAssociator_naturality
#print axioms derivedBimoduleAssociatorIso_resolution_fac
#print axioms derivedBimoduleTriangle
#print axioms derivedBimoduleTriangle_app
#print axioms derivedBimodulePentagon
