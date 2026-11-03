module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleComposition.Resolution
public import Mathlib.Data.ZMod.Basic

/-! # K-flat局所化比較同値と両変数の導来bimodule合成の監査

## 概要
K-flat局所化比較同値と両変数の導来bimodule合成の監査。

## 方針
既存の例・型照合・公理監査集合を保持し、証明済みの個別契約を検査する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。対応する一般APIの再現可能な検査入口。中断した一般経路を再開する際にも同じ対象を再実行できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
universe u v w z
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]

example (hC : localHomKFlat A C) :
    DerivedRightKFlatBimoduleCategory A B C ≌ DerivedBimoduleCategory A B C :=
  rightKFlatDerivedEquivalence A B C hC

example (hC : localHomKFlat A C) : (rightKFlatDerivedInclusion A B C).Full :=
  (rightKFlatDerivedInclusion_fullyFaithful A B C hC).full

example (hC : localHomKFlat A C) : (rightKFlatDerivedInclusion A B C).Faithful :=
  (rightKFlatDerivedInclusion_fullyFaithful A B C hC).faithful

example (hC : localHomKFlat A C) (X : DerivedRightKFlatBimoduleCategory A B C) :
    (rightKFlatDerivedEquivalence A B C hC).functor.map
        ((rightKFlatDerivedEquivalence A B C hC).unitIso.hom.app X) ≫
      (rightKFlatDerivedEquivalence A B C hC).counitIso.hom.app
        ((rightKFlatDerivedEquivalence A B C hC).functor.obj X) = 𝟙 _ :=
  (rightKFlatDerivedEquivalence A B C hC).functor_unitIso_comp X

example (hE : localHomKFlat A E) :
    DerivedBimoduleCategory A C E ⥤
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

#print axioms rightKFlatAugmentation
#print axioms rightKFlat_inverse_rightRelativeKFlat
#print axioms rightKFlatAugmentation_naturality
#print axioms rightKFlatAugmentationIso
#print axioms rightKFlatDerivedInclusion_map_base
#print axioms rightKFlatGlobalAugmentation_naturality
#print axioms rightKFlatGlobalAugmentationIso
#print axioms derivedRightKFlatReplacement_lifting
#print axioms rightKFlatCompositeFacIso
#print axioms rightKFlatComposite_lifting
#print axioms rightKFlatReplacementUnitIso
#print axioms rightKFlatReplacementCounitIso
#print axioms rightKFlatDerivedEquivalence
#print axioms rightKFlatDerivedInclusion_isEquivalence
#print axioms rightKFlatDerivedInclusion_fullyFaithful
#print axioms derivedBimoduleComposeFunctor
#print axioms derivedBimoduleComposeKFlatFamilyIso
#print axioms derivedBimoduleComposeKFlatIso
#print axioms derivedBimoduleComposeKFlatValueIso
#print axioms derivedBimoduleComposeResolutionComputation
#print axioms derivedBimoduleComposeKFlatIso_naturality
