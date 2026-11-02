module
public import SerrePositivity.DifferentialGraded.Resolution.Composition
public import Mathlib.Data.ZMod.Basic

/-! # 三圏同時制限と指定解像度変更の全導来合成比較の検査

## 概要
三圏同時制限と指定解像度変更の全導来合成比較の検査。

## 方針
既存の例・型照合・公理監査集合を保持し、証明済みの個別契約を検査する。

## 規約と注意
U12e-general（中断）の一部。R1〜R7への足場として保持する。収録された個別宣言の証明済み範囲と、一般経路全体の未受入を区別する。
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。対応する一般APIの再現可能な検査入口。中断した一般経路を再開する際にも同じ対象を再実行できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
universe u v w z t s r v' w' z' v'' w'' z''
open CategoryTheory CategoryTheory.Functor
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensor

section General
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (C : Type z) [DGCategory A C] [Small.{u} C]
  (K : Type t) [DGCategory A K] [Small.{u} K]
  (E : Type s) [DGCategory A E] [Small.{u} E]
  (L : Type r) [DGCategory A L] [Small.{u} L]
  (F : DGFunctor A D B) (G : DGFunctor A K C) (H : DGFunctor A L E)

-- 左右どちらの順序からも、既存の同じ同時導来制限へ比較できる。
example :
    derivedBimoduleRestriction A D C B C F (DGFunctor.id C) ⋙
        derivedBimoduleRestriction A D K D C (DGFunctor.id D) G ≅
      derivedBimoduleRestriction A D K B C F G :=
  pairedRestrictionReverseDerivedIso A B C D K F G

-- 六つの対象宇宙は独立。F・Hの準同値性やB・D・C・KのHomのK-flat性は不要。
example (hE : localHomKFlat A E) (hL : localHomKFlat A L) (hG : QuasiEquivalence G)
    (Q : DerivedBimoduleCategory A C E) (P : DerivedBimoduleCategory A B C) :
    ((derivedBimoduleComposeFunctor A D K L hL).obj
        ((derivedBimoduleRestriction A K L C E G H).obj Q)).obj
        ((derivedBimoduleRestriction A D K B C F G).obj P) ≅
      (derivedBimoduleRestriction A D L B E F H).obj
        (((derivedBimoduleComposeFunctor A B C E hE).obj Q).obj P) :=
  ((derivedBimoduleComposeRestrictionIso A B D C K E L F G H hE hL hG).app Q).app P

-- 任意のGの場合にも、比較自然変換は定義される。
example (hE : localHomKFlat A E) (hL : localHomKFlat A L) :
    simultaneousRestrictionDerivedSource A B D C K E L F G H hL ⟶
      endpointRestrictionDerivedTarget A B D C E L F H hE :=
  simultaneousRestrictionDerivedComparison A B D C K E L F G H hE hL
end General

section Resolutions
open SerrePositivity.DifferentialGraded.ResolutionBimodule
variable (A : Type u) [CommRing A]
  {B : Type v} [DGCategory A B] {C : Type w} [DGCategory A C]
  {E : Type z} [DGCategory A E]

-- 元のB・C・EのsmallnessやHomのK-flat性を追加せず、共通sourceへの合成比較を得る。
example (P : KFlatDGResolution.{u, v, v'} A B) (Q : KFlatDGResolution.{u, w, w'} A C)
    (R : KFlatDGResolution.{u, z, z'} A E) :
    comparisonLeft A Q R ⋙
        derivedBimoduleComposeFunctor A P.ComparisonSource Q.ComparisonSource R.ComparisonSource
          R.comparisonSource_homKFlat ⋙
        (whiskeringLeft _ _ _).obj (comparisonLeft A P Q) ≅
      composeFunctor A P Q R ⋙ (whiskeringRight _ _ _).obj (comparisonLeft A P R) :=
  comparisonLeftComposeIso A P Q R

variable [Small.{u} B] [Small.{u} C] [Small.{u} E]

-- 変更前後の六つの解像度source宇宙は独立で、既存のchangeEquivalenceをそのまま使う。
example (P : KFlatDGResolution.{u, v, v'} A B) (Q : KFlatDGResolution.{u, w, w'} A C)
    (R : KFlatDGResolution.{u, z, z'} A E) (P' : KFlatDGResolution.{u, v, v''} A B)
    (Q' : KFlatDGResolution.{u, w, w''} A C) (R' : KFlatDGResolution.{u, z, z''} A E)
    (N : DerivedCategory A Q R) (M : DerivedCategory A P Q) :
    ((composeFunctor A P' Q' R').obj ((changeEquivalence A Q R Q' R').functor.obj N)).obj
        ((changeEquivalence A P Q P' Q').functor.obj M) ≅
      (changeEquivalence A P R P' R').functor.obj (((composeFunctor A P Q R).obj N).obj M) :=
  ((changeComposeIso A P Q R P' Q' R').app N).app M
end Resolutions

example (X : Type v) [DGCategory (ZMod 2) X] [Small.{0} X] (hX : localHomKFlat (ZMod 2) X) :
    simultaneousRestrictionDerivedSource (ZMod 2) X X X X X X
        (DGFunctor.id X) (DGFunctor.id X) (DGFunctor.id X) hX ≅
      endpointRestrictionDerivedTarget (ZMod 2) X X X X X (DGFunctor.id X) (DGFunctor.id X) hX :=
  derivedBimoduleComposeRestrictionIso (ZMod 2) X X X X X X
    (DGFunctor.id X) (DGFunctor.id X) (DGFunctor.id X) hX hX quasiEquivalence_id

#print axioms BimoduleCategory.pairedRestrictionFunctor
#print axioms Bimodule.pairedRestriction_uncurryHom
#print axioms BimoduleCategory.pairedRestrictionFunctor_map_value
#print axioms Bimodule.pairedRestriction_interchange
#print axioms BimoduleCategory.pairedRestrictionInterchangeObjIso
#print axioms BimoduleCategory.pairedRestrictionInterchangeObjIso_hom_eval
#print axioms BimoduleCategory.pairedRestrictionInterchangeIso
#print axioms BimoduleTensorModule.pairedRestrictionPresentationObjIso
#print axioms BimoduleTensorModule.pairedRestrictionPresentationObjIso_hom_eval
#print axioms BimoduleTensorModule.pairedRestrictionPresentationIso
#print axioms pairedRestrictionIso
#print axioms pairedRestrictionDerivedIso
#print axioms pairedRestrictionPartialPresentationIso
#print axioms pairedRestrictionPartialPreIso
#print axioms pairedRestrictionPartialDerivedIso
#print axioms pairedRestrictionPartialDerivedIso_hom_app
#print axioms pairedRestrictionReversePresentationIso
#print axioms pairedRestrictionReversePreIso
#print axioms pairedRestrictionReverseDerivedIso
#print axioms pairedRestrictionReverseDerivedIso_hom_app
#print axioms BimoduleTensor.endpointRestrictionDerivedSource
#print axioms BimoduleTensor.endpointRestrictionDerivedTarget
#print axioms BimoduleTensor.derivedBimoduleComposeEndpointRestrictionIso
#print axioms BimoduleTensor.simultaneousRestrictionDerivedSource
#print axioms BimoduleTensor.simultaneousRestrictionMiddleSource
#print axioms BimoduleTensor.simultaneousRestrictionSourceIso
#print axioms BimoduleTensor.simultaneousRestrictionDerivedComparison
#print axioms BimoduleTensor.derivedBimoduleComposeRestrictionIso
#print axioms BimoduleTensor.derivedBimoduleComposeRestrictionIso_hom
#print axioms ResolutionBimodule.comparisonLeftComposeIso
#print axioms ResolutionBimodule.comparisonRightComposeIso
#print axioms ResolutionBimodule.inverseCompositionComparison
#print axioms ResolutionBimodule.canonicalComparisonComposeIso
#print axioms ResolutionBimodule.changeComposeIso
