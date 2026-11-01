module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleCanonicalComposition
public import SerrePositivity.DifferentialGraded.Tensor.ResolvedRestriction
public import Mathlib.Data.ZMod.Basic

/-! # 指定モデルと標準解像度による中間比較の恒等・dg関手合成則の検査

## 概要
指定モデルと標準解像度による中間比較の恒等・dg関手合成則の検査。

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
universe u v w z t s
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (E : Type z) [DGCategory A E] [Small.{u} E]
  (T : Type t) [DGCategory A T] [Small.{u} T]
  (L : Type s) [DGCategory A L] [Small.{u} L]
  (F : DGFunctor A D E) (G : DGFunctor A E T) (hL : localHomKFlat A L)

-- D・E・Tの局所Hom K-flat性やF・Gの準同値性を仮定せず、実際の導来比較の合成則を検査する。
example (P : BimoduleCategory A B T) (Q : RightKFlatBimoduleCategory A T L)
    (R : RightKFlatBimoduleCategory A E L) (S : RightKFlatBimoduleCategory A D L)
    (r : S.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A E D L F).obj R.obj)
    (q : R.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A T E L G).obj Q.obj)
    (hr : BimoduleCategory.quasiIso A D L r) (hq : BimoduleCategory.quasiIso A E L q) :
    (derivedMiddleCompositeSourceIso A B D L hL E T F G P Q.obj R.obj q hq).hom ≫
        derivedMiddleRestrictionComparison A B T D L (F.comp G) hL P Q S
          (BimoduleCategory.resolvedRestrictionAugmentationComp A D E T L F G r q)
          (BimoduleCategory.resolvedRestrictionAugmentationComp_quasiIso
            A D E T L F G r q hr hq) =
      derivedMiddleRestrictionComparison A B E D L F hL
          ((BimoduleCategory.middleLeftRestrictionFunctor A B T E G).obj P) R S r hr ≫
        ((derivedBimoduleComposeFunctor A B E L hL).map ((bimoduleToDerived A E L).map q)).app
          ((bimoduleToDerived A B E).obj
            ((BimoduleCategory.middleLeftRestrictionFunctor A B T E G).obj P)) ≫
        derivedMiddleRestrictionComparison A B T E L G hL P Q R q hq :=
  derivedMiddleRestrictionComparison_functor_comp A B D L hL E T F G P Q R S r q hr hq

-- 任意の指定モデルでの恒等則。前因子PにK-flat性は不要。
example (P : BimoduleCategory A B D) (Q R : RightKFlatBimoduleCategory A D L)
    (q : R.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A D D L (DGFunctor.id D)).obj
      Q.obj) (hq : BimoduleCategory.quasiIso A D L q) :
    derivedMiddleRestrictionComparison A B D D L (DGFunctor.id D) hL P Q R q hq =
      (derivedMiddleIdentitySourceIso A B D L hL P Q.obj).hom :=
  derivedMiddleRestrictionComparison_functor_id A B D L hL P Q R q hq

-- 合成への直接の標準解像度と二段階の標準解像度の間に、追加の比較squareを要求しない。
example (P : BimoduleCategory A B T) (Q : RightKFlatBimoduleCategory A T L) :
    let R := bimoduleCanonicalSemifreeResolution A E L
      ((BimoduleCategory.middleRightRestrictionFunctor A T E L G).obj Q.obj)
    (derivedMiddleCompositeSourceIso A B D L hL E T F G P Q.obj R.obj R.π R.quasiIso).hom ≫
        derivedMiddleRestrictionCanonicalComparison A B T D L (F.comp G) hL P Q =
      derivedMiddleRestrictionCanonicalComparison A B E D L F hL
          ((BimoduleCategory.middleLeftRestrictionFunctor A B T E G).obj P)
          (R.toRightKFlat A E L hL) ≫
        ((derivedBimoduleComposeFunctor A B E L hL).map ((bimoduleToDerived A E L).map R.π)).app
          ((bimoduleToDerived A B E).obj
            ((BimoduleCategory.middleLeftRestrictionFunctor A B T E G).obj P)) ≫
        derivedMiddleRestrictionCanonicalComparison A B T E L G hL P Q :=
  derivedMiddleRestrictionCanonicalComparison_functor_comp A B D E T L F G hL P Q

example (X : Type v) (Y : Type w) (Z : Type z)
    [DGCategory (ZMod 2) X] [DGCategory (ZMod 2) Y] [DGCategory (ZMod 2) Z]
    [Small.{0} X] [Small.{0} Y] [Small.{0} Z] (hZ : localHomKFlat (ZMod 2) Z)
    (P : BimoduleCategory (ZMod 2) X Y) (Q : RightKFlatBimoduleCategory (ZMod 2) Y Z) :
    derivedMiddleRestrictionCanonicalComparison (ZMod 2) X Y Y Z (DGFunctor.id Y) hZ P Q =
      (derivedMiddleIdentitySourceIso (ZMod 2) X Y Z hZ P Q.obj).hom :=
  derivedMiddleRestrictionCanonicalComparison_functor_id (ZMod 2) X Y Z hZ P Q

namespace SerrePositivity.DifferentialGraded
#print axioms BalancedTensor.resolvedRestrictionAugmentationComp
#print axioms BalancedTensor.resolvedRestrictionAugmentationComp_eval
#print axioms BalancedTensor.resolvedRestrictionAugmentationComp_quasiIso
#print axioms BalancedTensor.restrictionLeft_comp_assoc
#print axioms BalancedTensor.resolvedRestrictionCompTensorIso
#print axioms BalancedTensor.ι_resolvedRestrictionCompTensorIso_hom
#print axioms BalancedTensor.resolvedRestrictionComparison_comp
#print axioms BalancedTensor.restrictionLeft_id
#print axioms BalancedTensor.resolvedRestrictionIdTensorIso
#print axioms BalancedTensor.ι_resolvedRestrictionIdTensorIso_hom
#print axioms BalancedTensor.resolvedRestrictionAugmentationId
#print axioms BalancedTensor.resolvedRestrictionAugmentationId_eval
#print axioms BalancedTensor.resolvedRestrictionComparison_id
#print axioms BimoduleCategory.isoFamily_naturality_of_values
#print axioms BimoduleCategory.isoOfValueFamily
#print axioms BimoduleCategory.isoOfValueFamily_hom_eval
#print axioms BimoduleCategory.middleLeftRestrictionIdObjIso
#print axioms BimoduleCategory.middleLeftRestrictionIdObjIso_hom_eval
#print axioms BimoduleCategory.middleLeftRestrictionIdIso
#print axioms BimoduleCategory.middleLeftRestrictionCompObjIso
#print axioms BimoduleCategory.middleLeftRestrictionCompObjIso_hom_eval
#print axioms BimoduleCategory.middleLeftRestrictionCompIso
#print axioms BimoduleCategory.middleRightRestrictionIdObjIso
#print axioms BimoduleCategory.middleRightRestrictionIdObjIso_hom_value
#print axioms BimoduleCategory.middleRightRestrictionIdIso
#print axioms BimoduleCategory.middleRightRestrictionCompObjIso
#print axioms BimoduleCategory.middleRightRestrictionCompObjIso_hom_value
#print axioms BimoduleCategory.middleRightRestrictionCompIso
#print axioms BimoduleCategory.middleRightRestrictionCompositeMap
#print axioms BimoduleCategory.middleRightRestrictionCompositeMap_value
#print axioms BimoduleCategory.middleRightRestrictionCompositeMap_quasiIso
#print axioms BimoduleCategory.resolvedRestrictionAugmentationComp
#print axioms BimoduleCategory.resolvedRestrictionAugmentationComp_value
#print axioms BimoduleCategory.resolvedRestrictionAugmentationComp_quasiIso
#print axioms BimoduleCategory.resolvedRestrictionAugmentationId
#print axioms BimoduleCategory.resolvedRestrictionAugmentationId_value
#print axioms BimoduleCategory.resolvedRestrictionAugmentationId_quasiIso
#print axioms BimoduleTensor.middleLeftRestrictionCompObjIso_hom_value
#print axioms BimoduleTensor.middleRestrictionCompSourceIso
#print axioms BimoduleTensor.ι_middleRestrictionCompSourceIso_hom_value
#print axioms BimoduleTensor.ι_middleRestrictionResolvedMap_value
#print axioms BimoduleTensor.middleRestrictionResolvedMap_functor_comp
#print axioms BimoduleTensor.middleLeftRestrictionIdObjIso_hom_value
#print axioms BimoduleTensor.middleRestrictionIdSourceIso
#print axioms BimoduleTensor.ι_middleRestrictionIdSourceIso_hom_value
#print axioms BimoduleTensor.middleRestrictionResolvedMap_functor_id
#print axioms BimoduleTensor.middleRestrictionResolvedMap_functor_id_exchange
#print axioms BimoduleTensor.derivedBimoduleComposeKFlatValueIso_first_naturality
#print axioms BimoduleTensor.derivedBimoduleComposeResolutionValueIso_self
#print axioms BimoduleTensor.derivedMiddleIdentitySourceIso
#print axioms BimoduleTensor.derivedMiddleRestrictionComparison_functor_id
#print axioms BimoduleTensor.derivedBimoduleComposeResolutionValueIso_first_naturality
#print axioms BimoduleTensor.derivedBimoduleComposeResolutionValueIso_fac
#print axioms BimoduleTensor.derivedMiddleCompositeSourceIso
#print axioms BimoduleTensor.derivedMiddleCompositeSourceIso_computation
#print axioms BimoduleTensor.derivedMiddleRestrictionComparison_functor_comp
#print axioms BimoduleSemifreeResolution.postcompose
#print axioms BimoduleSemifreeResolution.postcompose_obj
#print axioms BimoduleTensor.derivedMiddleRestrictionCanonicalComparison_functor_comp
#print axioms BimoduleTensor.derivedMiddleRestrictionCanonicalComparison_functor_id
end SerrePositivity.DifferentialGraded
