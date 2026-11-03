module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddle.IteratedModels
public import Mathlib.Data.ZMod.Basic

/-! # 導来制限の合成正規化と二段階全導来比較の検査

## 概要
導来制限の合成正規化と二段階全導来比較の検査。

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

-- 中間圏D・E・Tの局所Hom K-flat性とF・Gの準同値性は不要。
example : middleIteratedDerivedSource A B D E T L F G hL ≅
    middleRestrictionDerivedSource A B T D L (F.comp G) hL :=
  middleIteratedDerivedSourceIso A B D E T L F G hL

-- 後因子も前因子も任意の導来対象であり、元の閉零対象に限定しない。
example (Q : DerivedBimoduleCategory A T L) (P P' : DerivedBimoduleCategory A B T)
    (f : P ⟶ P') :
    ((middleIteratedDerivedSource A B D E T L F G hL).obj Q).map f ≫
        ((middleIteratedDerivedComparison A B D E T L F G hL).app Q).app P' =
      ((middleIteratedDerivedComparison A B D E T L F G hL).app Q).app P ≫
        ((derivedBimoduleComposeFunctor A B T L hL).obj Q).map f :=
  ((middleIteratedDerivedComparison A B D E T L F G hL).app Q).naturality f

example {U V : DerivedBimoduleCategory A T L ⥤
    (DerivedBimoduleCategory A B T ⥤ DerivedBimoduleCategory A B L)} {α β : U ⟶ V}
    (h : ∀ (Q : RightKFlatBimoduleCategory A T L) (P : BimoduleCategory A B T),
      (α.app ((bimoduleToDerived A T L).obj Q.obj)).app
          ((bimoduleToDerived A B T).obj P) =
        (β.app ((bimoduleToDerived A T L).obj Q.obj)).app
          ((bimoduleToDerived A B T).obj P)) : α = β :=
  middleDerivedFamily_ext A B T L hL h

example (X : Type v) (Y : Type w) (Z : Type z)
    [DGCategory (ZMod 2) X] [DGCategory (ZMod 2) Y] [DGCategory (ZMod 2) Z]
    [Small.{0} X] [Small.{0} Y] [Small.{0} Z]
    (F' : DGFunctor (ZMod 2) X Y) (G' : DGFunctor (ZMod 2) Y Z) :
    derivedBimoduleRestriction (ZMod 2) Y X Z X G' (DGFunctor.id X) ⋙
        derivedBimoduleRestriction (ZMod 2) X X Y X F' (DGFunctor.id X) ≅
      derivedBimoduleRestriction (ZMod 2) X X Z X (F'.comp G') (DGFunctor.id X) :=
  middleRightDerivedCompIso (ZMod 2) X X Y Z F' G'

#print axioms middleLeftDerivedCompPreIso
#print axioms middleLeftDerivedCompIso
#print axioms middleLeftDerivedCompIso_hom_app
#print axioms middleRightDerivedCompPreIso
#print axioms middleRightDerivedCompIso
#print axioms middleRightDerivedCompIso_hom_app
#print axioms middleLeftDerivedCompIso_presentation
#print axioms middleRightDerivedCompIso_presentation
#print axioms middleLeftDerivedCompIso_precomp
#print axioms middleRightDerivedCompIso_precomp
#print axioms BimoduleTensor.middleIteratedDerivedSource
#print axioms BimoduleTensor.middleIteratedDerivedSourceIso
#print axioms BimoduleTensor.middleIteratedDerivedComparison
#print axioms BimoduleTensor.middleIteratedDerivedSourceIso_hom_app
#print axioms BimoduleTensor.middleIteratedDerivedComparison_app
#print axioms BimoduleTensor.middleDerivedFamily_ext
