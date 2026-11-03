module
public import SerrePositivity.DifferentialGraded.Derived.Bimodule
public import Mathlib.Data.ZMod.Basic

/-! # 右K-flatモデルからの移送の計算と外側左制限のモデル一致の検査

## 概要
右K-flatモデルからの移送の計算と外側左制限のモデル一致の検査。

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
universe u v w z t k k'
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensor
variable (A : Type u) [CommRing A] (C : Type v) [DGCategory A C] [Small.{u} C]
  (E : Type w) [DGCategory A E] [Small.{u} E] (hE : localHomKFlat A E)
  {T : Type k} [Category.{k'} T]

-- 値域の対象宇宙とHom宇宙は、dg圏・環の宇宙から独立。
example (G H : DerivedBimoduleCategory A C E ⥤ T)
    (e : rightKFlatInclusion A C E ⋙ bimoduleToDerived A C E ⋙ G ≅
      rightKFlatInclusion A C E ⋙ bimoduleToDerived A C E ⋙ H)
    (Q : RightKFlatBimoduleCategory A C E) :
    (rightKFlatDerivedIsoOfPrecomp A C E hE G H e).hom.app
        ((bimoduleToDerived A C E).obj Q.obj) = e.hom.app Q :=
  rightKFlatDerivedIsoOfPrecomp_hom_app A C E hE G H e Q

example (U V W : DerivedBimoduleCategory A C E ⥤ T)
    (e₁ : rightKFlatInclusion A C E ⋙ bimoduleToDerived A C E ⋙ U ≅
      rightKFlatInclusion A C E ⋙ bimoduleToDerived A C E ⋙ V)
    (e₂ : rightKFlatInclusion A C E ⋙ bimoduleToDerived A C E ⋙ V ≅
      rightKFlatInclusion A C E ⋙ bimoduleToDerived A C E ⋙ W) :
    rightKFlatDerivedIsoOfPrecomp A C E hE U W (e₁ ≪≫ e₂) =
      rightKFlatDerivedIsoOfPrecomp A C E hE U V e₁ ≪≫
        rightKFlatDerivedIsoOfPrecomp A C E hE V W e₂ :=
  rightKFlatDerivedIsoOfPrecomp_trans A C E hE U V W e₁ e₂

-- 前因子は任意の導来対象、Cの局所Hom K-flat性とFの準同値性は不要。
example (B : Type z) [DGCategory A B] [Small.{u} B]
    (D : Type t) [DGCategory A D] [Small.{u} D] (F : DGFunctor A D E)
    (hD : localHomKFlat A D) (Q : RightKFlatBimoduleCategory A C E)
    (P : DerivedBimoduleCategory A B C) :
    ((derivedBimoduleComposeLeftRestrictionIso A B C E D F hE hD).hom.app
        ((bimoduleToDerived A C E).obj Q.obj)).app P ≫
        ((leftRestrictionDerivedComposeTargetBaseIso A B C E D F hD).hom.app Q).app P =
      ((leftRestrictionDerivedComposeSourceBaseIso A B C E D F hE).hom.app Q).app P ≫
        (derivedComposeWithLeftRestrictionIso A B C E D F Q).inv.app P :=
  derivedBimoduleComposeLeftRestrictionIso_model_square_app A B C E D F hE hD Q P

example (X : Type v) (Y : Type w) [DGCategory (ZMod 2) X] [DGCategory (ZMod 2) Y]
    [Small.{0} X] [Small.{0} Y] (hY : localHomKFlat (ZMod 2) Y)
    (U : DerivedBimoduleCategory (ZMod 2) X Y ⥤ T) :
    rightKFlatDerivedIsoOfPrecomp (ZMod 2) X Y hY U U (Iso.refl _) = Iso.refl U :=
  rightKFlatDerivedIsoOfPrecomp_refl (ZMod 2) X Y hY U

#print axioms BimoduleTensor.rightKFlatLocalizedIsoOfPrecomp
#print axioms BimoduleTensor.rightKFlatDerivedIsoOfPrecomp
#print axioms BimoduleTensor.rightKFlatComposePresentationIso
#print axioms BimoduleTensor.rightKFlatDerivedIsoOfPrecomp_conjugate
#print axioms BimoduleTensor.rightKFlatDerivedIsoOfPrecomp_app_inclusion
#print axioms BimoduleTensor.rightKFlatDerivedIsoOfPrecomp_hom_app
#print axioms BimoduleTensor.rightKFlatDerivedIsoOfPrecomp_precomp
#print axioms BimoduleTensor.rightKFlatDerivedNatTrans_ext
#print axioms BimoduleTensor.rightKFlatDerivedIsoOfPrecomp_refl
#print axioms BimoduleTensor.rightKFlatDerivedIsoOfPrecomp_trans
#print axioms BimoduleTensor.rightKFlatDerivedIsoOfPrecomp_whiskerRight
#print axioms BimoduleTensor.derivedBimoduleComposeLeftRestrictionIso_precomp
#print axioms BimoduleTensor.derivedBimoduleComposeLeftRestrictionIso_app_rightKFlat
#print axioms BimoduleTensor.derivedBimoduleComposeLeftRestrictionIso_model_square
#print axioms BimoduleTensor.derivedBimoduleComposeLeftRestrictionIso_model_square_app
#print axioms BimoduleTensor.derivedBimoduleComposeLeftRestriction_hom_unique
