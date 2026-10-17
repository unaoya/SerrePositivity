module
public import SerrePositivity.DifferentialGraded.Derived.DiagonalRestrictionCoherence
public import Mathlib.Data.ZMod.Basic

/-! # 対角比較と両端制限の恒等・合成整合性の検査

## 概要
対角比較と両端制限の恒等・合成整合性の検査。

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
universe u v w z t s r
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensor

section Paired
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (E : Type z) [DGCategory A E] [Small.{u} E]
  (L : Type t) [DGCategory A L] [Small.{u} L]
  (D : Type s) [DGCategory A D] [Small.{u} D]
  (K : Type r) [DGCategory A K] [Small.{u} K]
  (F : DGFunctor A D E) (G : DGFunctor A E B)
  (H : DGFunctor A K L) (I : DGFunctor A L C)

-- 六宇宙の両端制限の合成比較。flatness・準同値性の仮定はない。
example (M : DerivedBimoduleCategory A B C) :
    (derivedBimoduleRestriction A D K E L F H).obj
        ((derivedBimoduleRestriction A E L B C G I).obj M) ≅
      (derivedBimoduleRestriction A D K B C (F.comp G) (H.comp I)).obj M :=
  (pairedRestrictionCompDerivedIso A B C E L D K F G H I).app M

example (M : DerivedBimoduleCategory A B C) :
    (derivedBimoduleRestriction A B C B C (DGFunctor.id B) (DGFunctor.id C)).obj M ≅ M :=
  (pairedRestrictionIdDerivedIso A B C).app M
end Paired

-- 標数2でも、任意の二つのdg関手で実際の導来対角比較射の合成則が成り立つ。
example (D : Type v) [DGCategory (ZMod 2) D] [Small.{0} D]
    (E : Type w) [DGCategory (ZMod 2) E] [Small.{0} E]
    (T : Type z) [DGCategory (ZMod 2) T] [Small.{0} T]
    (F : DGFunctor (ZMod 2) D E) (G : DGFunctor (ZMod 2) E T) :
    derivedDiagonalRestrictionMap (ZMod 2) D E F ≫
        (derivedBimoduleRestriction (ZMod 2) D D E E F F).map
          (derivedDiagonalRestrictionMap (ZMod 2) E T G) ≫
        (pairedRestrictionCompDerivedIso (ZMod 2) T T E E D D F G F G).hom.app
          ((bimoduleToDerived (ZMod 2) T T).obj (rightKFlatDiagonal (ZMod 2) T).obj) =
      derivedDiagonalRestrictionMap (ZMod 2) D T (F.comp G) :=
  derivedDiagonalRestrictionMap_comp (ZMod 2) D E T F G

#print axioms BimoduleCategory.pairedRestrictionIdObjIso
#print axioms BimoduleCategory.pairedRestrictionIdObjIso_hom_value
#print axioms BimoduleCategory.pairedRestrictionIdIso
#print axioms BimoduleCategory.pairedRestrictionCompObjIso
#print axioms BimoduleCategory.pairedRestrictionCompObjIso_hom_value
#print axioms BimoduleCategory.pairedRestrictionCompIso
#print axioms Bimodule.diagonalRestrictionMap_id
#print axioms Bimodule.diagonalRestrictionMap_comp
#print axioms pairedRestrictionIdDerivedPreIso
#print axioms pairedRestrictionIdDerivedIso
#print axioms pairedRestrictionIdDerivedIso_hom_app
#print axioms pairedRestrictionCompDerivedPreIso
#print axioms pairedRestrictionCompDerivedIso
#print axioms pairedRestrictionCompDerivedIso_hom_app
#print axioms derivedDiagonalRestrictionMap_id
#print axioms derivedDiagonalRestrictionMap_comp
