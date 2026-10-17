module
public import SerrePositivity.DifferentialGraded.Derived.RightUnitRestrictionCoherence
public import Mathlib.Data.ZMod.Basic

/-! # 右単位子・制限比較と任意K-flat解像度のモデル独立性の検査

## 概要
右単位子・制限比較と任意K-flat解像度のモデル独立性の検査。

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
universe u v w z t
open CategoryTheory CategoryTheory.Functor
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensor

section General
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D] (F : DGFunctor A D C)

-- Cの局所Hom条件やFの本質的全射性は不要。前因子は任意の導来対象。
example (hD : localHomKFlat A D) (hF : HomQuasiIso F)
    (P : DerivedBimoduleCategory A B C) :
    (rightUnitRestrictionDerivedComparison A B C D F hD).app P =
      (derivedBimoduleRightUnitIso A B D hD).hom.app
        ((derivedBimoduleRestriction A B D B C (DGFunctor.id B) F).obj P) :=
  NatTrans.congr_app (rightUnitRestrictionDerivedComparison_eq A B C D F hD hF) P

variable (E : Type t) [DGCategory A E] [Small.{u} E]

-- 解像度は右相対K-flatであればよく、semifree性やHomのA-flat性を追加しない。
example (hE : localHomKFlat A E) (Q : RightKFlatBimoduleCategory A C E)
    (R : RightKFlatBimoduleCategory A D E)
    (q : R.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj)
    (hq : BimoduleCategory.quasiIso A D E q) (P : BimoduleCategory A B C) :
    derivedMiddleRestrictionComparison A B C D E F hE P Q R q hq =
      derivedMiddleRestrictionCanonicalComparison A B C D E F hE P Q :=
  derivedMiddleRestrictionComparison_kFlat_eq_canonical A B C D E F hE Q R q hq P
end General

example (B : Type v) [DGCategory (ZMod 2) B] [Small.{0} B]
    (C : Type w) [DGCategory (ZMod 2) C] [Small.{0} C]
    (D : Type z) [DGCategory (ZMod 2) D] [Small.{0} D]
    (F : DGFunctor (ZMod 2) D C) (hD : localHomKFlat (ZMod 2) D)
    (hF : HomQuasiIso F) :
    rightUnitRestrictionDerivedComparison (ZMod 2) B C D F hD =
      whiskerLeft (derivedBimoduleRestriction (ZMod 2) B D B C (DGFunctor.id B) F)
        (derivedBimoduleRightUnitIso (ZMod 2) B D hD).hom :=
  rightUnitRestrictionDerivedComparison_eq (ZMod 2) B C D F hD hF

#print axioms rightUnitRestriction_value
#print axioms rightUnitRestriction
#print axioms composeAfter_bimoduleCanonicalResolutionLift_fac
#print axioms derivedMiddleRestrictionComparison_kFlat_eq_canonical
#print axioms rightUnitRestriction_source_computation
#print axioms derivedRightUnitRestriction_model
#print axioms rightUnitRestrictionMiddleMap
#print axioms rightUnitRestrictionDerivedComparison
#print axioms rightUnitRestriction_source_identification
#print axioms rightUnitRestrictionMiddleMap_base_fac
#print axioms rightUnitRestriction_target_calculation
#print axioms rightUnitRestrictionDerivedComparison_base_fac
#print axioms rightUnitRestrictionDerivedComparison_eq
