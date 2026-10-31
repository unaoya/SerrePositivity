module
public import SerrePositivity.DifferentialGraded.Resolution.DiagonalComparison
public import Mathlib.Data.ZMod.Basic

/-! # 対角制限と既存解像度変更の対角保存の検査

## 概要
対角制限と既存解像度変更の対角保存の検査。

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
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensor

section Restriction
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

-- 比較の値はF自身のHom写像であり、条件は本質的全射性を含まない。
example (b d : D) :
    (BimoduleCategory.valueEvaluation A D D b d).map
        (Bimodule.diagonalRestrictionMap A D E F) = F.map b d :=
  Bimodule.diagonalRestrictionMap_value A D E F b d

example : BimoduleCategory.quasiIso A D D (Bimodule.diagonalRestrictionMap A D E F) ↔
    HomQuasiIso F :=
  Bimodule.diagonalRestrictionMap_quasiIso_iff A D E F

-- どちらの圏にも局所Hom K-flat性を追加せず、既存の導来制限上の同型を得る。
example (hF : HomQuasiIso F) :
    (bimoduleToDerived A D D).obj (rightKFlatDiagonal A D).obj ≅
      (derivedBimoduleRestriction A D D E E F F).obj
        ((bimoduleToDerived A E E).obj (rightKFlatDiagonal A E).obj) :=
  derivedDiagonalRestrictionIso A D E F hF
end Restriction

section Resolutions
open SerrePositivity.DifferentialGraded.ResolutionBimodule
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

-- 元の対象型のsmallnessは比較左脚に不要。
example (P : KFlatDGResolution.{u, v, w} A D) :
    (comparisonLeft A P P).obj (diagonal A P) ≅ comparisonDiagonal A P :=
  comparisonLeftDiagonalIso A P

variable [Small.{u} D]

-- 指定した既存changeEquivalenceを使い、変更前後のsource宇宙は独立。
example (P : KFlatDGResolution.{u, v, w} A D)
    (Q : KFlatDGResolution.{u, v, z} A D) :
    (changeEquivalence A P P Q Q).functor.obj (diagonal A P) ≅ diagonal A Q :=
  changeDiagonalIso A P Q
end Resolutions

example (D : Type v) [DGCategory (ZMod 2) D] [Small.{0} D]
    (E : Type w) [DGCategory (ZMod 2) E] [Small.{0} E]
    (F : DGFunctor (ZMod 2) D E) (hF : HomQuasiIso F) :
    IsIso (derivedDiagonalRestrictionMap (ZMod 2) D E F) :=
  derivedDiagonalRestrictionMap_isIso (ZMod 2) D E F hF

#print axioms Bimodule.diagonalRestriction_leftAt_map
#print axioms Bimodule.diagonalRestriction_value_left_naturality
#print axioms Bimodule.diagonalRestrictionMap
#print axioms Bimodule.diagonalRestrictionMap_value
#print axioms Bimodule.diagonalRestrictionMap_quasiIso_iff
#print axioms derivedDiagonalRestrictionMap
#print axioms derivedDiagonalRestrictionIso
#print axioms derivedDiagonalRestrictionIso_hom
#print axioms derivedDiagonalRestrictionMap_isIso
#print axioms ResolutionBimodule.comparisonDiagonal
#print axioms ResolutionBimodule.comparisonLeftDiagonalIso
#print axioms ResolutionBimodule.comparisonRightDiagonalIso
#print axioms ResolutionBimodule.canonicalComparisonDiagonalIso
#print axioms ResolutionBimodule.changeDiagonalIso
