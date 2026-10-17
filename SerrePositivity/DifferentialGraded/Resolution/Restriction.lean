module
public import SerrePositivity.DifferentialGraded.Resolution.CanonicalZigzag
public import SerrePositivity.DifferentialGraded.Resolution.Bimodule
public import SerrePositivity.DifferentialGraded.Derived.BimoduleRestrictionEvaluation

/-! # 解像度比較に沿う導来bimodule制限の実際の関手

## 概要
準同値zigzagの両脚から比較関手を得る。これらの同値性と合成比較は別の受入条件である。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
universe u v w v' w' z' t'
namespace SerrePositivity.DifferentialGraded.ResolutionBimodule
open CategoryTheory
variable (A : Type u) [CommRing A] {B : Type v} [DGCategory A B]
  {C : Type w} [DGCategory A C]

/-- 任意の解像度source間のdg関手に沿う導来bimodule制限。 -/
def restriction (P : KFlatDGResolution.{u, v, v'} A B)
    (Q : KFlatDGResolution.{u, w, w'} A C)
    (R : KFlatDGResolution.{u, v, z'} A B) (S : KFlatDGResolution.{u, w, t'} A C)
    (f : DGFunctor A R.source P.source) (g : DGFunctor A S.source Q.source) :
    DerivedCategory A P Q ⥤ DerivedCategory A R S :=
  derivedBimoduleRestriction A R.source S.source P.source Q.source f g

/-- 任意解像度から標準解像度比較の中間sourceへ制限する。 -/
def comparisonLeft (P : KFlatDGResolution.{u, v, v'} A B)
    (Q : KFlatDGResolution.{u, w, w'} A C) :
    DerivedCategory A P Q ⥤ DerivedBimoduleCategory A P.ComparisonSource Q.ComparisonSource :=
  derivedBimoduleRestriction A P.ComparisonSource Q.ComparisonSource P.source Q.source
    P.comparisonLeft Q.comparisonLeft

variable [Small.{u} B] [Small.{u} C]

/-- 元のdg圏の局所K-flat性を要求せず、標準解像度側から同じ中間圏へ制限する。 -/
def comparisonRight (P : KFlatDGResolution.{u, v, v'} A B)
    (Q : KFlatDGResolution.{u, w, w'} A C) :
    DerivedCategory A (KFlatDGResolution.canonical A B) (KFlatDGResolution.canonical A C) ⥤
      DerivedBimoduleCategory A P.ComparisonSource Q.ComparisonSource :=
  derivedBimoduleRestriction A P.ComparisonSource Q.ComparisonSource
    (KFlatDGResolution.canonical A B).source (KFlatDGResolution.canonical A C).source
    P.comparisonRight Q.comparisonRight

end SerrePositivity.DifferentialGraded.ResolutionBimodule
