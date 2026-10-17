module
public import SerrePositivity.DifferentialGraded.Resolution.Restriction
public import SerrePositivity.DifferentialGraded.Derived.BimoduleRestrictionEquivalence

/-! # 指定解像度の導来bimodule圏を標準zigzagで比較する同値

## 概要
指定解像度の導来bimodule圏を標準zigzagで比較する同値。

## 方針
指定の共通source・準同値・局所化の比較を使い、既存の比較関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。Hom非平坦のdg圏のMorita・tensor・Hochschild型構成・K理論で、分解選択を比較する入口。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
universe u v w v' w' z' t'
namespace SerrePositivity.DifferentialGraded.ResolutionBimodule
open CategoryTheory
variable (A : Type u) [CommRing A] {B : Type v} [DGCategory A B]
  {C : Type w} [DGCategory A C]

/-- 比較zigzagの左脚の、既存の導来制限を順方向とする同値。 -/
def comparisonLeftEquivalence (P : KFlatDGResolution.{u, v, v'} A B)
    (Q : KFlatDGResolution.{u, w, w'} A C) :
    DerivedCategory A P Q ≌ DerivedBimoduleCategory A P.ComparisonSource Q.ComparisonSource :=
  derivedBimoduleRestrictionEquivalence A P.ComparisonSource Q.ComparisonSource P.source Q.source
    P.comparisonLeft Q.comparisonLeft P.comparisonLeft_quasiEquivalence
    Q.comparisonLeft_quasiEquivalence Q.comparisonSource_homKFlat P.homKFlat

lemma comparisonLeftEquivalence_functor (P : KFlatDGResolution.{u, v, v'} A B)
    (Q : KFlatDGResolution.{u, w, w'} A C) :
    (comparisonLeftEquivalence A P Q).functor = comparisonLeft A P Q := rfl

variable [Small.{u} B] [Small.{u} C]

/-- 比較zigzagの右脚の、標準解像度側からの既存導来制限を順方向とする同値。 -/
def comparisonRightEquivalence (P : KFlatDGResolution.{u, v, v'} A B)
    (Q : KFlatDGResolution.{u, w, w'} A C) :
    DerivedCategory A (KFlatDGResolution.canonical A B) (KFlatDGResolution.canonical A C) ≌
      DerivedBimoduleCategory A P.ComparisonSource Q.ComparisonSource :=
  derivedBimoduleRestrictionEquivalence A P.ComparisonSource Q.ComparisonSource
    (KFlatDGResolution.canonical A B).source (KFlatDGResolution.canonical A C).source
    P.comparisonRight Q.comparisonRight P.comparisonRight_quasiEquivalence
    Q.comparisonRight_quasiEquivalence Q.comparisonSource_homKFlat
    (KFlatDGResolution.canonical A B).homKFlat

lemma comparisonRightEquivalence_functor (P : KFlatDGResolution.{u, v, v'} A B)
    (Q : KFlatDGResolution.{u, w, w'} A C) :
    (comparisonRightEquivalence A P Q).functor = comparisonRight A P Q := rfl

/-- 任意の指定解像度の導来bimodule圏から標準解像度の導来bimodule圏への比較。 -/
def canonicalComparisonEquivalence (P : KFlatDGResolution.{u, v, v'} A B)
    (Q : KFlatDGResolution.{u, w, w'} A C) :
    DerivedCategory A P Q ≌
      DerivedCategory A (KFlatDGResolution.canonical A B) (KFlatDGResolution.canonical A C) :=
  (comparisonLeftEquivalence A P Q).trans (comparisonRightEquivalence A P Q).symm

/-- 両側の指定解像度を同時に変更する、実際の導来bimodule圏の同値。 -/
def changeEquivalence (P : KFlatDGResolution.{u, v, v'} A B)
    (Q : KFlatDGResolution.{u, w, w'} A C) (R : KFlatDGResolution.{u, v, z'} A B)
    (S : KFlatDGResolution.{u, w, t'} A C) : DerivedCategory A P Q ≌ DerivedCategory A R S :=
  (canonicalComparisonEquivalence A P Q).trans (canonicalComparisonEquivalence A R S).symm

end SerrePositivity.DifferentialGraded.ResolutionBimodule
