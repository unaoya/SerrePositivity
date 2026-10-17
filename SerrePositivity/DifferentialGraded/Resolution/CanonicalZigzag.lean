module
public import SerrePositivity.DifferentialGraded.Resolution.CellComparisonQuasiEquivalence

/-! # 任意の指定K-flat解像度と標準解像度の準同値zigzag

## 概要
P.source ← 標準解像度(P.source) → 標準解像度(D) はDへの増大と可換する。

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
universe u v w
namespace SerrePositivity.DifferentialGraded.KFlatDGResolution
open CategoryTheory
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] [Small.{u} D]
  (P : KFlatDGResolution.{u, v, w} A D)

abbrev ComparisonSource : Type w := DGCategoryCellResolution.Source A P.source

def comparisonLeft : DGFunctor A P.ComparisonSource P.source :=
  DGCategoryCellResolution.augmentation A P.source

def comparisonRight : DGFunctor A P.ComparisonSource (canonical A D).source :=
  DGCategoryCellResolution.comparisonFunctor A P.source D P.augmentation

omit [Small.{u} D] in
lemma comparisonLeft_quasiEquivalence : QuasiEquivalence P.comparisonLeft :=
  DGCategoryCellResolution.augmentation_quasiEquivalence A P.source

lemma comparisonRight_quasiEquivalence : QuasiEquivalence P.comparisonRight :=
  DGCategoryCellResolution.comparisonFunctor_quasiEquivalence A P.source D P.augmentation
    P.quasiEquivalence

omit [Small.{u} D] in
lemma comparisonSource_homKFlat : localHomKFlat A P.ComparisonSource :=
  DGCategoryCellResolution.source_homKFlat A P.source

/-- zigzagの両脚はDへの増大と厳密に可換する。 -/
lemma comparison_augmentation :
    P.comparisonRight.comp (canonical A D).augmentation = P.comparisonLeft.comp P.augmentation :=
  DGCategoryCellResolution.comparisonFunctor_augmentation A P.source D P.augmentation

end SerrePositivity.DifferentialGraded.KFlatDGResolution
