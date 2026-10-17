module
public import SerrePositivity.DifferentialGraded.Resolution.InitialComparison
public import SerrePositivity.DifferentialGraded.Resolution.CellSequence
public import SerrePositivity.DifferentialGraded.Resolution.FixedObjectMap

/-! # 標準解像度の初期段階の増大比較

## 概要
標準解像度の初期段階の増大比較。

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
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]
  {E : Type w} [DGCategory A E]

lemma DGFunctor.hcongr_map {F G : DGFunctor A D E} (h : F = G) (x y : D) :
    HEq (F.map x y) (G.map x y) := by
  cases h
  rfl

namespace DGCategoryCellResolution
variable (A D E) [Small.{u} D] [Small.{u} E] (F : DGFunctor A D E)

def initialComparison : FixedObjectAugmentation.Map (initial A D) (initial A E) F where
  hom x y := (DGCategoryCycleCover.map A D E F).map x y
  map_id x := (DGCategoryCycleCover.map A D E F).map_id x
  map_comp x y z := (DGCategoryCycleCover.map A D E F).map_comp x y z
  augmentation x y := eq_of_heq
    (DGFunctor.hcongr_map (DGCategoryCycleCover.map_augmentation A D E F) x y)

end DGCategoryCellResolution
end SerrePositivity.DifferentialGraded
