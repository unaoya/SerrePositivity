module
public import SerrePositivity.DifferentialGraded.Resolution.CellComparison
public import SerrePositivity.DifferentialGraded.Functor.QuasiIsoHomology

/-! # 準同値に沿う標準解像度の準同値比較

## 概要
準同値に沿う標準解像度の準同値比較。

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
namespace SerrePositivity.DifferentialGraded.DGCategoryCellResolution
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

lemma comparisonFunctor_essSurj (hF : F.onHomotopy.EssSurj) :
    (comparisonFunctor A D E F).onHomotopy.EssSurj := by
  let : (augmentation A D).onHomotopy.EssSurj := augmentation_essSurj A D
  let : F.onHomotopy.EssSurj := hF
  let : (augmentation A E).onHomotopy.Full :=
    (augmentation A E).onHomotopy_full_of_homQuasiIso (augmentation_homQuasiIso A E)
  let : (augmentation A E).onHomotopy.Faithful :=
    (augmentation A E).onHomotopy_faithful_of_homQuasiIso (augmentation_homQuasiIso A E)
  have hs : (comparisonFunctor A D E F).onHomotopy ⋙ (augmentation A E).onHomotopy =
      (augmentation A D).onHomotopy ⋙ F.onHomotopy := by
    rw [← DGFunctor.onHomotopy_comp, comparisonFunctor_augmentation, DGFunctor.onHomotopy_comp]
  have : ((comparisonFunctor A D E F).onHomotopy ⋙
      (augmentation A E).onHomotopy).EssSurj := by
    rw [hs]
    infer_instance
  exact Functor.essSurj_of_comp_fully_faithful _ (augmentation A E).onHomotopy

lemma comparisonFunctor_quasiEquivalence (hF : QuasiEquivalence F) :
    QuasiEquivalence (comparisonFunctor A D E F) :=
  ⟨comparisonFunctor_homQuasiIso A D E F hF.1, comparisonFunctor_essSurj A D E F hF.2⟩

end SerrePositivity.DifferentialGraded.DGCategoryCellResolution
