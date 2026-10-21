module

public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeNativeCoherentEdge
public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeAssociativityDiagram
public import SerrePositivity.InfinityCategories.F1.QuasicategoryDiagramNaturalPrism

/-!
概要：元の全空間の結合同型の分類像は、既存の結合自然変換の prism の辺そのもの。
方針：同じ底全体の自然変換と、自然変換の辺の実現公式を使う。
規約：分類先の全図式で同じ元の辺を保持する。
使われ方：既存の結合区間族と元の Hom 輸送への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
  (l : A ⥤ D) (k : D ⥤ C) (p : CocartesianFibrationCategory (nerve C))

/-- 元の underlying 結合比較を QCat 値で読むと、既存の同じ自然変換になる。 -/
lemma cocartesianBaseChangeNativeDiagramTransformation_qCat :
    quasicategoryDiagramQCatTransformation
      (cocartesianBaseChangeNativeDiagramTransformation l k p) =
    cocartesianBaseChangeAssociativityQCat p.val.hom l k := rfl

/-- 同じ結合同型の分類像の辺は、既存の結合自然変換の元の prism の辺。 -/
lemma cocartesianBaseChangeNativeObjectIso_naturalPrism_edge :
    (cocartesianStraighteningCoherentMap A).app (Opposite.op ⦋1⦌)
      (coherentNerveEdge (cocartesianBaseChangeNativeObjectIso l k p).hom).edge =
    (qCatDiagramNaturalTransformationEdge
      (cocartesianBaseChangeAssociativityQCat p.val.hom l k)).edge := by
  have h := quasicategoryDiagramHom_realization_edge
    (cocartesianBaseChangeNativeDiagramTransformation l k p)
  have hη := congrArg (fun η ↦ (qCatDiagramNaturalTransformationEdge η).edge)
    (cocartesianBaseChangeNativeDiagramTransformation_qCat l k p)
  exact (cocartesianBaseChangeNativeObjectIso_classified_edge l k p).trans (h.trans hη)

end SerrePositivity.InfinityCategories
