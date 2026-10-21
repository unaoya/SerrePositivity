module

public import SerrePositivity.InfinityCategories.F1.CocartesianIsoTransportFamilyVertex
public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeNativeAssociativityEdge

/-!
概要：全局所 Hom の比較の区間族は、元の対象では既存の結合比較の同じ辺となる。
方針：底全体の頂点の一致を同じ prism の辺へ渡す。
規約：元の結合比較辺と分類主写像を保持する。
使われ方：全局所 Hom から既存の結合 Hom span への比較。
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

/-- 元の対象での全局所比較の辺は、既存の結合区間族の同じ一単体。 -/
lemma cocartesianIsoTransportFamily_native_edge :
    (((SSet.Edge.ofTruncated homotopyIntervalEdge).map
      (transposeFunctorFamily (cocartesianIsoTransportFamily A ≫ qCatDiagramArrowCurry A))).map
        (evaluateFunctorAt (coherentNerveVertex (show CocartesianIsoTransportCategory A from
          cocartesianBaseChangeIsoTransportObject l k p)))).edge =
    (functorEdgeAt (cocartesianBaseChangeAssociativityEdge l k) (coherentNerveVertex p)).edge := by
  have h := qCatDiagramArrowFamily_edgeAt (C := A) (U := CocartesianIsoTransportInfinity A)
    (cocartesianIsoTransportFamily A)
    (coherentNerveVertex (show CocartesianIsoTransportCategory A from
      cocartesianBaseChangeIsoTransportObject l k p))
    (cocartesianBaseChangeAssociativityQCat p.val.hom l k)
    (cocartesianIsoTransportFamily_native_vertex l k p)
  exact h.trans (cocartesianBaseChangeAssociativityEdge_at_object l k p).symm

end SerrePositivity.InfinityCategories
