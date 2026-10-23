module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.IsoTransportHomPath
public import SerrePositivity.InfinityCategories.F1.Cocartesian.IsoTransportFamilyEdge
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeAssociativityHomPath
public import SerrePositivity.InfinityCategories.F1.IntervalFamilyVertexEdge

/-!
概要：全局所 Hom の比較 path は、元の fibration では既存の結合 path そのもの。
方針：包含後の区間族を回収し、同じ評価辺による頂点の一意性を使う。
規約：既存の結合比較の代表と同じ path を保持する。
使われ方：元の全局所 Hom から同じ結合 Hom span への写像。
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

/-- 元の対象での全局所比較の path 頂点は、既存の結合 path 頂点そのもの。 -/
lemma cocartesianIsoTransportHomPath_native_vertex :
    (cocartesianIsoTransportHomPath A).app (Opposite.op ⦋0⦌)
      (coherentNerveVertex (show CocartesianIsoTransportCategory A from
        cocartesianBaseChangeIsoTransportObject l k p)) =
    (cocartesianBaseChangeAssociativityHomPath l k).app (Opposite.op ⦋0⦌)
      (coherentNerveVertex p) := by
  apply Subtype.ext
  change ((cocartesianIsoTransportHomPath A) ≫ equivalencePathι _).app _
    (coherentNerveVertex (show CocartesianIsoTransportCategory A from
      cocartesianBaseChangeIsoTransportObject l k p)) =
    ((cocartesianBaseChangeAssociativityHomPath l k) ≫ equivalencePathι _).app _
      (coherentNerveVertex p)
  rw [cocartesianIsoTransportHomPath_ι, cocartesianBaseChangeAssociativityHomPath_ι]
  apply intervalFunctorVertexEdge_injective
  rw [intervalFamily_vertex_edge, intervalFamily_vertex_edge]
  exact (cocartesianIsoTransportFamily_native_edge l k p).trans
    (cocartesianBaseChangeAssociativityEdge_at_simplex l k p)

end SerrePositivity.InfinityCategories
