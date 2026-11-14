module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.StableStructure.UnitSixTriangleDiagram
/-! # 同じ六二単体からの係数六角形

概要：同じ六二単体の合成構造を用い、二つの単位閉路の零性から実係数六角形を得る。
方針：共有辺を厳密に照合して六片の合成関係の消去補題へ渡す。
規約：Kan 性から辺の可逆性を得るが、実二単体や辺を選び直さない。
使われ方：上流の単位則と相対内角比較を接続した後の指定境界充填。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory SSet
open scoped _root_.Simplicial
namespace DGGluingUnitSixTriangleDiagram
variable {Z : SSet.{u}} [KanComplex Z] {a b c d e : Z _⦋0⦌}
  (P : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingUnitSixTriangleDiagram Z a b c d e)

def edgeIso (i : Fin 6) (j : Fin 3) :
    Truncated.HomotopyCategory.mk (V := (truncation 2).obj Z)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitSixTriangleVertexPattern a b c d e i (![1,0,0] j)) ≅
    Truncated.HomotopyCategory.mk (V := (truncation 2).obj Z)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitSixTriangleVertexPattern a b c d e i (![2,2,1] j)) := by
  have : IsIso (Truncated.HomotopyCategory.homMk (P.edge i j)) :=
    IsGroupoid.all_isIso (C := hoFunctor.obj Z) _
  exact asIso (Truncated.HomotopyCategory.homMk (P.edge i j))

lemma hexagon_of_unit_classes
    (hr : Truncated.HomotopyCategory.homMk (P.edge 0 0) = 𝟙 _)
    (hl : Truncated.HomotopyCategory.homMk (P.edge 2 2) = 𝟙 _) :
    Truncated.HomotopyCategory.homMk (P.edge 0 2) ≫ (P.edgeIso 4 1).inv ≫
      Truncated.HomotopyCategory.homMk (P.edge 2 0) =
        Truncated.HomotopyCategory.homMk (P.edge 5 1) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitSixTriangle_cancel (P.edgeIso 4 1) (P.edgeIso 4 2)
    (Truncated.HomotopyCategory.homMk (P.edge 0 2))
    (Truncated.HomotopyCategory.homMk (P.edge 2 0))
    (Truncated.HomotopyCategory.homMk (P.edge 5 2))
    (Truncated.HomotopyCategory.homMk (P.edge 4 0))
    (Truncated.HomotopyCategory.homMk (P.edge 5 0))
    (Truncated.HomotopyCategory.homMk (P.edge 0 0))
    (Truncated.HomotopyCategory.homMk (P.edge 2 2))
    (Truncated.HomotopyCategory.homMk (P.edge 0 1))
    (Truncated.HomotopyCategory.homMk (P.edge 2 1))
    (Truncated.HomotopyCategory.homMk (P.edge 5 1))
  · exact Truncated.HomotopyCategory.homMk_comp_homMk (P.comp 0)
  · simpa only [P.first_bridge_edge, P.coefficient_first_edge,
      ← P.first_diagonal_edge] using
      Truncated.HomotopyCategory.homMk_comp_homMk (P.comp 1)
  · exact Truncated.HomotopyCategory.homMk_comp_homMk (P.comp 2)
  · simpa only [edgeIso, asIso_hom, P.coefficient_last_edge, P.last_bridge_edge,
      ← P.last_diagonal_edge] using
      Truncated.HomotopyCategory.homMk_comp_homMk (P.comp 3)
  · exact Truncated.HomotopyCategory.homMk_comp_homMk (P.comp 4)
  · exact Truncated.HomotopyCategory.homMk_comp_homMk (P.comp 5)
  · exact hr
  · exact hl
lemma hexagon_of_unit_classes_transport
    (df : Truncated.Edge (X := (truncation 2).obj Z) a b)
    (dl : Truncated.Edge (X := (truncation 2).obj Z) d e)
    (bridge : Truncated.Edge (X := (truncation 2).obj Z) a e)
    (k : Truncated.HomotopyCategory.mk (V := (truncation 2).obj Z) d ≅
      Truncated.HomotopyCategory.mk (V := (truncation 2).obj Z) b)
    (hdf : P.edge 0 2 = df) (hdl : P.edge 2 0 = dl) (hb : P.edge 5 1 = bridge)
    (hk : P.edgeIso 4 1 = k)
    (hr : Truncated.HomotopyCategory.homMk (P.edge 0 0) = 𝟙 _)
    (hl : Truncated.HomotopyCategory.homMk (P.edge 2 2) = 𝟙 _) :
    Truncated.HomotopyCategory.homMk df ≫ k.inv ≫ Truncated.HomotopyCategory.homMk dl =
      Truncated.HomotopyCategory.homMk bridge := by
  simpa only [hdf, hdl, hb, hk] using P.hexagon_of_unit_classes hr hl
end DGGluingUnitSixTriangleDiagram
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
