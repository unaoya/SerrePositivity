module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleDiamondComposition

/-! # 元の実三角形対を同じ全写像で写す
概要：元の二つの実三角形と共通対角辺を、同じ単体的写像で全体として写す。
方針：実辺と合成三角形の写像を使い、両全二単体の像を厳密に回収する。
規約：入力の全二単体の像を保持し、新しい充填は行わない。
使われ方：零段評価へ同じ BF 二三角形を渡す。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open scoped _root_.Simplicial
variable {E B : SSet.{u}} {x m n z : E _⦋0⦌}
  {a : E.Edge x m} {b : E.Edge m z} {c : E.Edge x n} {d : E.Edge n z}
  (D : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond a b c d) (p : E ⟶ B)

/-- 元の同じ全写像による、両実三角形と共通対角辺の全像。 -/
def CompositionDiamond.map : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond (a.map p) (b.map p) (c.map p) (d.map p) where
  diagonal := D.diagonal.map p
  first := D.first.map p
  second := D.second.map p

/-- 第一全三角形は、元の同じ全二単体の像そのもの。 -/
lemma CompositionDiamond.map_first_simplex :
    (D.map p).first.simplex = p.app (Opposite.op ⦋2⦌) D.first.simplex := rfl

/-- 第二全三角形も、元の同じ全二単体の像そのもの。 -/
lemma CompositionDiamond.map_second_simplex :
    (D.map p).second.simplex = p.app (Opposite.op ⦋2⦌) D.second.simplex := rfl

/-- 共通対角辺も、元の同じ全辺の像そのもの。 -/
lemma CompositionDiamond.map_diagonal : (D.map p).diagonal = D.diagonal.map p := rfl

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond.map (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CompositionDiamond.map := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond.map

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CompositionDiamond.map_diagonal := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond.map_diagonal

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CompositionDiamond.map_first_simplex := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond.map_first_simplex

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CompositionDiamond.map_second_simplex := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond.map_second_simplex
