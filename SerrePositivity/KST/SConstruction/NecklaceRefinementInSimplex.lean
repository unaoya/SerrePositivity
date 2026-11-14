module
public import SerrePositivity.KST.SConstruction.NecklaceBeadRefinement
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.NecklaceInIsoTerminal
public import SerrePositivity.KST.SConstruction.NecklaceCubicalMapping

/-! # 元の refinement の標準単体内の実表示関係
概要：元の necklace の標準単体への包含と一 bead への refinement を同じ Hom 図式で読む。
方針：元の全頂点と両端を保つ実射の可換三角形を、元の余極限へ送る。
規約：元の全単体的 augmentation を保持。使われ方：標準一面と元の合成生成射の比較。
-/
@[expose] public section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet

/-- 元の necklace の包含を、同じ標準単体の元の両端の間の necklace として読む。 -/
def necklaceInStandardSimplex (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn (Δ[T.down.vertexMax] : SSet.{u}) (simplexBeadFirstVertex T.down.vertexMax)
      (simplexBeadLastVertex T.down.vertexMax) where
  necklace := T
  map := T.down.inclusion
  map_first := rfl
  map_last := rfl

/-- 元の一 bead への refinement は、同じ標準単体内の元の可換三角形。 -/
def necklaceInBeadRefinement (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}) :
    necklaceInStandardSimplex T ⟶
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInOfIso (necklaceBead T.down.vertexMax) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.singleSimplexIso _) where
  necklaceHom := necklaceBeadRefinement T
  w := necklaceBeadRefinement_triangle T

/-- 元の実 refinement の可換三角形は、元の同じ cubical 生成射の表示関係を回収する。 -/
lemma necklaceInBeadRefinement_cell (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}) :
    necklaceCubicalSet.map (necklaceBeadRefinement T) ≫
        necklaceCubicalCell
          (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInOfIso (necklaceBead T.down.vertexMax) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.singleSimplexIso _)) =
      necklaceCubicalCell (necklaceInStandardSimplex T) :=
  necklaceCubicalCell_relation (necklaceInBeadRefinement T)

end SerrePositivity.KST.SConstruction
