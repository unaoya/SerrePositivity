module
public import SerrePositivity.KST.SConstruction.NecklaceSimplexIntervalTerminal
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.NecklaceBooleanMap

/-! # 元の全頂点を保つ一 bead への refinement 射
概要：元の necklace を同じ全頂点の一 bead に含め、元の全単体と Bool 座標作用を回収。
方針：元の標準単体への包含と元の一 bead 同型を合成する。
規約：joints を消しても元の全頂点は変えない。使われ方：分割合成の共有 joint の一面。
-/
@[expose] public section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory _root_.Simplicial SSet

/-- 元の necklace を、全頂点を共有する元の一 bead に含める実端点保存射。 -/
def necklaceBeadRefinement (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}) : T ⟶ necklaceBead T.down.vertexMax where
  map := T.down.inclusion ≫ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.singleSimplexIso _).inv
  map_first := simplexBeadIso_inv_first _
  map_last := simplexBeadIso_inv_last _

/-- 元の refinement 射の全頂点作用は、元の同じ局所番号そのもの。 -/
lemma necklaceBeadRefinement_vertex (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}) (v : T.down.Vertex) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap (necklaceBeadRefinement T) v = v := rfl

/-- 元の refinement 射は、元の標準単体への全単体的包含を厳密に回収する。 -/
lemma necklaceBeadRefinement_triangle (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}) :
    (necklaceBeadRefinement T).map ≫ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.singleSimplexIso _).hom =
      T.down.inclusion := by
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => T.down.inclusion ≫ f) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.singleSimplexIso _).inv_hom_id).trans
      (Category.comp_id _))

/-- 元の refinement の Bool 作用は、元の joints を一に固定する同じ全頂点指示関数。 -/
lemma necklaceBeadRefinement_boolean (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}) (x : T.down.NonjointVertex → Bool)
    (v : (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single T.down.vertexMax).NonjointVertex) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceBooleanMap (necklaceBeadRefinement T) x v = T.down.cubeFullBits x v.val := by
  apply Bool.eq_iff_iff.mpr
  rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceBooleanMap_true_iff]
  constructor
  · rintro ⟨w, hw, he⟩
    exact he ▸ hw
  · intro hv
    exact ⟨v.val, hv, rfl⟩

end SerrePositivity.KST.SConstruction
