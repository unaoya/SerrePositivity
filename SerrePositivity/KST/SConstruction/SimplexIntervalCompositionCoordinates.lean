module
public import SerrePositivity.KST.SConstruction.SimplexIntervalComposition
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.FaceDegeneracy.NecklaceSimplexMaps

/-! # 元の区間合成の全頂点作用
概要：元の二区間の連結から全区間への射は、共有頂点を含む元の頂点番号を保つ。
方針：連結 augmentation の左右への厳密な制限を、元の局所頂点番号で照合する。
規約：一点区間も含めて全頂点を保持。使われ方：合成の共有端点座標と HA 分割項。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet

/-- 元の標準単体内の連結の左頂点作用は、元の左 augmentation の頂点作用。 -/
lemma necklaceSimplexWedge_vertex_left {n : ℕ} {x y z : (Δ[n] : SSet.{u}) _⦋0⦌}
    (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn (Δ[n] : SSet.{u}) x y) (U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn (Δ[n] : SSet.{u}) y z)
    (v : T.necklace.down.Vertex) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexVertexMap (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge T U).necklace.down (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge T U).map
      (T.necklace.down.wedgeLeftVertex U.necklace.down v) =
        _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexVertexMap T.necklace.down T.map v :=
  congrArg (fun f => (f.app _ (T.necklace.down.vertexEquiv.symm v)) 0)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge_inl T U)

/-- 元の標準単体内の連結の右頂点作用は、元の右 augmentation の頂点作用。 -/
lemma necklaceSimplexWedge_vertex_right {n : ℕ} {x y z : (Δ[n] : SSet.{u}) _⦋0⦌}
    (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn (Δ[n] : SSet.{u}) x y) (U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn (Δ[n] : SSet.{u}) y z)
    (v : U.necklace.down.Vertex) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexVertexMap (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge T U).necklace.down (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge T U).map
      (T.necklace.down.wedgeRightVertex U.necklace.down v) =
        _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexVertexMap U.necklace.down U.map v :=
  congrArg (fun f => (f.app _ (U.necklace.down.vertexEquiv.symm v)) 0)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge_inr T U)

/-- 元の区間の連結から全区間への射は、元の左頂点の局所番号を保つ。 -/
lemma simplexIntervalComposeBeadHom_vertex_left {n : ℕ} (a b c : Fin (n + 1))
    (hab : a ≤ b) (hbc : b ≤ c) (v : (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (b.val - a.val)).Vertex) :
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap (simplexIntervalComposeBeadHom.{u} a b c hab hbc)
      ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (b.val - a.val)).wedgeLeftVertex
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (c.val - b.val)) v)).val = v.val := by
  have h := necklaceSimplexWedge_vertex_left (necklaceInSimplexInterval.{u} a b hab)
    (necklaceInSimplexInterval b c hbc) v
  change (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexVertexMap _ _ _).val - a.val = v.val
  exact (congrArg (fun w => w.val - a.val) h).trans (by
    change a.val + v.val - a.val = v.val
    omega)

/-- 元の区間の連結から全区間への射は、元の右頂点の共有端点からの番号を保つ。 -/
lemma simplexIntervalComposeBeadHom_vertex_right {n : ℕ} (a b c : Fin (n + 1))
    (hab : a ≤ b) (hbc : b ≤ c) (v : (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (c.val - b.val)).Vertex) :
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap (simplexIntervalComposeBeadHom.{u} a b c hab hbc)
      ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (b.val - a.val)).wedgeRightVertex
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (c.val - b.val)) v)).val = b.val - a.val + v.val := by
  have h := necklaceSimplexWedge_vertex_right (necklaceInSimplexInterval.{u} a b hab)
    (necklaceInSimplexInterval b c hbc) v
  change (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexVertexMap _ _ _).val - a.val = _
  exact (congrArg (fun w => w.val - a.val) h).trans (by
    change b.val + v.val - a.val = b.val - a.val + v.val
    have h : a.val ≤ b.val := hab
    omega)

/-- 元の二区間の連結から全区間への射は、元の全頂点の局所番号を厳密に保つ。 -/
lemma simplexIntervalComposeBeadHom_vertex {n : ℕ} (a b c : Fin (n + 1))
    (hab : a ≤ b) (hbc : b ≤ c)
    (v : (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedge (necklaceBead.{u} (b.val - a.val))
      (necklaceBead (c.val - b.val))).down.Vertex) :
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap (simplexIntervalComposeBeadHom.{u} a b c hab hbc) v).val = v.val := by
  rcases (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (b.val - a.val)).wedgeVertex_cases
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (c.val - b.val)) v with ⟨w, rfl⟩ | ⟨w, rfl⟩
  · exact simplexIntervalComposeBeadHom_vertex_left a b c hab hbc w
  · exact simplexIntervalComposeBeadHom_vertex_right a b c hab hbc w

end SerrePositivity.KST.SConstruction
