module
public import SerrePositivity.KST.SConstruction.SimplexIntervalCompositionCoordinates

/-! # 元の区間合成の共有端点の一座標
概要：厳密な中間頂点は、全区間 cube の非 joint 座標で、元の合成で常に一になる。
方針：元の連結の共有頂点は joint であり、元の合成射がその番号を保つことを使う。
規約：同じ部分集合像による Bool 作用。使われ方：HA 方程式の分割項と一の面。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet

/-- 元の厳密な中間頂点の、全区間 bead 内の非 joint 座標。 -/
def simplexIntervalSeam {n : ℕ} (a b c : Fin (n + 1)) (hab : a < b) (hbc : b < c) :
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (c.val - a.val)).NonjointVertex :=
  ⟨⟨b.val - a.val, by
    change b.val - a.val < c.val - a.val + 1
    have hab' : a.val < b.val := hab
    have hbc' : b.val < c.val := hbc
    omega⟩, by
      change b.val - a.val ∉ ({0, c.val - a.val} : Finset ℕ)
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      have hab' : a.val < b.val := hab
      have hbc' : b.val < c.val := hbc
      omega⟩

/-- 元の合成の共有頂点の座標は、元の全入力 Bool 座標に対して一。 -/
lemma simplexIntervalComposeBeadHom_seam {n : ℕ} (a b c : Fin (n + 1))
    (hab : a < b) (hbc : b < c)
    (x : (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedge (necklaceBead.{u} (b.val - a.val))
      (necklaceBead (c.val - b.val))).down.NonjointVertex → Bool) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceBooleanMap (simplexIntervalComposeBeadHom.{u} a b c hab.le hbc.le) x
      (simplexIntervalSeam a b c hab hbc) = true := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceBooleanMap_coordinate _ _ _).mpr
  apply Or.inl
  refine ⟨(_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (b.val - a.val)).wedgeLeftVertex
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (c.val - b.val)) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (b.val - a.val)).last, ?_, ?_⟩
  · exact (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (b.val - a.val)).wedge_joint_left
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (c.val - b.val)) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (b.val - a.val)).last_mem
  · apply Fin.ext
    exact simplexIntervalComposeBeadHom_vertex_left.{u} a b c hab.le hbc.le
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (b.val - a.val)).last

/-- 元の合成の全頂点作用は単射で、部分集合像の各非 joint 座標を一意に検出する。 -/
lemma simplexIntervalComposeBeadHom_vertex_injective {n : ℕ} (a b c : Fin (n + 1))
    (hab : a ≤ b) (hbc : b ≤ c) :
    Function.Injective (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap (simplexIntervalComposeBeadHom.{u} a b c hab hbc)) := by
  intro v w h
  apply Fin.ext
  exact (simplexIntervalComposeBeadHom_vertex.{u} a b c hab hbc v).symm.trans
    ((congrArg Fin.val h).trans (simplexIntervalComposeBeadHom_vertex.{u} a b c hab hbc w))

end SerrePositivity.KST.SConstruction
